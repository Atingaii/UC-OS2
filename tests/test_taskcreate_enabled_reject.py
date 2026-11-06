"""开启中断的提前返回接口结构回归；语义和假设闭包由 Coq 单独检查。"""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskCreateEnabledReject.v'

class TaskCreateEnabledRejectTests(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / SOURCE).read_text()
        self.public = self.text.split('Theorem V293_OSTaskCreateExt_enabled_rejection_contract :')[1].split('Proof.')[0]

    def test_exact_real_builders_original_complete_body(self):
        for term in ['BuildPreI P creator vl lg', 'BuildRetI P creator vl lg',
                     'V293_CreateExt_function 92%Z 99%Z 97%Z 98%Z',
                     'V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z']:
            self.assertIn(term, self.public)
        self.assertIn('V293_create_internal_domain', self.text)
        self.assertIn('V293_create_internal_buildp', self.text)

    def test_no_execution_or_guard_oracle_in_interface(self):
        self.assertEqual(self.public.count('InfRules '), 1)
        for term in ['evalval', 'evaladdr', 'sfexec', 'loststep', 'WFIFun', 'Spec hook=']:
            self.assertNotIn(term, self.public)
        self.assertIn('k<>V293_create_bad_priority ->', self.public)
        self.assertIn('<==> Aisr isr ** V293_create_borrowed', self.public)

    def test_caller_does_not_own_invariant_bytes(self):
        part = self.text.split('Definition V293_create_enabled_external ')[1].split('Lemma ')[0]
        self.assertIn('OS[ir,true,si,ci] ** R', part)
        for term in ['V293_create_borrowed', 'raw_cells', 'rejection_extra_cells']:
            self.assertNotIn(term, part)

    def test_actual_critical_rules_and_saved_true(self):
        self.assertIn('apply encrit1_rule', self.text)
        self.assertIn('apply excrit1_rule', self.text)
        self.assertIn('ir si(true::ci)', self.text)
        self.assertIn('apply astar_l_atopis_elim', self.text)
        self.assertIn('V293_create_enabled_frame_views', self.text)

    def test_reuse_owned_guards_and_three_returns(self):
        for term in ['V293_create_enabled_priority', 'V293_create_rejection_nesting',
                     'V293_create_rejection_slot', 'V293_create_from_isr',
                     'V293_create_bad_priority', 'V293_create_occupied_priority']:
            self.assertIn(term, self.text)
        self.assertIn('load Tint8 M(bp,0%Z)=Some(V293_byteval p)', self.text)

    def test_no_holes_probe_dependency_or_duplicate_project(self):
        self.assertNotRegex(self.text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.probes.', self.text)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

if __name__ == '__main__':
    unittest.main()
