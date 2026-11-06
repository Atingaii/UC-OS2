"""五分支共规格接口的结构回归；证明有效性由 Coq 内核另行检查。"""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskCreateUnifiedInternal.v'

class TaskCreateUnifiedInternalTests(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / SOURCE).read_text()
        self.public = self.text.split('Theorem V293_OSTaskCreateExt_unified_internal_contract :')[1].split('Proof.')[0]

    def test_single_hook_and_tcb_lookup(self):
        self.assertEqual(self.public.count('Spec hook=Some('), 1)
        self.assertEqual(self.public.count('Spec f=Some('), 1)
        self.assertIn('hook<>f', self.public)

    def test_five_outcomes_spatial_union_not_caller_tag(self):
        part = self.text.split('Definition V293_create_unified_fpre :')[1].split('Definition V293_create_unified_fpost')[0]
        self.assertEqual(part.count('V293_tcb_union_fpre'), 4)
        for name in ['bad_priority', 'from_isr', 'occupied_priority']:
            self.assertIn('V293_create_union_reject_pre V293_create_' + name, part)
        for name in ['empty', 'ready']:
            self.assertIn('V293_create_union_' + name + '_pre', part)
        self.assertNotIn('logic_ie', part)

    def test_exact_logical_instance_transport_all_call_rules(self):
        part = self.text.split('Lemma V293_InfRules_spec_instances :')[1].split('Qed.')[0]
        self.assertIn('induction Proof', part)
        for rule in ['call_rule', 'calle_rule', 'calle_rule_lvar']:
            self.assertIn('eapply ' + rule + ' with', part)
        self.assertIn('getasrt(np vl (instantiate lg) tid)=getasrt(fp vl lg tid)', self.text)
        self.assertIn('logic_ie branch::lg', self.text)

    def test_allocation_guards_and_reuse_frozen_contracts(self):
        self.assertIn('p<13 /\\', self.text)
        self.assertIn('V293_stack_argument_valid argv inputtop options', self.text)
        self.assertIn('V293_tcb_init_values_valid top bottom identity size ext options', self.text)
        for branch in ['rejection', 'empty', 'success']:
            self.assertIn('eapply V293_OSTaskCreateExt_' + branch + '_internal_contract', self.text)
        self.assertIn('(Contract Saved)', self.text)

    def test_real_builders_body_no_execution_oracle(self):
        for term in ['BuildPreI P creator vl lg', 'BuildRetI P creator vl lg',
                     'V293_CreateExt_function 92%Z 99%Z 97%Z 98%Z',
                     'V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z']:
            self.assertIn(term, self.public)
        self.assertEqual(self.public.count('InfRules '), 1)
        for term in ['evalval', 'evaladdr', 'sfexec', 'WFIFun', 'retpost']:
            self.assertNotIn(term, self.public)

    def test_no_holes_probe_imports_or_duplicate_project(self):
        self.assertNotRegex(self.text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.probes.', self.text)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

if __name__ == '__main__':
    unittest.main()
