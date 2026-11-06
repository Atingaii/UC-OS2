"""失败调用连接的结构回归；实际语义另由 Coq/coqchk 检查。"""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskCreateFailureHoare.v'


class TaskCreateFailureHoareTests(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / SOURCE).read_text()

    def test_real_slot_is_owned_not_inferred_from_error(self):
        part = self.text.split('Definition V293_create_failure_resources')[1].split('Definition ')[0]
        self.assertIn('LV 101%Z @ Tint8', part)
        self.assertIn('LV 209%Z @ Tint8', part)
        self.assertIn('Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true slot', part)

    def test_store_uses_existing_assignment_rule_and_derived_address(self):
        part = self.text.split('Theorem V293_create_failure_store_hoare')[1].split('Qed.')[0]
        for fragment in ['eapply assign_rule', 'V293_create_failure_address', 'V293_star_CurLINV_l']:
            self.assertIn(fragment, part)

    def test_critical_stack_and_real_false_branch(self):
        self.assertIn('apply encrit2_rule', self.text)
        self.assertIn('apply excrit2_rule', self.text)
        part = self.text.split('Theorem V293_OSTaskCreateExt_failure_suffix_hoare')[1].split('Qed.')[0]
        for fragment in ['V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z', 'V293_create_failure_guard',
                         'apply V293_create_failure_rollback_hoare', 'apply rete_rule']:
            self.assertIn(fragment, part)

    def test_same_full_snapshot_spec_without_execution_oracle(self):
        part = self.text.split('Theorem V293_OSTaskCreateExt_empty_call_suffix_hoare :')[1].split('Proof.')[0]
        self.assertEqual(part.count('InfRules '), 1)
        self.assertEqual(part.count('Spec f=Some('), 1)
        for branch in ['empty', 'success']:
            self.assertIn(f'V293_tcb_{branch}_fpre', part)
            self.assertIn(f'V293_tcb_{branch}_fpost', part)
        self.assertNotRegex(part, r'\b(?:evalval|evaladdr|load|sfexec|WFIFun)\b')

    def test_all_remaining_resources_are_retained(self):
        part = self.text.split('Definition V293_create_failure_kept')[1].split('Lemma ')[0]
        for identifier in [108, 205, 206, 207, 208, 204]:
            self.assertIn(f'LV {identifier}%Z', part)
        self.assertIn('false Vnull ** (R ** F)', part)
        self.assertIn('[|result=Some(Vint32(Int.repr 66))|]', self.text)

    def test_no_holes_or_probe_dependency(self):
        self.assertNotRegex(self.text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.probes.', self.text)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)


if __name__ == '__main__':
    unittest.main()
