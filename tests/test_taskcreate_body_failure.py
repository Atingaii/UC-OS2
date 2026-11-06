"""完整函数体受限空闲失败路径；语义由 Coq 检查，文本测试不替代证明。"""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskCreateBodyFailure.v'


class TaskCreateBodyFailureTests(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / SOURCE).read_text()
        self.public = self.text.split('Theorem V293_OSTaskCreateExt_empty_body_hoare :')[1]

    def test_original_complete_body_not_a_replacement_path(self):
        self.assertIn('(V293_CreateExt_body 92%Z nesting reserved running sched hook f)', self.public)
        self.assertIn('unfold V293_CreateExt_body,V293_TaskCreateExt_body.', self.public)
        self.assertIn('apply V293_OSTaskCreateExt_prefix_hoare.', self.public)
        self.assertIn('V293_OSTaskCreateExt_stack_empty_failure_hoare', self.public)

    def test_physical_guards_cpu_and_reservation(self):
        for term in ['V293_create_prefix_guards', 'PriorityRead', 'NestingRead', 'SlotRead',
                     '(sassign(evar 109%Z)(econst32 Int.zero))',
                     'V293_task_prio_reserved_expr reserved', 'V293_reserved_symbol_eval']:
            self.assertIn(term, self.text)

    def test_terminal_suffix_does_not_fall_through_occupied_error(self):
        part = self.text.split('Theorem V293_OSTaskCreateExt_prefix_hoare :')[1].split('Proof.')[0]
        self.assertIn('suffix Afalse tid ->', part)
        self.assertIn('eapply seq_rule with(p\':=Afalse).', self.text)
        self.assertIn('apply pfalse_rule.', self.text)

    def test_public_contract_has_no_hoare_or_execution_or_guard_oracle(self):
        part = self.public.split('Proof.')[0]
        self.assertEqual(part.count('InfRules '), 1)
        self.assertEqual(part.count('Spec hook=Some('), 1)
        self.assertEqual(part.count('Spec f=Some('), 1)
        for branch in ['empty', 'success']:
            for section in ['fpre', 'fpost']:
                self.assertIn(f'V293_tcb_{branch}_{section}', part)
        self.assertNotRegex(part, r'\b(?:evalval|evaladdr|load|sfexec|WFIFun)\b')

    def test_keeps_extra_memory_and_explicit_required_frame(self):
        self.assertIn('GoodFrm Rbefore -> GoodFrm R -> GoodFrm F -> p<13 ->', self.public)
        self.assertIn('V293_create_prefix_kept bnest bcpu nesting reserved breserved F', self.public)
        kept = self.text.split('Definition V293_create_prefix_kept')[1].split('Definition V293_create_body_frame')[0]
        for term in ['(bn,0%Z)', '(bc,0%Z)', 'Alvarenv 109%Z', 'nesting Tint8 bn', 'reserved Tint8 br', '** F']:
            self.assertIn(term, kept)

    def test_no_holes_probe_dependency_or_duplicate_project_entry(self):
        self.assertNotRegex(self.text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.probes.', self.text)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)


if __name__ == '__main__':
    unittest.main()
