"""启用中断的真实调用与回滚结构回归；不代替 Coq／整核证明。"""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskCreateEnabledFailure.v'


class TaskCreateEnabledFailureTests(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / SOURCE).read_text()
        self.public = self.text.split('Theorem V293_OSTaskCreateExt_enabled_empty_call_suffix :')[1].split('Proof.')[0]

    def test_pool_reborrows_typed_existential_not_reserved_snapshot(self):
        pool = self.text.split('Definition V293_create_rollback_pool ')[1].split('Definition ')[0]
        self.assertIn('EX slot:val', pool)
        self.assertIn('rule_type_val_match(Tptr V293_tcb_type)slot=true', pool)
        self.assertNotIn('RESERVED', pool)
        enter = self.text.split('Lemma V293_create_enabled_failure_enter :')[1].split('Proof.')[0]
        self.assertIn('EX slot:val', enter)
        self.assertIn('V293_create_failure_state table p slot', enter)

    def test_enabled_caller_owns_neither_head_nor_slot_bytes(self):
        resources = self.text.split('Definition V293_create_enabled_failure_resources ')[1].split('Definition ')[0]
        kept = self.text.split('Definition V293_create_enabled_failure_kept ')[1].split('Lemma ')[0]
        self.assertNotIn('Amapsto', resources)
        self.assertNotIn('Amapsto', kept)
        state = self.text.split('Definition V293_create_enabled_failure_state ')[1].split('Definition ')[0]
        self.assertIn('OS[ir,true,si,ci]', state)
        post = self.text.split('Definition V293_create_enabled_failure_return ')[1].split('Definition ')[0]
        self.assertNotIn('Vnull', post)

    def test_real_critical_borrow_store_close(self):
        for name in ['apply encrit1_rule', 'apply excrit1_rule', 'true::ci',
                     'apply V293_create_failure_store_hoare', 'V293_create_enabled_failure_enter',
                     'V293_create_enabled_failure_exit']:
            self.assertIn(name, self.text)
        self.assertEqual(self.public.count('V293_tcb_empty_pool bf(V293_create_rollback_pool table p K)'), 2)

    def test_actual_seven_arguments_and_unchanged_complete_suffix(self):
        self.assertIn('V293_TaskCreateExt_TCB_call 209%Z f 101%Z 108%Z 205%Z 206%Z 207%Z 208%Z 204%Z', self.public)
        self.assertIn('V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z running sched', self.public)
        for name in ['calle_rule_lvar', 'V293_create_tcb_arguments_read',
                     'V293_create_tcb_argument_types', 'V293_create_error66_guard', 'apply rete_rule']:
            self.assertIn(name, self.text)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

    def test_no_holes_execution_oracle_or_audit_dependency(self):
        self.assertNotRegex(self.text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.', self.text)
        self.assertEqual(self.public.count('InfRules '), 1)
        self.assertNotRegex(self.public, r'\b(?:load|evalval|evaladdr|loststep|sfexec|WFIFun)\b')

    def test_same_spec_caller_full_callee_builders_independent_probe(self):
        probe = (ROOT / 'audit/probes/V293TaskCreateEnabledFailureProbe.v').read_text()
        self.assertNotIn('CertiOS.audit.probes.', probe)
        self.assertEqual(len(re.findall(r'^Definition \w+ : Inv :=', probe, re.M)), 1)
        for name in ['RBCallerLiteral', 'RBCallerHasNoSharedBytes', 'RBBorrowEquivalence',
                     'RBSameInvariantDifferentSlots', 'RBBuilders',
                     'RBCalleeCheckedSameSpec', 'RBCallerCheckedSameSpec']:
            self.assertRegex(probe, rf'(?:Lemma|Theorem) {name} :')
        self.assertEqual(probe.count('InfRules(RBSpec cs)sd V293_witness_li RBInv'), 2)
        self.assertIn('V293_OS_TCBInit_empty_enabled_contract', probe)


if __name__ == '__main__':
    unittest.main()
