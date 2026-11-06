"""局部接口结构回归；不替代 Coq 资源／语义证明，也不授予整函数覆盖。"""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskCreateEnabledSlotPool.v'


class TaskCreateEnabledSlotPoolTests(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / SOURCE).read_text()
        self.public = self.text.split('Theorem V293_OSTaskCreateExt_enabled_stack_fragment :')[1].split('Proof.')[0]

    def test_nullable_pool_hides_both_physical_values(self):
        pool = self.text.split('Definition V293_create_nullable_pool ')[1].split('Definition ')[0]
        self.assertIn('EX n:nat, EX slot:option addrval', pool)
        self.assertIn('n<256', pool)
        self.assertIn('None=>Vnull | Some a=>Vptr a', self.text)
        self.assertIn('apply encrit1_rule', self.text)
        self.assertIn('apply excrit1_rule', self.text)

    def test_reservation_recloses_pool_and_preserves_ie_stack(self):
        self.assertIn('V293_create_nullable_close', self.text)
        self.assertIn('V293_create_slot_prefix_zero', self.text)
        self.assertIn('apply V293_create_prefix_reserve_hoare', self.text)
        self.assertIn('OS[ir,false,si,true::ci]', self.text)
        self.assertIn('V293_create_enabled_state bp bc p cpu F aop ir si ci', self.text)

    def test_actual_stack_assignment_and_resource_call(self):
        self.assertIn('V293_TaskCreateExt_stack_call 108%Z hook 201%Z 202%Z 203%Z 204%Z', self.public)
        self.assertIn('V293_OSTaskCreateExt_stack_resource_call_hoare', self.text)
        for name in ['Rbefore', 'Rafter', 'V293_create_stack_resource_fpre', 'V293_create_stack_resource_fpost']:
            self.assertIn(name, self.public)
        self.assertEqual(self.public.count('InfRules '), 1)

    def test_no_execution_oracle_or_holes(self):
        self.assertNotRegex(self.public, r'\b(?:evalval|evaladdr|load|loststep|sfexec|WFIFun)\b')
        self.assertNotRegex(self.text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.probes.', self.text)

    def test_explicit_fragment_scope_and_unchanged_original_ast(self):
        self.assertIn('NOT the whole prefix with a truncated', self.text)
        self.assertNotIn('V293_CreateExt_body ', self.public)
        original = (ROOT / 'certiucos/v293/code/V293OSTaskCreateExtPrefix.v').read_text()
        self.assertIn('V293_TaskCreateExt_occupied', original)
        self.assertIn('(sseq (sprim excrit) suffix)', original)

    def test_registered_once_and_same_probe_invariant(self):
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)
        probe = (ROOT / 'audit/probes/V293TaskCreateEnabledSlotPoolProbe.v').read_text()
        self.assertEqual(len(re.findall(r'^Definition \w+ : Inv :=', probe, re.M)), 1)
        self.assertIn('NPSameInvariantBothSlots', probe)
        self.assertIn('NPCallerHasNoSharedBytes', probe)
        for name in ['NPExactDomain', 'NPCallerSpatial', 'NPEnterChecked',
                     'NPReservationStackChecked', 'NPActualPrefixToCall']:
            self.assertIsNotNone(re.search(rf'^(?:Lemma|Theorem) {name} :', probe, re.MULTILINE))
        self.assertIn('kseq V293_TaskCreateExt_occupied kstop', probe)


if __name__ == '__main__':
    unittest.main()
