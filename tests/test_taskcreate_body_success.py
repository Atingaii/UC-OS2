"""完整成功分支的结构回归，不替代内核检查或全局可达性证明。"""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskCreateBodySuccess.v'
PROBE = 'audit/probes/V293TaskCreateBodySuccessProbe.v'


class TaskCreateBodySuccessTests(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / SOURCE).read_text()
        self.public = self.text.split('Theorem V293_OSTaskCreateExt_success_body_hoare :')[1].split('Proof.')[0]

    def test_original_body_and_existing_vertical_interfaces(self):
        self.assertIn('(V293_CreateExt_body 92%Z nesting reserved running sched hook f)', self.public)
        self.assertIn('apply V293_OSTaskCreateExt_prefix_hoare', self.text)
        self.assertIn('eapply V293_OSTaskCreateExt_stack_success_hoare', self.text)

    def test_priority_slot_has_one_owner_then_exact_reserved_value(self):
        self.assertIn('p cpuold Vnull', self.public)
        self.assertIn('success_body_frame(tl cells)globals', self.public)
        self.assertIn('let cells:=V293_tcb_success_pre_owned table(Vptr(breserved,Int.zero))', self.public)
        self.assertIn('V293_create_success_body_to_calls', self.text)

    def test_full_snapshot_and_only_two_declared_lookup_premises(self):
        for branch in ['empty', 'success']:
            for part in ['fpre', 'fpost']:
                self.assertIn('V293_tcb_' + branch + '_' + part, self.public)
        self.assertEqual(self.public.count('Spec hook=Some('), 1)
        self.assertEqual(self.public.count('Spec f=Some('), 1)
        self.assertEqual(self.public.count('InfRules '), 1)
        self.assertNotRegex(self.public, r'\b(?:evalval|evaladdr|load|sfexec|WFIFun)\b')

    def test_retains_callee_arguments_prefix_bytes_and_caller_frame(self):
        for phrase in ['getasrt(fq(', 'V293_create_tcb_arguments p top bottom identity size ext options',
                       'V293_create_stack_kept target argv inputtop',
                       'V293_create_prefix_kept bnest bcpu nesting reserved breserved(V293_tcb_table_binding table ** F)',
                       'V293_create_success_body_frame(tl cells)globals oldpsp']:
            self.assertIn(phrase, self.public)
        self.assertIn('LV 108%Z @ (Tptr Tint32) |->oldpsp', self.text.split('Lemma V293_create_success_body_frame_good')[0])

    def test_literal_entry_and_same_spec_callee_are_explicit(self):
        probe = (ROOT / PROBE).read_text()
        for name in ['SBLiteralEntry', 'SBHoareChecked', 'SBSameSpecCallee', 'SBPrefixExecution', 'SBReservedSlotNotNull']:
            self.assertIn('Theorem ' + name + ' :', probe)
        self.assertIn('getasrt(SBFpre present cs SuccessArguments[logic_val saved]SuccessTid)', probe)
        self.assertIn('(slot:=SBReserved)', probe)
        self.assertIn('SBState(SBMemory present cpu)cs |= SBEntry present cpu cs', probe)

    def test_no_holes_or_probe_dependency_and_project_entry_once(self):
        self.assertNotRegex(self.text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.probes.', self.text)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)


if __name__ == '__main__':
    unittest.main()
