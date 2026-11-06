"""调用现场结构回归；语义由 Coq 与 coqchk 检查，不替代执行证明。"""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskCreateTCBCall.v'


class TaskCreateTCBCallTests(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / SOURCE).read_text()

    def test_actual_caller_identifiers_and_stack_pointer_type(self):
        part = self.text.split('Definition V293_create_tcb_arguments')[1].split('Lemma ')[0]
        for fragment in ['LV 101%Z @ Tint8', 'LV 108%Z @ (Tptr Tint32)',
                         'LV 205%Z @ (Tptr Tint32)', 'LV 206%Z @ Tint16',
                         'LV 207%Z @ Tint32', 'LV 208%Z @ (Tptr Tvoid)',
                         'LV 204%Z @ Tint16']:
            self.assertIn(fragment, part)
        self.assertNotIn('Tptr V293_tcb_type', part)

    def test_reads_all_seven_values_from_owned_local_cells(self):
        part = self.text.split('Theorem V293_create_tcb_arguments_read')[1].split('Qed.')[0]
        self.assertEqual(part.count('eapply lvar_rv'), 7)
        self.assertIn('(rev V293_TCBInit_argument_types)', part)
        self.assertIn('cbn [sat getsmem evalexprlist', part)
        self.assertIn('V293_tcb_init_values_valid', part)

    def test_actual_scannable_call_with_return_receiver(self):
        part = self.text.split('Theorem V293_TaskCreateExt_TCB_snapshot_call :')[1]
        self.assertIn('eapply calle_rule_lvar', part)
        self.assertNotIn('apply call_rule', part)
        self.assertIn('V293_TaskCreateExt_TCB_call 209%Z f 101%Z 108%Z 205%Z 206%Z 207%Z 208%Z 204%Z', part)
        self.assertIn('LV 209%Z @ Tint8 |-> result', part)
        self.assertIn('V293_create_tcb_arguments p top bottom identity size ext options F', part)

    def test_public_contract_has_no_execution_or_argument_oracle(self):
        part = self.text.split('Theorem V293_TaskCreateExt_TCB_snapshot_call :')[1].split('Proof.')[0]
        self.assertEqual(part.count('InfRules '), 1)
        self.assertNotRegex(part, r'\b(?:evalval|evaladdr|Rvl|load|sfexec|WFIFun)\b')
        self.assertIn('Spec f=Some(fp,fq,(Tint8,rev V293_TCBInit_argument_types))', part)
        for branch in ['empty', 'success']:
            self.assertIn(f'V293_tcb_{branch}_fpre', part)
            self.assertIn(f'V293_tcb_{branch}_fpost', part)

    def test_correlation_retpost_and_linv_not_omitted(self):
        part = self.text.split('Theorem V293_TaskCreateExt_TCB_snapshot_call :')[1]
        for fragment in ['saved=Vnull /\\ result=Vint32(Int.repr 66)',
                         'saved=Vptr(bt,Int.repr base) /\\ result=Vint32 Int.zero',
                         'assert(Ret:retpost fq)', 'V293_tcb_snapshot_post_code',
                         'apply V293_create_snapshot_pre_linv',
                         'eapply V293_create_snapshot_post_linv']:
            self.assertIn(fragment, part)

    def test_no_holes_or_probe_dependency(self):
        self.assertNotRegex(self.text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.probes.', self.text)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)


if __name__ == '__main__':
    unittest.main()
