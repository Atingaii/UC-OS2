"""栈调用到失败链的结构回归；语义正确性由 Coq 和 coqchk 检查。"""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskCreateStackCall.v'


class TaskCreateStackCallTests(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / SOURCE).read_text()

    def test_four_arguments_read_from_real_caller_locals(self):
        part = self.text.split('Theorem V293_create_stack_arguments_read :')[1].split('Qed.')[0]
        self.assertIn('Rvl [evar 201%Z;evar 202%Z;evar 203%Z;evar 204%Z]', part)
        self.assertEqual(part.count('eapply lvar_rv'), 4)
        self.assertIn('rev V293_stack_argument_types', part)

    def test_actual_receiver_and_existing_call_rule(self):
        part = self.text.split('Theorem V293_OSTaskCreateExt_stack_call_hoare :')[1].split('Qed.')[0]
        self.assertIn('V293_TaskCreateExt_stack_call 108%Z hook 201%Z 202%Z 203%Z 204%Z', part)
        self.assertIn('eapply calle_rule_lvar', part)
        self.assertIn('LV 108%Z @ (Tptr Tint32) |-> stack', part)

    def test_external_hook_tracks_arguments_and_can_change_resource(self):
        self.assertIn('[|vl=args|]', self.text)
        self.assertIn('[|vl=args /\\ result=Some stack|]', self.text)
        part = self.text.split('Theorem V293_OSTaskCreateExt_stack_call_hoare :')[1].split('Proof.')[0]
        self.assertIn('gb:GoodFunAsrt Rbefore', part)
        self.assertIn('ga:GoodFunAsrt Rafter', part)
        self.assertIn('Rbefore ==> CurLINV li tid', part)
        self.assertIn('Rafter ==> CurLINV li tid', part)

    def test_same_full_tcb_snapshot_and_no_execution_oracle(self):
        part = self.text.split('Theorem V293_OSTaskCreateExt_stack_empty_failure_hoare :')[1].split('Proof.')[0]
        self.assertEqual(part.count('InfRules '), 1)
        self.assertEqual(part.count('Spec hook=Some('), 1)
        self.assertEqual(part.count('Spec f=Some('), 1)
        self.assertIn('table reserved slot bg bt', part)
        for branch in ['empty', 'success']:
            for section in ['fpre', 'fpost']:
                self.assertIn(f'V293_tcb_{branch}_{section}', part)
        self.assertNotRegex(part, r'\b(?:evalval|evaladdr|load|sfexec|WFIFun)\b')

    def test_connection_retains_extra_locals_and_original_suffix(self):
        part = self.text.split('Definition V293_create_stack_kept')[1].split('Lemma ')[0]
        for identifier in [201, 202, 203]:
            self.assertIn(f'LV {identifier}%Z', part)
        part = self.text.split('Theorem V293_OSTaskCreateExt_stack_empty_failure_hoare :')[1]
        self.assertIn('V293_TaskCreateExt_calls 108%Z hook', part)
        self.assertIn('V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z running sched', part)
        self.assertIn('eapply V293_OSTaskCreateExt_empty_call_suffix_hoare', part)

    def test_no_holes_or_probe_dependency(self):
        self.assertNotRegex(self.text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.probes.', self.text)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)


if __name__ == '__main__':
    unittest.main()
