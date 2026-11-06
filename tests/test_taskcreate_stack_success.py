"""成功两调用的结构回归；不替代Coq内核检查或端口实现证明。"""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskCreateStackSuccess.v'
PROBE = 'audit/probes/V293TaskCreateStackSuccessProbe.v'


class TaskCreateStackSuccessTests(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / SOURCE).read_text()
        self.public = self.text.split('Theorem V293_OSTaskCreateExt_stack_success_hoare :')[1].split('Proof.')[0]

    def test_external_resource_is_not_restricted_to_empty_free_list(self):
        generic = self.text.split('Theorem V293_OSTaskCreateExt_stack_resource_call_hoare :')[1].split('Qed.')[0]
        self.assertIn('(before after:funasrt)', generic)
        self.assertNotIn('V293_tcb_empty_external', generic)
        self.assertIn('getasrt before ==> CurLINV', generic)
        self.assertIn('getasrt after ==> CurLINV', generic)
        self.assertIn('calle_rule_lvar', generic)

    def test_exact_actual_calls_and_original_suffix(self):
        self.assertIn('V293_TaskCreateExt_calls 108%Z hook 201%Z 202%Z 203%Z 204%Z 209%Z f', self.public)
        self.assertIn('V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z running sched', self.public)
        self.assertIn('eapply V293_OSTaskCreateExt_success_call_suffix_hoare', self.text)

    def test_same_full_tcb_snapshot_and_exact_hook_handoff(self):
        for branch in ['empty', 'success']:
            for part in ['fpre', 'fpost']:
                self.assertIn('V293_tcb_' + branch + '_' + part, self.public)
        self.assertIn('Spec hook=Some(', self.public)
        self.assertIn('Spec f=Some(fp,fq,', self.public)
        self.assertIn('(fp(V293_tcb_success_arguments', self.public)
        self.assertIn('logic_val(Vptr(bt,Int.repr base))', self.public)

    def test_retains_stack_arguments_tcb_arguments_and_caller_frame(self):
        self.assertIn('V293_create_stack_kept target argv inputtop F', self.public)
        self.assertIn('V293_create_tcb_arguments p top bottom identity size ext options', self.public)
        self.assertIn('V293_create_idle_running running brun ** F', self.public)
        self.assertIn('LV 108%Z @ (Tptr Tint32) |->oldpsp', self.public)

    def test_no_new_execution_oracle_or_holes(self):
        self.assertEqual(self.public.count('InfRules '), 1)
        self.assertNotRegex(self.public, r'\b(?:evalval|evaladdr|load|sfexec|WFIFun)\b')
        self.assertNotRegex(self.text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.probes.', self.text)

    def test_nonvacuous_same_spec_probe_and_project_inclusion(self):
        probe = (ROOT / PROBE).read_text()
        for name in ['SSSameSpecCallee', 'SSHoareChecked', 'SSLiteralEntry', 'SSEntrySatisfiable', 'SSActualStackArguments']:
            self.assertIn('Theorem ' + name + ' :', probe)
        self.assertIn('good_fun_asrt_absop', probe)
        self.assertIn('CallLocals Vundef Vnull Vundef', probe)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)


if __name__ == '__main__':
    unittest.main()
