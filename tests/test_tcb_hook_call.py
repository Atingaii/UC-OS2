"""Hook 调用连接的结构防回退；形式证明信用来自 Coq 内核。"""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
PROOF = ROOT / 'certiucos/v293/proofs/V293TCBHookCall.v'
PROBE = ROOT / 'audit/probes/V293TCBHookCallProbe.v'

class TCBHookCallTests(unittest.TestCase):
    def test_no_unproved_terms_or_old_probe_imports(self):
        for path in [PROOF, PROBE]:
            text = path.read_text()
            self.assertNotRegex(text, r'\b(Axiom|Parameter|Conjecture|Admitted|admit|Abort)\b')
            self.assertNotRegex(text, r'Require(?: Import)? CertiOS\.audit\.probes\.')

    def test_actual_call_rule_and_actual_argument_load(self):
        text = PROOF.read_text()
        self.assertIn('eapply call_rule with', text)
        arg = text.split('Theorem V293_tcb_hook_argument :', 1)[1].split('Theorem V293_tcb_hook_call', 1)[0]
        self.assertIn('load (Tptr V293_tcb_type) M (bc,0%Z)', arg)
        self.assertIn('eapply V293_rdy_raw_load', arg)
        self.assertIn('get le 108%Z', arg)
        statement = arg.split('Proof.', 1)[0]
        self.assertEqual(statement.count('==>'), 1)
        self.assertNotIn('InfRules', statement)

    def test_complete_body_two_lookups_not_two_hoare_premises(self):
        text = PROOF.read_text()
        statement = text.split('Theorem V293_OS_TCBInit_hook_calls_body_hoare :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(statement.count('InfRules '), 1)
        self.assertEqual(statement.count('Spec hi=Some('), 1)
        self.assertEqual(statement.count('Spec hc=Some('), 1)
        self.assertIn('Hfun:GoodFunAsrt R', statement)
        self.assertIn('(V293_TCBInit_function_body hi hc)', statement)
        self.assertNotRegex(statement, r'\b(evalval|evaladdr|V293_stmt_exec|sfexec)\b')
        self.assertIn('apply RuleSound', text)

    def test_caller_locals_not_transferred_to_hook_contract(self):
        text = PROOF.read_text()
        owned = text.split('Definition V293_hook_owned_cells', 1)[1].split('Definition V293_hook_bindings', 1)[0]
        self.assertNotIn('V293_tcb_prefix_inputs', owned)
        self.assertNotIn('bu', owned)
        for token in ['V293_tcb_init_final_fields', 'V293_tcb_prefix_links', 'V293_link_extra']:
            self.assertIn(token, owned)
        self.assertIn('V293_hook_frame locals bindings := V293_rdy_raw_cells locals bindings', text)
        for token in ['Lemma V293_hook_layout', 'Lemma V293_hook_cells_factor', 'Theorem V293_tcb_hook_view']:
            self.assertIn(token, text)

    def test_contract_checks_pointer_task_and_void_result(self):
        text = PROOF.read_text()
        pre = text.split('Definition V293_hook_fpre', 1)[1].split('Lemma V293_hook_cells_factor', 1)[0]
        self.assertIn('vl=[pointer] /\ tid=owner', pre)
        self.assertIn('result=None', pre)
        self.assertNotIn('Alvarenv', pre)
        self.assertIn('(tl:=[Tptr V293_tcb_type])', text)

    def test_literal_call_entries_both_sites_and_ready_list_branches(self):
        text = PROBE.read_text()
        for name in ['HookAtCallRawLiteral', 'HookAtCallLiteralEntry', 'HookAtCallView', 'HookAtCallEntry',
                     'HookArgumentRead', 'HookArgumentNotNext', 'HookFootprint']:
            self.assertIn('Theorem ' + name, text)
        self.assertIn('destruct written,present', text)
        self.assertIn('if written then HookHead else Vundef', text)
        self.assertIn('then 27 else 26', text)
        self.assertIn('))=9.', text)
        self.assertIn('Int.repr 384', text)
        self.assertIn('Int.repr 256', text)

    def test_finite_lookup_witness_not_hook_implementation(self):
        text = PROBE.read_text()
        for name in ['HookInitLookup', 'HookCreateLookup', 'HookBodyUnderDeclaredContracts',
                     'HookPreRejectsWrongPointer', 'HookPostRejectsValueReturn', 'HookCallSiteChecked']:
            self.assertIn('Theorem ' + name, text)
        self.assertIn('Definition HookDeclaredSpec', text)
        self.assertNotIn('Definition HookImplementation', text)

    def test_active_build_once(self):
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(str(PROOF.relative_to(ROOT))), 1)

if __name__ == '__main__':
    unittest.main()
