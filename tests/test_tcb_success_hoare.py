"""Structural regression checks; Coq compilation/coqchk supply proof checking."""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
PROOF = ROOT / 'certiucos/v293/proofs/V293TCBSuccessHoare.v'
PROBE = ROOT / 'audit/probes/V293TCBSuccessHoareProbe.v'

class TCBSuccessHoareTests(unittest.TestCase):
    def test_no_new_assumptions_or_probe_dependencies(self):
        for path in [PROOF, PROBE]:
            source = path.read_text()
            self.assertNotRegex(source, r'\b(Axiom|Parameter|Conjecture|Admitted|admit)\b')
            self.assertNotRegex(source, r'Require(?: Import)? CertiOS\.audit\.probes\.')

    def test_full_actual_body_with_only_real_suffix_open(self):
        text = PROOF.read_text()
        for name in ['V293_OS_TCBInit_nonempty_body_with_suffix_hoare',
                     'V293_OS_TCBInit_nonempty_body_with_suffix_semantics']:
            statement = text.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]
            self.assertIn('(V293_TCBInit_function_body hi hc)', statement)
            self.assertIn('(V293_TCBInit_success_suffix hi hc) Afalse tid ->', statement)
            self.assertNotRegex(statement, r'\b(evalval|evaladdr|sfexec|exec|V293_stmt_exec)\b')
        self.assertIn('apply RuleSound', text)

    def test_three_real_assignments_and_field_chain(self):
        text = PROOF.read_text()
        self.assertEqual(re.findall(r'^ V293_success_store (\d+)', text, re.M), ['0', '19', '27'])
        self.assertIn('V293_tcb_init_read Owned 27 HeadRead', text)
        self.assertIn('V293_tcb_init_read Owned 28 NextRead', text)
        self.assertIn('apply V293_OS_TCBInit_fields_hoare', text)
        segment = text.split('Theorem V293_OS_TCBInit_pop_fields_hoare :', 1)[1].split('Qed.', 1)[0]
        self.assertNotIn('suffix', segment)
        for rule in ['V293_tcb_success_pop_hoare', 'V293_tcb_success_exit', 'V293_tcb_success_fields_hoare']:
            self.assertIn(rule, segment)

    def test_real_nonempty_guard_and_critical_stack(self):
        text = PROOF.read_text()
        self.assertIn('eapply ift_rule with (tp:=Tint32)', text)
        self.assertIn('Some(Vint32 Int.one)', text)
        self.assertIn('rewrite One in V', text)
        self.assertIn('apply pfalse_rule', text)
        self.assertIn('apply encrit2_rule', text)
        self.assertIn('apply excrit2_rule', text)
        self.assertIn('false::cs', text)

    def test_joint_literal_entries_and_non_circular_readback(self):
        text = PROBE.read_text()
        for name in ['SuccessLiteralEntry', 'SuccessInitialEntry', 'SuccessPopEntry',
                     'SuccessHeadRead', 'SuccessWrongHeadRead', 'SuccessNextPreserved', 'SuccessCoreSize']:
            self.assertIn('Theorem ' + name, text)
        self.assertIn('Definition SuccessChecked', text)
        self.assertIn('Definition SuccessBodyChecked', text)
        self.assertIn('SuccessPre Vundef Vundef cs', text)
        self.assertIn('=29', text)
        self.assertIn('=81', text)
        self.assertIn('Definition SuccessSentinel', text)
        self.assertIn('SuccessRGood', text)
        self.assertIn('SuccessRCurLINV', text)

    def test_exactly_once_in_active_build(self):
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(str(PROOF.relative_to(ROOT))), 1)

if __name__ == '__main__':
    unittest.main()
