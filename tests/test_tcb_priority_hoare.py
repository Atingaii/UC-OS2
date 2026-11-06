"""结构回归；证明信用来自 coqc/coqchk，不来自字符串检查。"""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
PROOF = ROOT / 'certiucos/v293/proofs/V293TCBPriorityHoare.v'
PROBE = ROOT / 'audit/probes/V293TCBPriorityHoareProbe.v'

class TCBPriorityHoareTests(unittest.TestCase):
    def test_no_new_assumptions_or_probe_dependencies(self):
        for path in [PROOF, PROBE]:
            self.assertNotRegex(path.read_text(), r'\b(Axiom|Parameter|Conjecture|Admitted|admit)\b')
            self.assertNotRegex(path.read_text(), r'Require(?: Import)? CertiOS\.audit\.probes\.')

    def test_actual_store_uses_real_load_and_array_address(self):
        text = PROOF.read_text()
        for token in ['V293_raw_assign_hoare', 'V293_rekey_array_address',
                      'V293_tcb_init_read Owned 20 PointerRead',
                      'V293_tcb_init_read Owned 21 PriorityRead',
                      '(earrayelem(evar 92%Z)(evar 101%Z)) (evar 108%Z)']:
            self.assertIn(token, text)
        statement = text.split('Theorem V293_OS_TCBInit_priority_store_hoare :', 1)[1].split('Proof.', 1)[0]
        self.assertNotRegex(statement, r'\b(evalval|evaladdr|sfexec|exec|V293_stmt_exec)\b')

    def test_unconditional_bracket_and_rule_sound(self):
        text = PROOF.read_text()
        bracket = text.split('Theorem V293_OS_TCBInit_priority_bracket_hoare :', 1)[1].split('Qed.', 1)[0]
        self.assertEqual(bracket.count('InfRules '), 1)
        for rule in ['V293_tcb_success_enter', 'V293_OS_TCBInit_priority_store_hoare', 'V293_tcb_success_exit']:
            self.assertIn(rule, bracket)
        self.assertIn('V293_OS_TCBInit_priority_bracket_semantics', text)
        self.assertIn('apply RuleSound', text)

    def test_exact_body_has_only_two_hook_and_publish_obligations(self):
        text = PROOF.read_text()
        statement = text.split('Theorem V293_OS_TCBInit_nonempty_body_split_hoare :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(statement.count('InfRules '), 4)
        for token in ['(scall hi [evar 108%Z])', '(scall hc [evar 108%Z])',
                      '(V293_TCB_publish 108%Z 93%Z 94%Z 95%Z 96%Z)',
                      '(V293_TCBInit_function_body hi hc)']:
            self.assertIn(token, statement)
        self.assertNotIn('V293_TCBInit_success_suffix', statement)
        self.assertNotRegex(statement, r'\b(evalval|evaladdr|sfexec|V293_stmt_exec)\b')
        self.assertIn('V293_tcb_table_success_view', text)

    def test_joint_literal_entries_and_separate_readback(self):
        text = PROBE.read_text()
        for name in ['PriorityLiteralEntry', 'PriorityInitialEntry', 'PriorityBetweenHooksEntry',
                     'PrioritySlotRead', 'PriorityWrongSlotRead', 'PriorityFreeHeadPreserved', 'PriorityCoreSize']:
            self.assertIn('Theorem ' + name, text)
        self.assertIn('Definition PriorityChecked', text)
        self.assertIn('Definition PriorityBodyChecked', text)
        self.assertIn('PriorityPre false Vundef Vundef Vundef cs', text)
        self.assertIn('=30', text)
        self.assertIn('=85', text)
        self.assertIn('PriorityTableSpatial', text)
        self.assertIn('PriorityRGood', text)
        self.assertIn('PriorityRCurLINV', text)
        self.assertIn('Definition PrioritySentinel', text)

    def test_exactly_once_in_active_build(self):
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(str(PROOF.relative_to(ROOT))), 1)

if __name__ == '__main__':
    unittest.main()
