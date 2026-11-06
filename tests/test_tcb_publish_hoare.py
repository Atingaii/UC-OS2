"""结构回归；Hoare 信用来自 coqc/coqchk，不来自文本匹配。"""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
PROOF = ROOT / 'certiucos/v293/proofs/V293TCBPublishHoare.v'
PROBE = ROOT / 'audit/probes/V293TCBPublishHoareProbe.v'

class TCBPublishHoareTests(unittest.TestCase):
    def test_no_new_assumptions_or_probe_dependencies(self):
        for path in [PROOF, PROBE]:
            self.assertNotRegex(path.read_text(), r'\b(Axiom|Parameter|Conjecture|Admitted|admit)\b')
            self.assertNotRegex(path.read_text(), r'Require(?: Import)? CertiOS\.audit\.probes\.')

    def test_unconditional_real_body_without_execution_oracle(self):
        text = PROOF.read_text()
        for name in ['V293_OS_TCBInit_publish_body_hoare', 'V293_OS_TCBInit_publish_hoare']:
            statement = text.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]
            self.assertEqual(statement.count('InfRules '), 1)
            self.assertNotRegex(statement, r'\b(evalval|evaladdr|sfexec|exec|V293_stmt_exec)\b')
        for token in ['V293_raw_assign_hoare', 'V293_pub_field_value', 'V293_byte_array_offset_eval',
                      'V293_tcb_init_read Owned 9 CountRead', 'V293_rekey_byte_narrow']:
            self.assertIn(token, text)
        self.assertNotIn('V293_OS_TCBInit_publication_execution', text)

    def test_both_old_head_cases_and_actual_backlink_store(self):
        text = PROOF.read_text()
        branch = text.split('Lemma V293_pub_backlink_hoare :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('destruct present.', branch)
        self.assertEqual(branch.count('eapply ift_rule'), 2)
        self.assertIn('V293_publish_store 10', branch)
        self.assertIn('apply pfalse_rule', branch)
        self.assertIn('V293_pub_guard_eval', branch)

    def test_critical_bracket_return_and_rule_sound(self):
        text = PROOF.read_text()
        theorem = text.split('Theorem V293_OS_TCBInit_publish_hoare :', 1)[1].split('Qed.', 1)[0]
        for token in ['V293_pub_critical_enter', 'V293_OS_TCBInit_publish_body_hoare',
                      'V293_pub_critical_exit', 'apply rete_rule', 'Vint32 Int.zero']:
            self.assertIn(token, theorem)
        self.assertIn('V293_OS_TCBInit_publish_semantics', text)
        self.assertIn('apply RuleSound', text)

    def test_independent_joint_entries_readback_and_existing_bits(self):
        text = PROBE.read_text()
        for name in ['PubLiteralEntry', 'PubInitialEntry', 'PubReturnEntry', 'PubCounterRead',
                     'PubWrongCounterRead', 'PubReadyBitsRead', 'PubPreservesOldReadyBits',
                     'PubLinksRead', 'PubOldBacklinkRead', 'PubReturnedZero', 'PubCoreSize']:
            self.assertIn('Theorem ' + name, text)
        for token in ['Definition PubChecked', 'PubRGood', 'PubRCurLINV', 'Definition PubSentinel',
                      'Int.repr 128', 'Int.repr 256', 'then 255 else 254', '=22', '=26']:
            self.assertIn(token, text)

    def test_exactly_once_in_active_build(self):
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(str(PROOF.relative_to(ROOT))), 1)

if __name__ == '__main__':
    unittest.main()
