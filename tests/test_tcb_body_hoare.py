"""整函数双分支接口的结构防回退；证明成立性以 Coq 内核为准。"""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
PROOF = ROOT / 'certiucos/v293/proofs/V293TCBBodyHoare.v'
PROBE = ROOT / 'audit/probes/V293TCBBodyHoareProbe.v'

class TCBBodyHoareTests(unittest.TestCase):
    def test_no_unproved_terms_or_old_probe_imports(self):
        for path in [PROOF, PROBE]:
            text = path.read_text()
            self.assertNotRegex(text, r'\b(Axiom|Parameter|Conjecture|Admitted|admit|Abort)\b')
            self.assertNotRegex(text, r'Require(?: Import)? CertiOS\.audit\.probes\.')

    def test_same_complete_body_both_entries_no_hoare_oracle(self):
        text = PROOF.read_text()
        statement = text.split('Theorem V293_OS_TCBInit_body_hoare :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(statement.count('InfRules '), 1)
        self.assertEqual(statement.count('Spec hi=Some('), 1)
        self.assertEqual(statement.count('Spec hc=Some('), 1)
        self.assertIn('(V293_tcb_empty_state bg bc bu pc cpu E aop isr is cs) \\\\//', statement)
        self.assertIn('V293_tcb_table_state table slot', statement)
        self.assertIn('(Vptr(bt,Int.repr base)) next', statement)
        self.assertEqual(statement.count('(V293_TCBInit_function_body hi hc)'), 1)
        self.assertNotRegex(statement, r'\b(evalval|evaladdr|sfexec|V293_stmt_exec|bool)\b')
        self.assertIn('GoodFrm E -> (E ==> CurLINV li tid)', statement)
        self.assertIn('Hfun:GoodFunAsrt R', statement)

    def test_join_uses_real_rules_and_both_prior_body_proofs(self):
        text = PROOF.read_text()
        for token in ['apply disj_rule', 'eapply r_conseq_rule',
                      'apply V293_OS_TCBInit_empty_body_hoare',
                      'eapply V293_OS_TCBInit_hook_calls_body_hoare', 'apply RuleSound']:
            self.assertIn(token, text)

    def test_exact_return_branch_and_no_resource_erasure(self):
        text = PROOF.read_text()
        definition = text.split('Definition V293_tcb_body_post', 1)[1].split('Lemma ', 1)[0]
        self.assertIn('Int.repr 66', definition)
        self.assertIn('Int.zero', definition)
        self.assertIn('** empty', definition)
        self.assertIn('** ready', definition)
        self.assertNotIn('Atrue', definition)
        for name in ['codes', 'empty', 'ready', 'no_other', 'no_void']:
            self.assertIn('Lemma V293_tcb_body_post_' + name, text)
        self.assertIn('s |= empty.', text)
        self.assertIn('s |= ready.', text)

    def test_literal_entries_and_same_environments(self):
        text = PROBE.read_text()
        for name in ['BodyEmptyJointEntry', 'BodyNonemptyJointEntry', 'BodySharedEnvironments',
                     'BodyCombinedChecked', 'BodyCombinedDeclaredContracts', 'BodyEmptyReturnExact',
                     'BodyReadyReturnExact', 'BodyRejectsVoid', 'BodyRejectsWrongCode']:
            self.assertIn('Theorem ' + name, text)
        self.assertIn('Definition BodyEmptyGE : env := BodyGE.', text)
        self.assertIn('Definition BodyEmptyLE : env := BodyLE.', text)
        self.assertIn('BodyState BodyEmptyMemory cs |= BodyCombinedPre', text)
        self.assertIn('BodyState(BodyWhole false present)cs |= BodyCombinedPre', text)
        self.assertIn('Definition BodyEmptyNoHookSpec : funspec := fun _=>None.', text)
        self.assertIn('Theorem BodyEmptyBodyNoHook', text)

    def test_active_build_once(self):
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(str(PROOF.relative_to(ROOT))), 1)

if __name__ == '__main__':
    unittest.main()
