"""空语句规则及初始化 Hoare 接口的结构回归；不能替代 Coq 验证。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage75-init-misc-hoare'

class InitMiscHoareTests(unittest.TestCase):
    def test_exact_existing_function_not_rewritten(self):
        expected = {
            'certiucos/v293/code/V293OSInitMisc.v': '059a35aa7d0757b930cb65f19a53c873477d2f0ffae526f0c7e53456192c3cbc',
            'certiucos/v293/proofs/V293InitMisc.v': 'e668f014fa8fc770e719178564678381ea4636e718269b915bdddac842a2c916',
        }
        for name, digest in expected.items():
            self.assertEqual(hashlib.sha256((ROOT / name).read_bytes()).hexdigest(), digest)

    def test_replayed_c_has_exact_ten_zero_assignments(self):
        replay = json.loads((LOG / 'source/result.json').read_text())
        self.assertTrue(replay['all94_identities_equal'])
        selected = replay['selected']['OS_InitMisc']
        self.assertEqual(selected['identity']['preprocessed_body_sha256'],
                         'c46412d3e2adca015c1f5b24cfa1afc39456df56864665a2a2b82c210f7560f8')
        expected = [('OSTime', 'unsigned int'), ('OSIntNesting', 'unsigned char'),
                    ('OSLockNesting', 'unsigned char'), ('OSTaskCtr', 'unsigned char'),
                    ('OSRunning', 'unsigned char'), ('OSCtxSwCtr', 'unsigned int'),
                    ('OSIdleCtr', 'unsigned int'), ('OSIdleCtrRun', 'unsigned int'),
                    ('OSIdleCtrMax', 'unsigned int'), ('OSStatRdy', 'unsigned char')]
        actual = []
        for node in selected['clang_body']['inner']:
            self.assertEqual((node['kind'], node['opcode']), ('BinaryOperator', '='))
            lhs, rhs = node['inner']
            self.assertEqual(lhs['kind'], 'DeclRefExpr')
            actual.append((lhs['referencedDecl']['name'], node['type']['desugaredQualType']))
            while rhs['kind'] == 'ImplicitCastExpr':
                self.assertEqual(rhs['castKind'], 'IntegralCast')
                rhs, = rhs['inner']
            self.assertEqual((rhs['kind'], rhs['value']), ('IntegerLiteral', '0'))
        self.assertEqual(actual, expected)

    def test_skip_has_semantic_proof_and_soundness_branch(self):
        rules = (ROOT / 'framework/logic/inferules.v').read_text()
        rules = re.sub(r'\(\*.*?\*\)', '', rules, flags=re.S)
        self.assertRegex(rules, r'\| skip_rule : forall Spec sd pa I r ri p t v,\s*'
                               r'InfRules Spec sd pa I r ri p \(sskip v\) p t\.')
        sound = (ROOT / 'framework/proof/soundness.v').read_text()
        self.assertIn('Lemma skip_rule_sound', sound)
        self.assertIn('eapply skip_rule_sound.', sound)
        self.assertIn('[Hp Hlin]', sound)

    def test_stable_interface_keeps_real_invariant_and_syntax(self):
        text = (ROOT / 'certiucos/v293/proofs/V293InitMiscHoare.v').read_text()
        self.assertNotRegex(text, r'\b(Axiom|Admitted|admit|Parameter|Conjecture)\b')
        self.assertNotIn('CertiOS.audit.probes', text)
        self.assertIn('(R ==> CurLINV li tid) ->', text)
        self.assertIn('apply skip_rule.', text)
        self.assertIn('apply RuleSound.', text)
        self.assertIn('V293_OS_InitMisc_body_hoare', text)
        self.assertIn('V293_OS_InitMisc_body_semantics', text)
        self.assertIn('sseq (V293_InitMisc_updates', text)
