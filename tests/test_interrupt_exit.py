"""原 OSIntExit 的真实递减/守卫连接；不把完整 AST 计作完整函数证明。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage184-interrupt-exit'
CODE = 'certiucos/v293/code/V293OSIntExit.v'
PROD = 'certiucos/v293/proofs/V293OSIntExitHoare.v'
PROBE = 'audit/probes/V293OSIntExitProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]


class InterruptExitTests(unittest.TestCase):
    def test_fixed_configured_source_and_prospective_protocol(self):
        src = read('source-check.json')
        self.assertTrue(src['passed'])
        for path, digest in src['files'].items():
            self.assertEqual(hashlib.sha256((R / path).read_bytes()).hexdigest(), digest)
            self.assertEqual(digest, read('baseline.json')['files'][path])
        entry = src['function']
        self.assertEqual((entry['name'], entry['first_line'], entry['last_line']), ('OSIntExit', 693, 736))
        self.assertEqual(entry['direct_calls'], ['OSIntCtxSw', 'OS_SchedNew', 'V293_EnterCritical', 'V293_ExitCritical'])
        self.assertEqual(hashlib.sha256((D / 'OSIntExit.configured.c.txt').read_bytes()).hexdigest(), entry['preprocessed_definition_sha256'])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(), read('protocol-identity.json')['protocol.json'])
        previous = R / 'audit/logs/stage183-interrupt-enter/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(previous.read_bytes()).hexdigest(), src['previous_manifest_sha256'])

    def test_raw_body_preserves_cpu_calls_and_real_empty_else(self):
        src = (R / CODE).read_text()
        for token in ('ebinop olt (econst32 Int.zero)', 'ebinop ominus', 'Tint8',
                      'V293_OSSched_unlocked_prefix', 'V293_OSSched_increment',
                      'scall int_switch nil', 'scall enter', 'scall exit',
                      'dcons saved Tint32 dnil', 'sskip None', 'sret'):
            self.assertIn(token, src)
        self.assertNotIn('sprim', src)
        self.assertIn('sif (V293_OSSched_zero nesting)', src)
        self.assertIn('sif (V293_OSSched_zero lock)', src)
        for path in (CODE, PROD, PROBE):
            self.assertNotRegex((R / path).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
        self.assertNotIn('CertiOS.audit.', (R / PROD).read_text())

    def test_real_count_and_guard_interface_has_precise_residual(self):
        src = (R / PROD).read_text()
        theorem = statement(src, 'V293_OSIntExit_nesting_dispatch_hoare')
        for token in ('nest<256 -> locked<256', 'V293_exit_depth nest=0 -> locked=0 ->',
                      'dispatch q tid', 'V293_OSIntExit_nesting_dispatch',
                      'if V293_exit_enabled nest locked then q else'):
            self.assertIn(token, theorem)
        for token in ('V293_rdy_raw_load', 'V293_raw_assign_hoare', 'V293_exit_owned_eval',
                      'V293_exit_enabled_iff', 'RuleSound'):
            self.assertIn(token, src)
        self.assertNotIn('dispatch q tid', statement(src, 'V293_OSIntExit_disabled_hoare'))
        self.assertIn(r'(2<=nest \/ 0<locked)', statement(src, 'V293_OSIntExit_disabled_hoare'))
        self.assertIn('simulation.RuleSem', statement(src, 'V293_OSIntExit_nesting_dispatch_semantics'))

    def test_nonempty_controls_physical_load_and_single_factor_frames(self):
        src = (R / PROBE).read_text()
        for token in ('XEnonempty', 'XEfragment_checked', 'XEdisabled_checked',
                      'XEactual_eval', 'XEwrong_post_control', 'XEdecrement_ablation',
                      'XErun_frame', 'XEnest_frame', 'XElock_frame', 'rewrite Actual in Wrong'):
            self.assertIn(token, src)
        wrong = statement(src, 'XEwrong_post_control')
        self.assertIn('eq_dom_env', wrong)
        self.assertIn('XEpre 1(V293_exit_depth 2)0', wrong)
        self.assertIn('~(XEstate(XEmemory 1 1 0) |= XEpre 1 2 0)', wrong)
        count = statement(src, 'XEnesting_control')
        for n in (0, 1, 2, 255):
            self.assertIn('XEmemory 1 ' + str(n) + ' 0', count)
        for n in (0, 1, 2):
            self.assertIn('XEmemory ' + str(n) + ' 1 0', statement(src, 'XErun_control'))
        lock = statement(src, 'XElock_control')
        self.assertIn('XEmemory 1 0 0', lock)
        self.assertIn('XEmemory 1 0 1', lock)

    def test_actual_stable_compiles_and_recursive_trust(self):
        stable = read('stable-compiles.json')
        for kind, path in (('code', CODE), ('body', PROD), ('probe', PROBE)):
            row = read(stable[kind] + '.json')
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['source_sha256'], row['initial_source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256((R / path).read_bytes()).hexdigest())
        trust = read('trust.json')
        self.assertTrue(trust['passed'])
        self.assertTrue(trust['recursive'])
        self.assertEqual(len(trust['entry_modules']), 2)
        self.assertEqual(trust['roots_printed'], len(trust['roots']))
        self.assertTrue(set(trust['assumptions']) <= set(trust['allowed']))
        for row in trust['commands']:
            self.assertEqual(row['exit'], 0)


if __name__ == '__main__':
    unittest.main()
