"""原 OSIntExit 完整 body 的条件连接，不代表生产函数或整核证明。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage188-interrupt-full-body'
PROD = 'certiucos/v293/proofs/V293OSIntExitBody.v'
PROBE = 'audit/probes/V293OSIntExitBodyProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]


class InterruptFullBodyTests(unittest.TestCase):
    def test_exact_source_and_frozen_prospective_protocol(self):
        src = read('source-check.json')
        self.assertTrue(src['passed'])
        for path, digest in src['files'].items():
            self.assertEqual(hashlib.sha256((R / path).read_bytes()).hexdigest(), digest)
            self.assertEqual(digest, read('baseline.json')['files'][path])
        self.assertEqual(src['function']['name'], 'OSIntExit')
        self.assertEqual(src['function']['direct_calls'], ['OSIntCtxSw', 'OS_SchedNew', 'V293_EnterCritical', 'V293_ExitCritical'])
        self.assertEqual(hashlib.sha256((D / 'OSIntExit.configured.c.txt').read_bytes()).hexdigest(), src['function']['preprocessed_definition_sha256'])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(), read('protocol-identity.json')['protocol.json'])
        prev = R / 'audit/logs/stage187-interrupt-resource-bridge/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(prev.read_bytes()).hexdigest(), src['previous_manifest_sha256'])

    def test_complete_original_body_has_only_actual_switch_statement_residual(self):
        src = (R / PROD).read_text()
        main = statement(src, 'V293_OSIntExit_body_hoare')
        self.assertEqual(main.count('InfRules'), 2)
        self.assertEqual(main.count('V293_OSIntExit_body running'), 1)
        self.assertEqual(main.count('(scall int_switch nil)'), 1)
        for token in ('run=1 -> Spec sched_id=Some', 'run=1 -> Spec enter=Some',
                      'run=1 -> Spec exit=Some',
                      'run=1 -> V293_exit_depth nest=0 -> locked=0 ->',
                      'V293_ready_select lo hi(V293_ready_group lo hi)<>nc',
                      'Int.add c Int.one', 'result=None', 'oldsave'):
            self.assertIn(token, main)
        self.assertNotIn('V293_OSIntExit_nesting_dispatch', main)
        for token in ('apply V293_OSIntExit_saved_initialize',
                      'eapply V293_tick_known_ift_hoare',
                      'eapply (V293_OSIntExit_resource_bridge',
                      'apply ret_rule', 'rewrite On in Call'):
            self.assertIn(token, src)
        for path in (PROD, PROBE):
            text = (R / path).read_text()
            self.assertNotRegex(text, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            self.assertNotIn('CertiOS.audit.', text)
            self.assertNotIn('sprim', text)

    def test_nonrunning_path_requires_no_lookup_or_middle_proof(self):
        src = (R / PROD).read_text()
        off = statement(src, 'V293_OSIntExit_not_running_body')
        self.assertEqual(off.count('InfRules'), 1)
        self.assertNotIn('Spec sched_id=', off)
        self.assertNotIn('Spec enter=', off)
        self.assertNotIn('Spec exit=', off)
        self.assertIn('run<>1', off)
        self.assertIn('V293_exit_body_at', off)
        probe = statement((R / PROBE).read_text(), 'FBno_lookup_body')
        self.assertIn('InfRules(fun _=>None)', probe)
        self.assertIn('V293_OSIntExit_body', probe)
        self.assertIn('FBfullpre run old', probe)
        self.assertIn('FBfullat run', probe)

    def test_nonempty_resources_and_actual_load_single_factor_controls(self):
        src = (R / PROBE).read_text()
        for name in ('FBfull_pre_nonempty', 'FBfull_initialized_nonempty',
                     'FBrunning_read', 'FBrunning_control', 'FBrunning_frame',
                     'FBsaved_load', 'FBsaved_control', 'FBsaved_frame'):
            self.assertIn(name, src)
        control = statement(src, 'FBrunning_control')
        for run in (0, 1, 2, 255):
            self.assertIn('FBfullstate ' + str(run) + '(Vint32 Int.one)', control)
        self.assertEqual(control.count('Some(Vint32 Int.one)'), 1)
        self.assertEqual(control.count('Some(Vint32 Int.zero)'), 3)
        self.assertIn('evaltype', statement(src, 'FBrunning_read'))
        saved = statement(src, 'FBsaved_control')
        self.assertEqual(saved.count('FBfullstate 0(Vint32 Int.one)'), 2)
        self.assertIn('rewrite Actual in Wrong', src)
        self.assertIn('b<>16%positive', src)
        self.assertIn('b<>15%positive', src)
        prod = (R / PROD).read_text()
        self.assertIn('rewrite L.', prod)
        self.assertIn('V293_interrupt_eq_one', prod)

    def test_stable_compiles_and_recursive_trust(self):
        stable = read('stable-compiles.json')
        for kind, path in (('body', PROD), ('probe', PROBE)):
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
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))


if __name__ == '__main__':
    unittest.main()
