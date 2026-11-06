"""同 Spec 函数环境连接的结构、来源与实际 Coq 证据回归。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage182-tick-function-environment'
PROD = 'certiucos/v293/proofs/V293TickFunctionEnvironment.v'
PROBE = 'audit/probes/V293TickFunctionEnvironmentProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]


class TickFunctionEnvironmentTests(unittest.TestCase):
    def test_fixed_source_and_frozen_previous_stage(self):
        base = read('baseline.json')['files']
        for path in read('source-check.json')['files']:
            self.assertEqual(hashlib.sha256((R / path).read_bytes()).hexdigest(), base[path])
        path = 'audit/logs/stage181-time-api-refinement/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256((R / path).read_bytes()).hexdigest(),
                         read('source-check.json')['previous_manifest_sha256'])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])

    def test_stable_environment_exposes_real_remaining_hook(self):
        src = (R / PROD).read_text()
        body = statement(src, 'V293_tick_scheduler_known_bodies')
        self.assertIn('f<>hook ->', body)
        for token in ('BuildPreI', 'BuildRetI', 'good_decllist', 'InfRules V293_tick_scheduler_spec'):
            self.assertIn(token, body)
        equivalent = statement(src, 'V293_tick_scheduler_environment')
        self.assertIn('WFFunEnv', equivalent)
        self.assertIn('<->', equivalent)
        self.assertIn('V293_tick_hook_remaining port', equivalent)
        residual = src.split('Definition V293_tick_hook_remaining', 1)[1].split('Theorem', 1)[0]
        for token in ('port=Some(Tvoid,d1,d2,body)', 'good_decllist', 'BuildPreI', 'BuildRetI',
                      'InfRules V293_tick_scheduler_spec sd li inv'):
            self.assertIn(token, residual)
        for token in ('V293_tick_shared_internal_contract', 'V293_OSSchedNew_internal_contract'):
            self.assertIn(token, src)
        self.assertNotIn('CertiOS.audit.', src)
        for path in (PROD, PROBE):
            self.assertNotRegex((R / path).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')

    def test_original_nonempty_builder_and_common_spec(self):
        src = (R / PROBE).read_text()
        for token in ('Theorem ENnonempty', 'BHmemory clock run', 'SNpre(SNlogic',
                      'proj2(BLallocated', 'Theorem ENtick_body', 'destruct(ENknown',
                      'BuildPreI(ENprogram port)', 'BuildRetI(ENprogram port)',
                      'Theorem ENapi_same_spec', 'ENli ENspec V293_scheduler ENinv lg',
                      'V293_time_ready_names_good', 'exact ENlocal', 'Theorem ENdisjoint',
                      'no_fun_same(V293_clock_api_unit'):
            self.assertIn(token, src)
        self.assertNotIn('Definition ENli:=fun', src)

    def test_domain_and_type_controls_are_separate(self):
        src = (R / PROD).read_text()
        missing = statement(src, 'V293_tick_scheduler_missing_hook')
        self.assertIn('~ EqDom', missing)
        wrong = statement(src, 'V293_tick_scheduler_wrong_hook_type')
        self.assertIn('EqDom(V293_tick_scheduler_program(Some(Tint32,d1,d2,body)))', wrong)
        self.assertIn('~WFFunEnv', wrong)
        probe = (R / PROBE).read_text()
        control = statement(probe, 'ENsame_type_control')
        self.assertIn('Some(Tvoid,d1,d2,body)', control)
        self.assertIn('ENremaining', control)
        self.assertIn('<->', control)

    def test_actual_stable_compile_and_recursive_trust(self):
        stable = read('stable-compiles.json')
        for label, path in ((stable['body'], PROD), (stable['probe'], PROBE)):
            row = read(label + '.json')
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['source_sha256'], hashlib.sha256((R / path).read_bytes()).hexdigest())
            self.assertEqual(row['source_sha256'], row['initial_source_sha256'])
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
