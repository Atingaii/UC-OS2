"""原 OSIntEnter 的源码、真实 builder、字节消融及实际证明证据。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage183-interrupt-enter'
CODE = 'certiucos/v293/code/V293OSIntEnter.v'
PROD = 'certiucos/v293/proofs/V293OSIntEnterInternal.v'
PROBE = 'audit/probes/V293OSIntEnterProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]


class InterruptEnterTests(unittest.TestCase):
    def test_fixed_source_and_prospective_protocol(self):
        src = read('source-check.json')
        self.assertTrue(src['passed'])
        for path, digest in src['files'].items():
            self.assertEqual(hashlib.sha256((R / path).read_bytes()).hexdigest(), digest)
            self.assertEqual(digest, read('baseline.json')['files'][path])
        self.assertEqual(src['function']['name'], 'OSIntEnter')
        self.assertEqual(src['function']['category'], 'public')
        self.assertEqual(src['function']['direct_calls'], [])
        self.assertTrue(src['reconstructed_repaired_source_matches'])
        self.assertIn('OSIntNesting < 255u', src['configured_definition'])
        previous = R / 'audit/logs/stage182-tick-function-environment/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(previous.read_bytes()).hexdigest(), src['previous_manifest_sha256'])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])

    def test_real_body_and_full_contract(self):
        code = (R / CODE).read_text()
        for token in ('ebinop oeq', 'ebinop olt', 'sassign (evar nesting)',
                      'Int.repr 255', 'Tint8', 'sskip None', 'sret', 'Tvoid,dnil,dnil'):
            self.assertIn(token, code)
        src = (R / PROD).read_text()
        contract = statement(src, 'V293_OSIntEnter_internal_contract')
        for token in ('BuildPreI P f vl lg', 'BuildRetI P f vl lg',
                      'InfRules Spec sd li I post Afalse pre', 'V293_OSIntEnter_body'):
            self.assertIn(token, contract)
        self.assertIn('WFFunEnv', statement(src, 'V293_OSIntEnter_WFFunEnv'))
        for token in ('run<256 -> nest<256', 'Aie false', 'V293_interrupt_owned_eval',
                      'V293_raw_assign_hoare', 'V293_interrupt_builder_env'):
            self.assertIn(token, src)
        for path in (CODE, PROD, PROBE):
            self.assertNotRegex((R / path).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
        self.assertNotIn('CertiOS.audit.', src)

    def test_nonempty_real_entry_and_actual_evaluation(self):
        src = (R / PROBE).read_text()
        nonempty = statement(src, 'IEnonempty_builders')
        for token in ('BuildPreI IEprogram', 'IEstate(IEmemory run nest) |= pre',
                      'run<256 -> nest<256'):
            self.assertIn(token, nonempty)
        for token in ('V293_encoded_memory', 'IEcurrent_owned', 'IEresource_owned',
                      'IEpre_owned', 'IEbuilders', 'IEbody_checked', 'IEenvironment',
                      'V293_interrupt_owned_eval', 'V293_interrupt_builder_env'):
            self.assertIn(token, src)
        self.assertIn('evalval(V293_OSIntEnter_running', statement(src, 'IEactual_eval'))
        self.assertIn('evalval(V293_OSIntEnter_room', statement(src, 'IEactual_eval'))

    def test_single_byte_controls_and_independent_post_load(self):
        src = (R / PROBE).read_text()
        run = statement(src, 'IErun_control')
        for n in (0, 1, 2):
            self.assertIn('IEmemory ' + str(n) + ' 254', run)
        saturated = statement(src, 'IEsaturation_control')
        self.assertIn('IEmemory 1 254', saturated)
        self.assertIn('IEmemory 1 255', saturated)
        self.assertIn('V293_interrupt_nest_after 1 255=255', saturated)
        wrong = statement(src, 'IEwrong_post_control')
        for token in ('eq_dom_env', 'IEpost 1 254', '~ (IEstate(IEmemory 1 255) |= IEpost 1 253)'):
            self.assertIn(token, wrong)
        self.assertIn('V293_rdy_raw_load', src)
        self.assertIn('rewrite Actual in Wrong', src)
        self.assertIn('IEnot_running_outputs', src)

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
