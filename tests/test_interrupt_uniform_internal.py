"""统一内部规格回归；结构检查不代替 Coq 语义证明。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage193-interrupt-uniform-internal'
PROD = 'certiucos/v293/proofs/V293OSIntExitInternal.v'
PROBE = 'audit/probes/V293OSIntExitInternalProbe.v'


def read(name):
    return json.loads((D / name).read_text())


class InterruptUniformInternalTests(unittest.TestCase):
    def test_exact_source_and_protocol(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        for p, h in source['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
            self.assertEqual(h, read('baseline.json')['files'][p])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(), read('protocol-identity.json')['protocol.json'])
        old = R / 'audit/logs/stage192-interrupt-switch-call/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_uniform_internal_contract_real_builders(self):
        src = (R / PROD).read_text()
        stmt = src.split('Theorem V293_OSIntExit_internal_contract :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(stmt.count('InfRules'), 1)
        for token in ('vl lg tid pre post', 'BuildPreI P f vl lg', 'BuildRetI P f vl lg', 'V293_exit_internal_fpre', 'V293_exit_internal_fpost'):
            self.assertIn(token, stmt)
        self.assertIn('eapply V293_OSIntExit_port_lookup_builder_contract', src)
        self.assertNotIn('CertiOS.audit.', src)
        self.assertNotIn('sprim', src)

    def test_dynamic_index_and_pure_validity_not_new_primitive(self):
        src = (R / PROD).read_text()
        for token in ('V293_exit_internal_encode', 'V293_exit_internal_index', 'V293_exit_internal_valid',
                      'V293_exit_internal_pre_asrt', 'V293_exit_internal_post_asrt', 'V293_exit_decode',
                      'pure_split_rule', 'pfalse_rule'):
            self.assertIn(token, src)
        self.assertIn('logic_val(Vint32', src)
        self.assertIn('V293_bitmap_tasks', src)
        self.assertIn('V293_priority_table', src)

    def test_same_spec_real_builder_and_physical_controls(self):
        src = (R / PROBE).read_text()
        for root in ('UIbuilders', 'UIenabled_different', 'UIenabled_same', 'UIdisabled_nested',
                     'UInot_running', 'UIpre_nonempty', 'UIrunning_control', 'UIcounter_control',
                     'UIrunning_frame', 'UIreject_runtime_argument', 'UIreject_bad_logic'):
            self.assertIn('Theorem ' + root + ' :', src)
        self.assertIn('InfRules SCspec', src)
        self.assertIn('load Tint8', src)
        self.assertIn('load Tint32', src)
        self.assertIn('RCbigstate', src)

    def test_stable_compiles_recursive_trust_and_no_holes(self):
        stable = read('stable-compiles.json')
        for kind, p in (('body', PROD), ('probe', PROBE)):
            row = read(stable[kind] + '.json')
            h = hashlib.sha256((R / p).read_bytes()).hexdigest()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(h, row['initial_source_sha256'])
            self.assertEqual(h, row['source_sha256'])
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
        trust = read('trust.json')
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(trust['roots_printed'], len(trust['roots']))
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))
