"""资源逻辑参数编码及真实 builder 连接回归；Coq 负责语义证明。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage191-interrupt-resource-codec'
PROD = 'certiucos/v293/proofs/V293OSIntExitResourceCodec.v'
PROBE = 'audit/probes/V293OSIntExitResourceCodecProbe.v'


def read(name):
    return json.loads((D / name).read_text())


class InterruptResourceCodecTests(unittest.TestCase):
    def test_source_and_prospective_protocol_identity(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        for path, digest in source['files'].items():
            self.assertEqual(hashlib.sha256((R / path).read_bytes()).hexdigest(), digest)
            self.assertEqual(digest, read('baseline.json')['files'][path])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(), read('protocol-identity.json')['protocol.json'])
        old = R / 'audit/logs/stage190-interrupt-indexed-port/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_bounded_lossless_payload_and_malformed_rejection(self):
        src = (R / PROD).read_text()
        for name in ('V293_exit_codec_roundtrip', 'V293_exit_decode_bounded', 'V293_exit_select_encoded'):
            self.assertIn('Lemma ' + name + ' :', src)
        codec = src.split('Definition V293_exit_encode', 1)[1].split('Lemma V293_exit_codec_roundtrip', 1)[0]
        for field in ('lo', 'hi', 'current', 'nest', 'locked', 'counter', 'old', 'token', 'value', 'entries', 'tasks', 'aop'):
            self.assertIn('V293_x' + field, codec)
        self.assertIn('logic_abstcb', codec)
        self.assertIn('else None', codec)
        probe = (R / PROBE).read_text()
        for name in ('RCreject_empty', 'RCreject_extra_field', 'RCreject_out_of_byte', 'RCcodec_full_payload'):
            self.assertIn('Theorem ' + name + ' :', probe)

    def test_real_builder_without_four_matching_premises(self):
        src = (R / PROD).read_text()
        stmt = src.split('Theorem V293_OSIntExit_encoded_builder_contract :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(stmt.count('InfRules'), 2)
        for token in ('BuildPreI P f vl lg', 'BuildRetI P f vl lg', 'Int.add c Int.one', '(forall bs,run=1', '(scall int_switch nil)'):
            self.assertIn(token, stmt)
        for name in ('entryF enter_lg', 'acquiredF enter_lg', 'leavingF exit_lg', 'restoredF exit_lg'):
            self.assertNotIn(name, stmt)
        self.assertIn('eapply V293_OSIntExit_indexed_builder_contract', src)
        self.assertEqual(src.count('rewrite V293_exit_select_encoded by exact Bound'), 4)
        self.assertNotIn('CertiOS.audit.', src)
        self.assertNotIn('sprim', src)

    def test_enabled_and_disabled_same_spec_nonempty_physical_controls(self):
        src = (R / PROBE).read_text()
        for name in ('RCenabled_same_priority', 'RCdisabled_nested', 'RCbuilder_pre_nonempty',
                     'RCcounter_control', 'RCnest_control', 'RCcounter_frame', 'RCnest_frame'):
            self.assertIn('Theorem ' + name + ' :', src)
        self.assertIn('InfRules RCspec', src)
        self.assertIn('RCbuilderpost 12 1 c', src)
        self.assertIn('RCbuilderpost 0 2 c', src)
        self.assertIn('forall nc nest c value,RCbigstate nc nest c 1 value |= RCbuilderpre nc nest c', src)
        self.assertIn('mapstoval_load', src)
        self.assertIn('RCentry_nonempty', src)
        self.assertNotIn('vm_compute in', src)

    def test_stable_compiles_recursive_trust_and_no_new_holes(self):
        stable = read('stable-compiles.json')
        for kind, path in (('body', PROD), ('probe', PROBE)):
            row = read(stable[kind] + '.json')
            digest = hashlib.sha256((R / path).read_bytes()).hexdigest()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['source_sha256'], digest)
            self.assertEqual(row['initial_source_sha256'], digest)
            self.assertNotRegex((R / path).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
        trust = read('trust.json')
        self.assertTrue(trust['passed'])
        self.assertTrue(trust['recursive'])
        self.assertEqual(trust['roots_printed'], len(trust['roots']))
        self.assertTrue(set(trust['assumptions']) <= set(trust['allowed']))
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))


if __name__ == '__main__':
    unittest.main()
