"""无实参切换规格接入；字符串回归不代替 Coq 语义证据。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage192-interrupt-switch-call'
PROD = 'certiucos/v293/proofs/V293OSIntExitSwitchCall.v'
PROBE = 'audit/probes/V293OSIntExitSwitchCallProbe.v'


def read(name):
    return json.loads((D / name).read_text())


class InterruptSwitchCallTests(unittest.TestCase):
    def test_frozen_source_and_prospective_protocol(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        for path, digest in source['files'].items():
            self.assertEqual(hashlib.sha256((R / path).read_bytes()).hexdigest(), digest)
            self.assertEqual(digest, read('baseline.json')['files'][path])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(), read('protocol-identity.json')['protocol.json'])
        old = R / 'audit/logs/stage191-interrupt-resource-codec/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_nullary_runtime_call_and_logical_saved_address(self):
        src = (R / PROD).read_text()
        self.assertIn('Theorem V293_nullary_call :', src)
        self.assertIn('eapply call_rule', src)
        self.assertIn('(vl:=nil)(logicl:=lg)(tp:=Tvoid)(tl:=nil)', src)
        self.assertIn('logic_val(Vptr address)::V293_exit_encode x', src)
        self.assertIn('Lemma V293_exit_switch_select_encoded :', src)
        self.assertIn('Int.add(V293_xcounter x)Int.one', src)
        self.assertNotIn('CertiOS.audit.', src)
        self.assertNotIn('sprim', src)

    def test_complete_builder_only_lookup_not_statement_premise(self):
        src = (R / PROD).read_text()
        stmt = src.split('Theorem V293_OSIntExit_port_lookup_builder_contract :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(stmt.count('InfRules'), 1)
        for token in ('BuildPreI P f vl lg', 'BuildRetI P f vl lg', 'Spec int_switch=Some', '(Tvoid,nil)'):
            self.assertIn(token, stmt)
        self.assertNotIn('(scall int_switch nil)', stmt)
        self.assertIn('eapply V293_OSIntExit_encoded_builder_contract', src)
        self.assertIn('apply V293_nullary_call', src)

    def test_same_spec_branch_and_independent_physical_controls(self):
        src = (R / PROBE).read_text()
        for name in ('SCenabled_different', 'SCenabled_same', 'SCdisabled_nested', 'SCbuilder_pre_nonempty',
                     'SCswitch_pre_nonempty', 'SCcounter_control', 'SCaddress_control', 'SCcounter_frame',
                     'SCreject_runtime_argument', 'SCreject_bad_logical_address'):
            self.assertIn('Theorem ' + name + ' :', src)
        self.assertIn('InfRules SCspec', src)
        self.assertIn('mapstoval_load', src)
        self.assertIn('RBtailresource_owned', src)
        self.assertIn('RCbuilder_pre_nonempty', src)

    def test_stable_compiles_recursive_trust_no_holes(self):
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
