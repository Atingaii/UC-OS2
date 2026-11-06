"""原 OSIntExit 的资源分解与真实中段连接；非完整 port 或整核证明。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage187-interrupt-resource-bridge'
PROD = 'certiucos/v293/proofs/V293OSIntExitResourceBridge.v'
PROBE = 'audit/probes/V293OSIntExitResourceBridgeProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]


class InterruptResourceBridgeTests(unittest.TestCase):
    def test_fixed_source_and_prospective_protocol(self):
        src = read('source-check.json')
        self.assertTrue(src['passed'])
        for path, digest in src['files'].items():
            self.assertEqual(hashlib.sha256((R / path).read_bytes()).hexdigest(), digest)
            self.assertEqual(digest, read('baseline.json')['files'][path])
        self.assertEqual(src['function']['name'], 'OSIntExit')
        self.assertEqual(src['function']['direct_calls'], ['OSIntCtxSw', 'OS_SchedNew', 'V293_EnterCritical', 'V293_ExitCritical'])
        self.assertEqual(hashlib.sha256((D / 'OSIntExit.configured.c.txt').read_bytes()).hexdigest(), src['function']['preprocessed_definition_sha256'])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(), read('protocol-identity.json')['protocol.json'])
        prev = R / 'audit/logs/stage186-interrupt-critical-calls/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(prev.read_bytes()).hexdigest(), src['previous_manifest_sha256'])

    def test_bidirectional_ownership_and_callee_admissibility(self):
        src = (R / PROD).read_text()
        for name in ('V293_exit_pre_split', 'V293_exit_pre_join',
                     'V293_exit_tail_split', 'V293_exit_tail_join',
                     'V293_exit_physical_pre_good', 'V293_exit_physical_tail_good',
                     'V293_exit_caller_bindings_good'):
            self.assertIn('Lemma ' + name + ' :', src)
        for path in (PROD, PROBE):
            self.assertNotRegex((R / path).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            self.assertNotIn('CertiOS.audit.', (R / path).read_text())
        physical = src.split('Definition V293_exit_physical_pre', 1)[1].split('Let oldpre', 1)[0]
        self.assertNotIn('Alvarenv', physical)
        self.assertNotIn('A_notin_lenv', physical)
        for token in ('V293_read_pointers', 'Aabsdata abstcblsid', 'Amapsto(bcur',
                      'V293_rdy_raw_cells', 'V293_prefix_output', 'PV(bcounter'):
            self.assertIn(token, physical)

    def test_only_real_switch_residual_and_actual_call_composition(self):
        src = (R / PROD).read_text()
        for name in ('V293_OSIntExit_middle_bridge', 'V293_OSIntExit_resource_bridge'):
            main = statement(src, name)
            self.assertEqual(main.count('V293_OSIntExit_nesting_dispatch'), 1)
            self.assertIn('(scall int_switch nil)', main)
            self.assertIn('Int.add c Int.one', main)
            self.assertIn('V293_exit_depth nest=0 -> locked=0 ->', main)
            self.assertIn('V293_ready_select lo hi(V293_ready_group lo hi)<>nc', main)
            self.assertNotIn('V293_OSIntExit_body', main)
        main = statement(src, 'V293_OSIntExit_resource_bridge')
        for token in ('Spec sched_id=Some', 'Spec enter=Some', 'Spec exit=Some',
                      'scall enter ((eaddrof(evar saved))::nil)',
                      'scall exit ((eaddrof(evar saved))::nil)'):
            self.assertIn(token, main)
        self.assertIn('eapply V293_OSIntExit_ready_dispatch', src)
        self.assertIn('eapply V293_OSIntExit_critical_calls', src)
        self.assertIn('Fixed-owner, empty-logic-argument contracts', src)
        self.assertNotIn('sprim', src)

    def test_full_resources_shadow_and_counter_single_factor_controls(self):
        src = (R / PROBE).read_text()
        for name in ('RBcomplete_acquired_nonempty', 'RBcomplete_tail_nonempty',
                     'RBshadow_control', 'RBcounter_load', 'RBcounter_control',
                     'RBcounter_frame', 'RBlookup_ablation'):
            self.assertIn(name, src)
        shadow = statement(src, 'RBshadow_control')
        self.assertEqual(shadow.count('RBfullmemory 0 Vnull 1 0 0 Int.zero'), 3)
        self.assertIn('RBle false', shadow)
        self.assertIn('RBle true', shadow)
        counter = statement(src, 'RBcounter_control')
        self.assertEqual(counter.count('RBle false'), 3)
        self.assertEqual(counter.count('RBfullmemory 0 Vnull 1 0 0 Int.one'), 2)
        self.assertIn('rewrite Actual in Wrong', src)
        self.assertIn('b<>14%positive', src)
        self.assertNotIn('InfRules', statement(src, 'RBlookup_ablation'))

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
