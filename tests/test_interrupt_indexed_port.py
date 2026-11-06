"""索引临界规格的连接回归；语义结论由对应 Coq 根提供。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage190-interrupt-indexed-port'
PROD = 'certiucos/v293/proofs/V293OSIntExitIndexedPort.v'
PROBE = 'audit/probes/V293OSIntExitIndexedPortProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]


class InterruptIndexedPortTests(unittest.TestCase):
    def test_locked_source_and_prospective_controls(self):
        src = read('source-check.json')
        self.assertTrue(src['passed'])
        for path, digest in src['files'].items():
            self.assertEqual(hashlib.sha256((R / path).read_bytes()).hexdigest(), digest)
            self.assertEqual(digest, read('baseline.json')['files'][path])
        self.assertEqual(src['function']['name'], 'OSIntExit')
        self.assertEqual(hashlib.sha256((D / 'OSIntExit.configured.c.txt').read_bytes()).hexdigest(), src['function']['preprocessed_definition_sha256'])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(), read('protocol-identity.json')['protocol.json'])
        prev = R / 'audit/logs/stage189-interrupt-function-builders/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(prev.read_bytes()).hexdigest(), src['previous_manifest_sha256'])

    def test_one_spec_consumes_task_and_nonempty_logical_arguments(self):
        src = (R / PROD).read_text()
        pre = src.split('Definition V293_indexed_pointer_fpre', 1)[1].split('Theorem V293_indexed_pointer_call', 1)[0]
        self.assertIn('resource lg t address', pre)
        self.assertNotIn('owner', pre)
        self.assertNotIn('lg=nil', pre)
        self.assertIn('(logicl:=lg)', src)
        self.assertIn('eapply call_rule', src)
        self.assertIn('eapply V293_saved_pointer_argument', src)
        probe = (R / PROBE).read_text()
        multi = statement(probe, 'IPtwo_tasks_one_spec')
        self.assertIn('forall sd I r ri t v', multi)
        self.assertIn('InfRules IPspec', multi)
        self.assertIn('cons (logic_val(Vint32 v)) nil', multi)
        self.assertIn('IPindependent_witnesses', probe)

    def test_direct_old_middle_and_complete_original_body(self):
        src = (R / PROD).read_text()
        bridge = statement(src, 'V293_OSIntExit_indexed_bridge')
        self.assertEqual(bridge.count('InfRules'), 2)
        self.assertIn('(scall int_switch nil)', bridge)
        self.assertRegex(src, r'\b(?:apply|eapply) V293_OSIntExit_middle_bridge with')
        self.assertIn('eapply V293_OSIntExit_indexed_bridge', src)
        self.assertIn('apply V293_OSIntExit_saved_initialize', src)
        self.assertIn('V293_exit_running_eval', src)
        self.assertIn('apply ret_rule', src)
        self.assertNotIn('sprim', src)
        self.assertNotIn('CertiOS.audit.', src)

    def test_real_builders_keep_explicit_family_and_switch_obligations(self):
        src = (R / PROD).read_text()
        main = statement(src, 'V293_OSIntExit_indexed_builder_contract')
        self.assertEqual(main.count('InfRules'), 2)
        self.assertEqual(main.count('(scall int_switch nil)'), 1)
        for token in ('BuildPreI P f vl lg', 'BuildRetI P f vl lg',
                      'run=1 -> entryF enter_lg tid=', 'run=1 -> acquiredF enter_lg tid=',
                      'run=1 -> leavingF exit_lg tid=', 'run=1 -> restoredF exit_lg tid=',
                      '(forall bs,run=1 -> V293_exit_depth nest=0', 'Int.add c Int.one'):
            self.assertIn(token, main)
        self.assertIn('V293_exit_builder_identify', src)
        self.assertIn('V293_exit_builder_unpack', src)
        self.assertIn('V293_exit_builder_pack', src)
        self.assertIn('apply ex_intro_rule;intro oldsave;apply ex_intro_rule;intro bs', src)
        self.assertNotIn('oldsave', main)

    def test_physical_single_factor_controls_and_nonvacuous_running_builder(self):
        src = (R / PROBE).read_text()
        for name in ('IPtask_index_control', 'IPlogical_value_control', 'IPsaved_value_control',
                     'IPtask_change_frame', 'IPsaved_frame', 'IPold_owner_rejects',
                     'IPold_empty_lg_rejects', 'IPrunning_builder', 'IPrunning_pre_nonempty',
                     'IPnot_running_builder'):
            self.assertIn('Theorem ' + name + ' :', src)
        self.assertIn('mapstoval_load', src)
        self.assertIn('IPcurrent_load', src)
        self.assertIn('IPowned', src)
        self.assertIn('V293_OSIntExit_indexed_builder_contract', src)
        self.assertIn('forall c value,IPbigstate c 1 value |= IPbuilderpre c', src)
        self.assertIn('else None', src.split('Definition IPrunningSpec', 1)[1].split('Definition IPbuilderpre', 1)[0])
        # This running fixture has nest=2. It does not exercise scheduler/switch.
        self.assertIn('(nest:=2)', src)
        self.assertIn('InfRules(fun _=>None)', statement(src, 'IPnot_running_builder'))

    def test_stable_compiles_and_recursive_trust(self):
        stable = read('stable-compiles.json')
        for kind, path in (('body', PROD), ('probe', PROBE)):
            row = read(stable[kind] + '.json')
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['source_sha256'], row['initial_source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256((R / path).read_bytes()).hexdigest())
            self.assertNotRegex((R / path).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
        trust = read('trust.json')
        self.assertTrue(trust['passed'])
        self.assertTrue(trust['recursive'])
        self.assertEqual(len(trust['entry_modules']), 2)
        self.assertEqual(trust['roots_printed'], len(trust['roots']))
        self.assertTrue(set(trust['assumptions']) <= set(trust['allowed']))
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))


if __name__ == '__main__':
    unittest.main()
