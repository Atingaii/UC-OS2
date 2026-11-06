"""共享快照统一规格的结构回归；不将文本匹配作为语义证明。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage176-tick-shared-snapshot'
PROD = 'certiucos/v293/proofs/V293TimeTickSharedSnapshot.v'
PROBE = 'audit/probes/V293TimeTickSharedSnapshotProbe.v'


class TickSharedSnapshotTests(unittest.TestCase):
    def test_fixed_source_and_predecessor(self):
        base = json.loads((D / 'baseline.json').read_text())['files']
        for p in ('certiucos/v293/code/V293OSTimeTick.v',
                  'framework/logic/inferules.v',
                  'certiucos/v293/proofs/V293TimeTickUniformSpec.v',
                  'audit/logs/stage175-tick-uniform-spec/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), base[p])

    def test_one_spec_uses_existing_logical_channel(self):
        src = (R / PROD).read_text()
        for name in ('V293_tick_shared_index', 'V293_tick_shared_guard',
                     'V293_tick_shared_fpre', 'V293_tick_shared_fpost',
                     'V293_tick_shared_hook_pre', 'V293_tick_shared_hook_post'):
            self.assertRegex(src, r'Definition ' + name + r'\b')
        for token in ('logic_absecb es', 'logic_is si', 'logic_cs ci',
                      '(logicl:=lg)', 'eapply call_rule',
                      'apply V293_tick_shared_hook_call', 'tid_eq_dec ct tid'):
            self.assertIn(token, src)
        variables = src.split('Section SharedSnapshot.', 1)[1].split('Let ir:', 1)[0]
        self.assertNotRegex(variables, r'\b(?:clock|run|ct|es|si|ci)\b')
        self.assertNotIn('CertiOS.audit.', src)
        for p in (PROD, PROBE):
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')

    def test_single_index_controls_on_nonempty_same_endpoint(self):
        src = (R / PROBE).read_text()
        for name in ('SNallocated', 'SNactual_fields', 'SNactual_stacks',
                     'SNsame_endpoint_event_control', 'SNsame_endpoint_is_control',
                     'SNsame_endpoint_cs_control', 'SNidentity_gate_control'):
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        for name in ('event', 'is', 'cs'):
            statement = src.split('Theorem SNsame_endpoint_' + name + '_control :', 1)[1].split('Proof.', 1)[0]
            endpoint = 'SNstate(BHmemory clock run)(SNabs clock ChainEvents)(PCcode run)[1][false]'
            self.assertEqual(statement.count(endpoint), 2)
        self.assertIn('ChainEvents[2][false]', src)
        self.assertIn('ChainEvents[1][true]', src)
        self.assertIn('ChainEvents[1][false]', src)
        self.assertIn('SNphysical_good', src)
        self.assertIn('goodfrm_prop', src)
        self.assertEqual(len(json.loads((D / 'protocol.json').read_text())['controls']), 4)

    def test_actual_builder_total_contract_not_full_environment(self):
        src = (R / PROD).read_text()
        theorem = src.split('Theorem V293_tick_shared_internal_contract :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('vl lg pre post', theorem)
        self.assertNotIn('run<256 ->', theorem)
        for token in ('Some pre=BuildPreI', 'Some post=BuildRetI',
                      'unfold BuildPreI in Pre', 'unfold BuildRetI in Post',
                      'apply V293_tick_shared_internal_resources', 'apply pfalse_rule'):
            self.assertIn(token, src)
        probe = (R / PROBE).read_text()
        for name in ('SNcontract', 'SNsemantics', 'SNall_snapshots_same_spec',
                     'SNfixed_entries', 'SNmissing_hook', 'SNno_EqDom'):
            self.assertRegex(probe, r'Theorem ' + name + r'\s*:')
        self.assertIn('~EqDom CCprogram SNspec', probe)
        self.assertIn('apply HCmissing_no_step', probe)

    def test_stable_compiles_and_recursive_trust(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        roots = []
        for key, p in (('body', PROD), ('probe', PROBE)):
            row = json.loads((D / (stable[key] + '.json')).read_text())
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256((R / p).read_bytes()).hexdigest())
            roots += [Path(p).stem + '.' + n for n in
                      re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', (R / p).read_text(), re.M)]
        trust = json.loads((D / 'trust.json').read_text())
        self.assertTrue(trust['passed'])
        self.assertTrue(trust['recursive'])
        self.assertEqual(len(trust['entry_modules']), 2)
        self.assertEqual(len(roots), 29)
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertEqual([x['exit'] for x in trust['commands']], [0, 0])
        old = json.loads((D.parent / 'stage175-tick-uniform-spec/trust.json').read_text())
        self.assertEqual(set(trust['allowed']), set(old['allowed']))
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
