"""真实 builder 连接的结构回归；不替代 Coq 内核检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage174-tick-builder-locals'
PROD = 'certiucos/v293/proofs/V293TimeTickBuilderLocals.v'
PROBE = 'audit/probes/V293TimeTickBuilderLocalsProbe.v'


class TickBuilderLocalsTests(unittest.TestCase):
    def test_fixed_target_and_predecessors(self):
        base = json.loads((D / 'baseline.json').read_text())['files']
        for p in ('certiucos/v293/code/V293OSTimeTick.v',
                  'framework/logic/inferules.v',
                  'certiucos/v293/proofs/V293TimeTickBodyHoare.v',
                  'certiucos/v293/proofs/V293TimeTickHookContract.v',
                  'audit/logs/stage173-tick-body-hoare/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), base[p])

    def test_raw_locals_and_shared_only_hook(self):
        src = (R / PROD).read_text()
        for token in ('Theorem V293_tick_builder_body_hoare :',
                      'caller old scan',
                      'apply V293_time_zero.',
                      'apply V293_tick_hook_call_rule with(good:=good)',
                      '(sseq(V293_tick_body ptcb rows group saved now running head hook)sret)',
                      '(EX scan:val, LV ptcb @(Tptr V293_tcb_type)|->scan)',
                      '(EX old:val, LV saved @Tint32|->old)'):
            self.assertIn(token, src)
        resource = src.split('Definition V293_tick_builder_resource', 1)[1].split('Definition ', 1)[0]
        for token in ('bc', 'bs', 'saved', 'caller', 'Alvarenv', 'LV '):
            self.assertNotIn(token, resource)
        self.assertNotIn('CertiOS.audit.', src)
        for p in (PROD, PROBE):
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')

    def test_same_endpoint_raw_scan_controls(self):
        src = (R / PROBE).read_text()
        allocated = src.split('Theorem BLsame_allocated_controls :', 1)[1].split('Proof.', 1)[0]
        for token in ('BHmemory clock run', 'BLpre clock run',
                      'BLentry Vundef Vundef clock run',
                      '~CCstate(BHmemory clock run)', 'BLentry Vundef(Vptr WhileIdle)clock run'):
            self.assertIn(token, allocated)
        alternate = src.split('Theorem BLarbitrary_scan_nonvacuous :', 1)[1].split('Proof.', 1)[0]
        for token in ('store(Tptr V293_tcb_type)(BHmemory clock run)',
                      'BLentry Vundef(Vptr WhileIdle)clock run',
                      'BLpre clock run', '~CCstate Ms', 'BHentry Vundef clock run'):
            self.assertIn(token, alternate)
        self.assertIn('V293_tick_raw_slot_update', src)
        self.assertIn('V293_tick_raw_pointer_load', src)
        self.assertEqual(len(json.loads((D / 'protocol.json').read_text())['controls']), 4)

    def test_actual_builders_returns_and_hook_limit(self):
        src = (R / PROD).read_text()
        for token in ('Theorem V293_tick_builder_internal_contract :',
                      'Some pre=BuildPreI P f vl lg', 'Some post=BuildRetI P f vl lg',
                      'P f=Some(V293_tick_function', 'unfold BuildPreI in Pre',
                      'unfold BuildRetI in Post', 'apply V293_tick_builder_internal_resources',
                      'Spec hook=Some', '[|result=None|]'):
            self.assertIn(token, src)
        probe = (R / PROBE).read_text()
        for name in ('BLbuilders', 'BLcontract', 'BLsemantics', 'BLwrong_return',
                     'BLstopped_return_nonvacuous', 'BLmissing_hook_still_blocked'):
            self.assertRegex(probe, r'Theorem ' + name + r'\s*:')
        for token in ('run<256 ->run<>1 ->exists Ms', 'BLpost run None',
                      'BLpost run(Some(Vint32 Int.zero))', 'apply HCmissing_no_step'):
            self.assertIn(token, probe)

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
        self.assertEqual(len(roots), 28)
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertEqual([x['exit'] for x in trust['commands']], [0, 0])
        old = json.loads((D.parent / 'stage173-tick-body-hoare/trust.json').read_text())
        self.assertEqual(set(trust['allowed']), set(old['allowed']))
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
