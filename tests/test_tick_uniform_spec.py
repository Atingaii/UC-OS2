"""clock/run 统一规格的结构回归；语义依据由 Coq 与 coqchk 独立检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage175-tick-uniform-spec'
PROD = 'certiucos/v293/proofs/V293TimeTickUniformSpec.v'
PROBE = 'audit/probes/V293TimeTickUniformSpecProbe.v'


class TickUniformSpecTests(unittest.TestCase):
    def test_fixed_source_and_predecessor(self):
        base = json.loads((D / 'baseline.json').read_text())['files']
        for p in ('certiucos/v293/code/V293OSTimeTick.v',
                  'framework/logic/inferules.v',
                  'certiucos/v293/proofs/V293TimeTickBuilderLocals.v',
                  'audit/logs/stage174-tick-builder-locals/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), base[p])

    def test_one_spec_uses_existing_logical_channel(self):
        src = (R / PROD).read_text()
        for name in ('V293_tick_index', 'V293_tick_uniform_fpre',
                     'V293_tick_uniform_fpost', 'V293_tick_uniform_hook_pre',
                     'V293_tick_uniform_hook_post'):
            self.assertRegex(src, r'Definition ' + name + r'\b')
        self.assertIn('(logicl:=lg)', src)
        self.assertIn('eapply call_rule', src)
        self.assertIn('apply V293_tick_uniform_hook_call', src)
        self.assertIn('if Nat.ltb run 256 then', src)
        variables = src.split('Section UniformTick.', 1)[1].split('Definition ', 1)[0]
        self.assertNotRegex(variables, r'\b(?:clock|run)\b')
        self.assertNotIn('CertiOS.audit.', src)
        for p in (PROD, PROBE):
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')

    def test_single_index_controls_on_nonempty_same_endpoint(self):
        src = (R / PROBE).read_text()
        for name in ('Uallocated', 'Uclock_slot', 'Urun_load',
                     'Usame_endpoint_clock_control', 'Usame_endpoint_run_control',
                     'Umalformed_or_out_of_range', 'Usame_stopped_code'):
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        clock = src.split('Theorem Usame_endpoint_clock_control :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(clock.count('BHmemory(Int.repr 37)run'), 2)
        self.assertIn('Ulogic(Int.repr 38)run', clock)
        run = src.split('Theorem Usame_endpoint_run_control :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(run.count('BHmemory clock 0'), 2)
        self.assertIn('Ulogic clock 255', run)
        self.assertIn('PCcode 0=PCcode 255', src)
        self.assertIn('pose proof(Urun_load', src)
        self.assertEqual(len(json.loads((D / 'protocol.json').read_text())['controls']), 4)

    def test_actual_builder_total_contract_not_full_environment(self):
        src = (R / PROD).read_text()
        theorem = src.split('Theorem V293_tick_uniform_internal_contract :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('vl lg pre post', theorem)
        self.assertNotIn('run<256 ->', theorem)
        for token in ('Some pre=BuildPreI', 'Some post=BuildRetI',
                      'unfold BuildPreI in Pre', 'unfold BuildRetI in Post',
                      'apply V293_tick_uniform_internal_resources', 'apply pfalse_rule'):
            self.assertIn(token, src)
        probe = (R / PROBE).read_text()
        for name in ('Ucontract', 'Usemantics', 'Uall_clock_run_same_spec',
                     'Ustopped_post_nonvacuous', 'Ufixed_entries', 'Umissing_hook', 'Uno_EqDom'):
            self.assertRegex(probe, r'Theorem ' + name + r'\s*:')
        self.assertIn('~EqDom CCprogram Uspec', probe)
        self.assertIn('apply HCmissing_no_step', probe)
        self.assertIn('Ustopped_post_nonvacuous', probe)

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
        self.assertEqual(len(roots), 24)
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertEqual([x['exit'] for x in trust['commands']], [0, 0])
        old = json.loads((D.parent / 'stage174-tick-builder-locals/trust.json').read_text())
        self.assertEqual(set(trust['allowed']), set(old['allowed']))
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
