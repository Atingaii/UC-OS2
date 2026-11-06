"""时间 API 的同不变量组件回归；文本形状不是语义证明。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage177-time-ready-api'
PROD = 'certiucos/v293/proofs/V293TimeReadyAPI.v'
PROBE = 'audit/probes/V293TimeReadyAPIProbe.v'


class TimeReadyAPITests(unittest.TestCase):
    def test_fixed_source_and_old_evidence(self):
        base = json.loads((D / 'baseline.json').read_text())['files']
        for p in ('certiucos/v293/proofs/V293TimeAccess.v',
                  'certiucos/v293/proofs/V293TimeReadyShared.v',
                  'certiucos/v293/proofs/V293TimeGetAPI.v',
                  'certiucos/v293/proofs/V293TimeSharedSet.v',
                  'framework/logic/inferules.v',
                  'audit/logs/stage176-tick-shared-snapshot/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), base[p])

    def test_real_getter_and_setter_preserve_existing_strong_invariant(self):
        src = (R / PROD).read_text()
        for name in ('V293_TimeGet_ready_api_contract', 'V293_TimeSet_ready_api_contract'):
            statement = src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]
            for token in ('Some pre=BuildPreA\'', 'Some post=BuildRetA\'',
                          'V293_time_ready_inv br bg bp bn', 'vl pre post'):
                self.assertIn(token, statement)
            self.assertNotIn('InfRules', statement.split('->')[-2])
        for token in ('apply V293_time_get_absinfer', 'apply V293_time_set_absinfer',
                      'V293_ready_payload br bg bp ts',
                      'apply V293_time_ready_irq_open_asrt',
                      'apply V293_time_ready_irq_close_asrt',
                      'V293_time_copy', 'V293_time_zero', 'inferules.dladd'):
            self.assertIn(token, src)
        self.assertNotIn('V293_time_shared_inv', src)
        self.assertNotRegex(src, r'Definition \w+\b[^.]*:\s*Inv\b')
        self.assertNotIn('CertiOS.audit.', src)
        for p in (PROD, PROBE):
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')

    def test_same_spec_inv_local_resource_not_whole_kernel(self):
        src = (R / PROD).read_text()
        theorem = src.split('Theorem V293_ready_clock_components_checked :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(theorem.count('V293_time_ready_inv br bg bp bn'), 3)
        for token in ('GoodI', 'WFAPI', 'WFIFun', 'no_fun_same',
                      'V293_clock_api_unit version settime gettime', 'let Spec :='):
            self.assertIn(token, theorem)
        for token in ('V293_time_ready_good br bg bp bn',
                      'V293_time_names_footprint', 'V293_OSSchedNew_WFFunEnv'):
            self.assertIn(token, src)
        self.assertNotIn('GOOD_OS', theorem)

    def test_independent_nonempty_core_and_separate_controls(self):
        src = (R / PROBE).read_text()
        for name in ('RAget_builders', 'RAset_builders', 'RAactual_entries',
                     'RAargument_controls', 'RAcore_nonempty', 'RAclock_control',
                     'RAready_control', 'RAget_positive', 'RAget_wrong_return',
                     'RAset_preserves_nonclock_slots'):
            self.assertRegex(src, r'Theorem ' + name + r'\s*:')
        witness = src.split('Theorem RAcore_nonempty :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('TRliteral_spatial', witness)
        self.assertNotIn('api_contract', witness)
        ready = src.split('Theorem RAready_control :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('load Tint32 Mf (150%positive,0%Z)=Some(Vint32 n)', ready)
        self.assertIn('V293_ready_group 32 0=V293_ready_group 16 0', ready)
        self.assertIn('apply TRready_ablation', src)
        self.assertEqual(len(json.loads((D / 'protocol.json').read_text())['controls']), 4)

    def test_stable_compiles_and_recursive_trust(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        roots = []
        for key, p in (('body', PROD), ('probe', PROBE)):
            row = json.loads((D / (stable[key] + '.json')).read_text())
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256((R / p).read_bytes()).hexdigest())
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', (R / p).read_text(), re.M)]
        trust = json.loads((D / 'trust.json').read_text())
        self.assertTrue(trust['passed'])
        self.assertTrue(trust['recursive'])
        self.assertEqual(len(trust['entry_modules']), 2)
        self.assertEqual(len(roots), 25)
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertEqual([x['exit'] for x in trust['commands']], [0, 0])
        old = json.loads((D.parent / 'stage176-tick-shared-snapshot/trust.json').read_text())
        self.assertEqual(set(trust['allowed']), set(old['allowed']))
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
