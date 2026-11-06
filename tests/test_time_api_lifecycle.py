"""原时间 API 有限生命周期回归；文本检查不替代 Coq 语义证明。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage180-time-api-lifecycle'
PROD = 'certiucos/v293/proofs/V293TimeAPILifecycle.v'
PROBE = 'audit/probes/V293TimeAPILifecycleProbe.v'


class TimeAPILifecycleTests(unittest.TestCase):
    def test_source_and_prior_inputs_unchanged(self):
        base = json.loads((D / 'baseline.json').read_text())['files']
        for p in ('certiucos/v293/proofs/V293TimeAccess.v',
                  'certiucos/v293/proofs/V293TimeAPICall.v',
                  'audit/probes/V293TimeAPICallProbe.v', 'framework/logic/inferules.v',
                  'audit/logs/stage179-time-api-call/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), base[p])
        source = json.loads((D / 'source-check.json').read_text())
        data = (R / source['actual_file']).read_bytes()
        self.assertEqual(hashlib.sha256(data).hexdigest(), source['file_sha256'])
        for row in source['functions'].values():
            lo, hi = row['lines']
            self.assertEqual(hashlib.sha256(b''.join(data.splitlines(keepends=True)[lo-1:hi])).hexdigest(), row['sha256'])

    def test_owned_store_original_body_and_real_return(self):
        src = (R / PROD).read_text()
        for name in ('V293_time_cell_store', 'V293_time_local_layout', 'V293_time_locals_return',
                     'V293_time_body_prefix', 'V293_time_get_body_return', 'V293_time_set_body_return'):
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        for token in ('V293_tick_raw_slot_update', 'V293_tick_raw_owned_writable',
                      'V293_evaluated_return_execution', 'V293_tick_void_return',
                      'apply encrit_step', 'apply excrit_step', 'V293_time_cell_read',
                      'V293_time_call_locals', 'caller,Mf', 'get Mf(bt,Z.of_nat k)=None'):
            self.assertIn(token, src)
        for name in ('V293_time_get_body_return', 'V293_time_set_body_return'):
            stmt = src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]
            self.assertNotIn('evalval', stmt)
            self.assertNotIn('free', stmt)
            self.assertIn('exists Mz Mc Mf', stmt)
            self.assertIn('(enabled,si,ci)', stmt)
        self.assertNotIn('CertiOS.audit.', src)
        for p in (PROD, PROBE):
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')

    def test_same_actual_call_endpoint_continues_to_return(self):
        src = (R / PROBE).read_text()
        for name in ('Lget_actual_lifecycle', 'Lset_actual_lifecycle'):
            stmt = src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]
            self.assertIn('Ccore ** J', stmt)
            self.assertIn('Ma', stmt)
            self.assertIn('Mf', stmt)
            self.assertIn('get Mf(160%positive,Z.of_nat k)=None', stmt)
            self.assertIn('get Mf(161%positive,Z.of_nat k)=None', stmt)
        for name, fn in (('LgetExec', '203%Z []'), ('LsetExec', '202%Z [econst32 n]')):
            stmt = src.split('Definition ' + name, 1)[1].split('.', 1)[0]
            self.assertIn('scall ' + fn, stmt)
            self.assertIn('TRmemory ct clock', stmt)
            self.assertIn('((JGE,caller,Mf),empisr,(true,[],[]))', stmt)
            self.assertNotIn('Jmemory', stmt)
        self.assertIn('exact Call | exact Body', src)
        self.assertIn('V293_time_get_call_entry Cprogram', src)
        self.assertIn('V293_time_set_call_entry Cprogram', src)

    def test_argument_and_restored_shadow_controls(self):
        src = (R / PROBE).read_text()
        stmt = src.split('Theorem Lset_two_argument_control :', 1)[1].split('Proof.', 1)[0]
        for token in ('LsetExec caller ks ct clock n Mn', 'LsetExec caller ks ct clock bad Mb',
                      'load Tint32 An(160%positive,0%Z)=Some(Vint32 n)',
                      'load Tint32 Ab(160%positive,0%Z)=Some(Vint32 bad)',
                      'load Tint32 Mn(150%positive,0%Z)=Some(Vint32 n)',
                      'load Tint32 Mb(150%positive,0%Z)=Some(Vint32 bad)',
                      'load Tint32 Mb(150%positive,0%Z)<>Some(Vint32 n)'):
            self.assertIn(token, stmt)
        self.assertNotIn('Jstate', stmt)
        shadow = src.split('Theorem Lget_caller_shadow_control :', 1)[1].split('Proof.', 1)[0]
        for token in ('LgetExec Ccaller', 'Some(150%positive,Tint32)', 'Some(160%positive,Tint32)',
                      'evalval(evar 1002%Z)(JGE,Ccaller,Mf)=Some(Vint32 clock)'):
            self.assertIn(token, shadow)
        self.assertEqual(len(json.loads((D / 'protocol.json').read_text())['controls']), 4)

    def test_stable_compilation_and_recursive_trust(self):
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
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertEqual([r['exit'] for r in trust['commands']], [0, 0])
        old = json.loads((D.parent / 'stage179-time-api-call/trust.json').read_text())
        self.assertEqual(set(trust['allowed']), set(old['allowed']))
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
