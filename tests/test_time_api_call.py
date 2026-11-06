"""真实调用分配回归；文本门仅核对结构，语义依靠 Coq 与递归检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage179-time-api-call'
PROD = 'certiucos/v293/proofs/V293TimeAPICall.v'
PROBE = 'audit/probes/V293TimeAPICallProbe.v'


class TimeAPICallTests(unittest.TestCase):
    def test_source_and_previous_checkpoint_unchanged(self):
        base = json.loads((D / 'baseline.json').read_text())['files']
        for p in ('certiucos/v293/proofs/V293TimeReadyEntry.v',
                  'audit/probes/V293TimeReadyEntryProbe.v',
                  'certiucos/v293/proofs/V293TimeAccess.v',
                  'framework/logic/inferules.v',
                  'audit/logs/stage178-time-ready-entry/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), base[p])
        source = json.loads((D / 'source-check.json').read_text())
        data = (R / source['actual_file']).read_bytes()
        self.assertEqual(hashlib.sha256(data).hexdigest(), source['file_sha256'])
        for item in source['functions'].values():
            lo, hi = item['lines']
            self.assertEqual(hashlib.sha256(b''.join(data.splitlines(keepends=True)[lo-1:hi])).hexdigest(), item['sha256'])

    def test_real_call_allocation_and_parameter_store(self):
        src = (R / PROD).read_text()
        for name in ('V293_time_parameter_store', 'V293_time_get_call_entry',
                     'V293_time_fresh_after_alloc', 'V293_time_fresh_after_store',
                     'V293_time_set_call_entry'):
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        for token in ('snpcall_step', 'spcall_step', 'svfevalnil_step', 'sfexec_step',
                      'salloclv_step', 'sallocp_step', 'sallocend_step',
                      'store Tint32 (allocb M bt', 'kcall f', 'caller ks'):
            self.assertIn(token, src)
        self.assertNotIn('CertiOS.audit.', src)
        self.assertNotRegex(src, r'Definition \w+\b[^.]*:\s*Inv\b')
        for p in (PROD, PROBE):
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')

    def test_actual_endpoint_matches_builders_and_strong_core(self):
        src = (R / PROBE).read_text()
        for name, pre in (('Cget_actual_call', 'JgetPre ct lg'),
                          ('Cset_actual_call', 'JsetPre ct lg n')):
            statement = src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]
            for token in ("BuildPreA'", "BuildRetA'", 'InfRules RAspec',
                          'TRinv', 'Mf', '** ' + pre, 'b<>160%positive', 'b<>161%positive'):
                self.assertIn(token, statement)
            self.assertNotIn('fresh', statement)
        for name in ('CgetExec', 'CsetExec'):
            definition = src.split('Definition ' + name, 1)[1].split('Theorem', 1)[0]
            self.assertIn('TRmemory ct clock', definition)
            self.assertIn('kcall', definition)
            self.assertIn('caller ks', definition)
            self.assertNotIn('Jmemory', definition)
        self.assertIn('Definition Cprogram := pumerge RAapi RAinternal.', src)

    def test_argument_shadow_and_freshness_controls(self):
        src = (R / PROBE).read_text()
        for name in ('Cfresh', 'Cset_parameter_control', 'Ccaller_shadow_control', 'Cset_two_argument_control'):
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        statement = src.split('Theorem Cset_two_argument_control :', 1)[1].split('Proof.', 1)[0]
        for token in ('CsetExec caller ks ct clock n Mn', 'CsetExec caller ks ct clock bad Mb',
                      'Ccore ** JsetPre ct lg n', 'Ccore ** JsetPre ct lg bad',
                      'load Tint32 Mn (150%positive,0%Z)', 'load Tint32 Mb (150%positive,0%Z)',
                      '~ Jstate', '(LV 1002%Z @ Tint32 |-> Vint32 n) ** Atrue'):
            self.assertIn(token, statement)
        shadow = src.split('Theorem Ccaller_shadow_control :', 1)[1].split('Proof.', 1)[0]
        for token in ('Some(150%positive,Tint32)', 'Some(160%positive,Tint32)', 'CgetExec Ccaller', 'fresh(TRmemory'):
            self.assertIn(token, shadow)
        self.assertIn('V293_time_cell_read', src)
        self.assertEqual(len(json.loads((D / 'protocol.json').read_text())['controls']), 4)

    def test_compilation_identity_and_recursive_trust(self):
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
        self.assertEqual([x['exit'] for x in trust['commands']], [0, 0])
        old = json.loads((D.parent / 'stage178-time-ready-entry/trust.json').read_text())
        self.assertEqual(set(trust['allowed']), set(old['allowed']))
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
