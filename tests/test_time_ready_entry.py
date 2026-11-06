"""联合已分配入口回归；语义证据来自 Coq，文本检查不替代它。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage178-time-ready-entry'
PROD = 'certiucos/v293/proofs/V293TimeReadyEntry.v'
PROBE = 'audit/probes/V293TimeReadyEntryProbe.v'


class TimeReadyEntryTests(unittest.TestCase):
    def test_old_source_and_frozen_evidence_unchanged(self):
        base = json.loads((D / 'baseline.json').read_text())['files']
        for p in ('certiucos/v293/proofs/V293TimeReadyAPI.v',
                  'certiucos/v293/proofs/V293TimeReadyShared.v',
                  'audit/probes/V293TimeReadyAPIProbe.v',
                  'audit/probes/V293TimeReadySharedProbe.v',
                  'framework/logic/inferules.v',
                  'audit/logs/stage177-time-ready-api/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), base[p])
        source = json.loads((D / 'source-check.json').read_text())
        self.assertEqual(hashlib.sha256((R / source['actual_file']).read_bytes()).hexdigest(), source['file_sha256'])

    def test_existing_core_context_and_real_halves(self):
        src = (R / PROD).read_text()
        for name in ('V293_current_entry_context', 'V293_time_ready_entry_context',
                     'V293_time_ready_entry_halves'):
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        statement = src.split('Theorem V293_time_ready_entry_halves :', 1)[1].split('Proof.', 1)[0]
        for token in ('SWINVt (V293_time_ready_inv br bg bp bn) t',
                      'V293_time_ready_core br bg bp bn ** CurTid t'):
            self.assertIn(token, statement)
        self.assertNotIn('CertiOS.audit.', src)
        self.assertNotRegex(src, r'Definition \w+\b[^.]*:\s*Inv\b')
        for p in (PROD, PROBE):
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')

    def test_single_allocated_heap_matches_contract_builders(self):
        src = (R / PROBE).read_text()
        self.assertIn('merge (TRmemory ct clock) (Jlocals tmp save)', src)
        for name, pre in (('Jget_allocated_contract', 'JgetPre ct lg'),
                          ('Jset_allocated_contract', 'JsetPre ct lg n')):
            statement = src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]
            for token in ("BuildPreA'", "BuildRetA'", 'InfRules RAspec',
                          'TRinv', 'Jmemory ct clock', '** ' + pre):
                self.assertIn(token, statement)
            self.assertNotIn('->', statement)
        raw = src.split('Theorem Jraw_joint :', 1)[1].split('Qed.', 1)[0]
        for token in ('Jjoint_join', 'Jlocals_join', 'Jcore_and_current', 'Jlocal', 'Jempty'):
            self.assertIn(token, raw)

    def test_independent_clock_and_setter_slot_controls(self):
        src = (R / PROBE).read_text()
        clock = src.split('Theorem Jclock_control :', 1)[1].split('Proof.', 1)[0]
        for token in ('b<>150%positive', 'JgetPre ct lg ** Atrue',
                      '~ Jstate', 'Jmemory ct bad tmp save'):
            self.assertIn(token, clock)
        setter = src.split('Theorem Jsetter_slot_control :', 1)[1].split('Proof.', 1)[0]
        for token in ('b<>160%positive', 'Jmemory ct clock (Vint32 bad) save',
                      '150%positive,0%Z', 'JsetPre ct lg n ** Atrue'):
            self.assertIn(token, setter)
        for token in ('Jsetter_required_load', 'Jticks_load', 'Jget_caller_any_clock',
                      'Theorem Jraw_getter_control', 'Vundef Vundef'):
            self.assertIn(token, src)
        self.assertEqual(len(json.loads((D / 'protocol.json').read_text())['controls']), 4)

    def test_compiled_sources_and_recursive_trust(self):
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
        self.assertEqual(len(trust['entry_modules']), 2)
        self.assertEqual([x['exit'] for x in trust['commands']], [0, 0])
        old = json.loads((D.parent / 'stage177-time-ready-api/trust.json').read_text())
        self.assertEqual(set(trust['allowed']), set(old['allowed']))
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
