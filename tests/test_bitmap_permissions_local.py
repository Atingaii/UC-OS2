"""Protocol regressions supplement, not replace, the actual Coq checks."""
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage26-bitmap-permissions'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def driver():
    spec = importlib.util.spec_from_file_location('bitmap_owned_gate', ROOT / 'scripts/check-v293-bitmap-permissions.py')
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class BitmapPermissionsTests(unittest.TestCase):
    def test_subject_and_original_1528_lines_preserved(self):
        g = driver()
        b = json.loads((LOG / 'baseline.json').read_text())
        prefix = (LOG / 'Before_Ownership.v.snapshot.txt').read_bytes()
        self.assertEqual(hashlib.sha256(prefix).hexdigest(), b['sources'][g.SOURCE])
        self.assertEqual(len(prefix.decode().splitlines()), 1528)
        self.assertTrue((ROOT / g.SOURCE).read_bytes().startswith(prefix))
        self.assertEqual(len(b['sources']), 167)
        self.assertEqual(len(b['protected']), 12)
        for p, h in {**{p: h for p, h in b['sources'].items() if p != g.SOURCE}, **b['protected']}.items():
            self.assertEqual(sha(ROOT / p), h, p)

    def test_single_factor_controls_keep_entire_proof_suffix(self):
        g = driver()
        s = (ROOT / g.SOURCE).read_text()
        negative = g.controls(s)
        self.assertEqual(set(negative), {'FreedLocalsRetained', 'ReadOnlyCreatesOwnership'})
        for name, n in negative.items():
            root = g.CONTROL_ROOTS[name]
            self.assertEqual(n[n.index('Proof.', n.index(root)):], s[s.index('Proof.', s.index(root)):])
            self.assertEqual(n, (LOG / f'gate01/{name}.v.snapshot.txt').read_text())
            self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.', n)

    def test_eight_actual_checks_and_fixed_assumptions(self):
        g = driver()
        r = json.loads((LOG / 'gate01/result.json').read_text())
        for key in ['passed', 'inputs_unchanged', 'temporary_tree_removed']:
            self.assertTrue(r[key])
        self.assertEqual(len(r['checks']), 8)
        modules = {c['name']: c['command'][-1] for c in r['checks'] if c['name'].endswith('-coqchk')}
        self.assertEqual(modules['Probe-coqchk'], 'CertiOS.audit.probes.V293BitmapOwnershipProbe')
        self.assertEqual(modules['Production-coqchk'], 'CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership')
        self.assertEqual(modules['Positive-coqchk'], 'BitmapOwnedGate.Positive')
        for c in r['checks']:
            self.assertEqual(c['exit_code'], c['expected_exit_code'])
            if c['name'] in {'FreedLocalsRetained', 'ReadOnlyCreatesOwnership'}:
                self.assertFalse(c['downstream_credit'])
                self.assertTrue(c['entire_proof_suffix_unchanged'])
                self.assertGreater(c['error_line'], c['proof_line'])
        for p, h in r['inputs'].items():
            self.assertEqual(sha(ROOT / p), h, p)
        check = g.helper(g.HELPERS[0]).checked_assumptions
        self.assertEqual(check((LOG / 'gate01/Positive.log').read_text(), 4), r['positive_assumptions'])
        self.assertEqual(check((LOG / 'gate01/Probe.log').read_text(), 6), r['probe_assumptions'])

    def test_same_execution_and_no_ownership_from_read_alone(self):
        g = driver()
        s = (ROOT / g.SOURCE).read_text()
        a = s.index('Theorem V293_critical_event_return_bitmap_owned')
        b = s.index('Qed.', a) + len('Qed.')
        header, proof = s[a:b].split('Proof.', 1)
        self.assertEqual(proof.count('V293_critical_event_update_execution_writable_event_frame'), 1)
        self.assertEqual(proof.count('V293_success_tail_return_execution'), 1)
        self.assertNotIn('V293_critical_event_return_tcb_owned_block', proof)
        for text in ['UpdateWritable', 'FreeFrame', 'Surviving', 'V293_full_byte_cells_owned']:
            self.assertIn(text, proof)
        self.assertIn('~ In c (map fst (getaddr le)) ->', header)
        self.assertIn('V293_bitmap_layout', header)
        helper = s[s.index('Lemma V293_full_byte_cells_owned'):s.index('Definition V293_bitmap_layout')]
        self.assertIn('NoDup (map fst cells)', helper)
        self.assertIn('map_join_get_sig', helper)
        self.assertIn('Some (true,raw)', helper)

    def test_literal_actual_return_and_consumers(self):
        g = driver()
        s = (ROOT / g.PROBE).read_text()
        for name in g.PROBE_ROOTS:
            self.assertIn('Theorem ' + name, s)
        self.assertEqual(s.count('V293_critical_event_return_bitmap_owned'), 1)
        self.assertEqual(s.count('Print Assumptions '), 6)
        for forbidden in ['JointOwnedFullReturn', 'AllOwnedFullReturn', 'ApiOwnedFullReturn',
                          'RecordProbeExecution', 'OwnershipProbeExecution']:
            self.assertNotIn(forbidden, s)
        for text in ['30%positive 31%positive 72%positive 5%Z 16 0 64 0',
                     'V293_owned_cells_byte_update', 'V293_bytes_writable Mf 50%positive 24%Z 4',
                     'V293_bytes_writable Mf 50%positive 32%Z 4', 'Some (false,', 'get Mf (51%positive,0%Z) = None']:
            # The half-permission literal uses a direct singleton constructor.
            if text == 'Some (false,':
                self.assertIn('(false,Byte (Byte.repr 16))', s)
            else:
                self.assertIn(text, s)
        for name, p in [('Production', g.SOURCE), ('Probe', g.PROBE)]:
            self.assertEqual((LOG / f'gate01/{name}.v.snapshot.txt').read_bytes(), (ROOT / p).read_bytes())
        builds = json.loads((LOG / 'fixture-builds.json').read_text())
        self.assertEqual(len(builds), 16)
        self.assertTrue(all(x['exit'] == 0 for x in builds))

    def test_historical_evidence_and_cache_paths_retained(self):
        b = json.loads((LOG / 'baseline.json').read_text())
        self.assertEqual(len(b['history']), 8914)
        for p, h in b['history'].items():
            self.assertEqual(sha(ROOT / p), h, p)
        for p in b['caches']:
            self.assertTrue((ROOT / p).exists(), p)
        protocol = json.loads((LOG / 'protocol.json').read_text())
        for control in protocol['controls'].values():
            self.assertFalse(control['downstream_credit'])
