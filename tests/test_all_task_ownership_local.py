"""Frozen protocol checks; semantic conclusions require the actual Coq gate."""
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage26-all-task-ownership'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def driver():
    spec = importlib.util.spec_from_file_location('all_owned_gate', ROOT / 'scripts/check-v293-all-task-ownership.py')
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class AllTaskOwnershipTests(unittest.TestCase):
    def test_subject_and_original_899_lines_preserved(self):
        g = driver()
        b = json.loads((LOG / 'baseline.json').read_text())
        prefix = (LOG / 'Before_Ownership.v.snapshot.txt').read_bytes()
        self.assertEqual(hashlib.sha256(prefix).hexdigest(), b['sources'][g.SOURCE])
        self.assertEqual(len(prefix.decode().splitlines()), 899)
        self.assertTrue((ROOT / g.SOURCE).read_bytes().startswith(prefix))
        self.assertEqual(len(b['sources']), 167)
        self.assertEqual(len(b['protected']), 12)
        for p, h in {**{p: h for p, h in b['sources'].items() if p != g.SOURCE}, **b['protected']}.items():
            self.assertEqual(sha(ROOT / p), h, p)

    def test_single_factor_controls_keep_entire_proof_suffix(self):
        g = driver()
        s = (ROOT / g.SOURCE).read_text()
        negative = g.controls(s)
        self.assertEqual(set(negative), {'DroppedOtherTaskFrame', 'StaleCanonicalTaskMap'})
        root = 'Theorem V293_critical_wait_all_records_owned_execution'
        for name, n in negative.items():
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
        self.assertEqual(modules['Probe-coqchk'], 'CertiOS.audit.probes.V293AllTaskOwnershipProbe')
        for c in r['checks']:
            self.assertEqual(c['exit_code'], c['expected_exit_code'])
            if c['name'] in {'DroppedOtherTaskFrame', 'StaleCanonicalTaskMap'}:
                self.assertFalse(c['downstream_credit'])
                self.assertTrue(c['entire_proof_suffix_unchanged'])
                self.assertGreater(c['error_line'], c['proof_line'])
        for p, h in r['inputs'].items():
            self.assertEqual(sha(ROOT / p), h, p)
        check = g.helper(g.HELPERS[0]).checked_assumptions
        self.assertEqual(check((LOG / 'gate01/Positive.log').read_text(), 4), r['positive_assumptions'])
        self.assertEqual(check((LOG / 'gate01/Probe.log').read_text(), 4), r['probe_assumptions'])

    def test_one_real_execution_and_full_fragment_transport(self):
        g = driver()
        s = (ROOT / g.SOURCE).read_text()
        header, proof = s[s.index('Theorem V293_critical_wait_all_records_owned_execution'):].split('Proof.', 1)
        self.assertEqual(proof.count('V293_critical_wait_record_owned_execution'), 1)
        self.assertEqual(proof.count('V293_owned_task_records_update'), 1)
        self.assertIn('V293_owned_task_records_block_frame', proof)
        self.assertIn('V293_owned_tasks_fields_reconstruct', proof)
        self.assertIn('fst t <> bt', header)
        self.assertNotIn('NoDup (map fst (TcbMod.lst tasks))', header)
        frame = s[s.index('Theorem V293_owned_task_records_block_frame'):s.index('Lemma V293_owned_tasks_fields_reconstruct')]
        self.assertIn('exists mr. exists remaining', frame)
        self.assertIn('V293_owned_task_list_local', frame)
        self.assertNotIn('V293_owned_task_record_sound', frame)

    def test_literal_combines_actual_entry_resources(self):
        g = driver()
        s = (ROOT / g.PROBE).read_text()
        for token in ['AllFragmentsJoin', 'AllFragmentsSub', 'AllLiteralSpatial', 'AllEntryJoint',
                      'AllOwnedFullReturn', 'AllRejectsOldCanonical', 'AllFinalBothWritable']:
            self.assertIn(token, s)
        self.assertEqual(s.count('V293_critical_wait_all_records_owned_execution'), 1)
        self.assertEqual(s.count('Print Assumptions '), 4)
        for forbidden in ['RecordProbeExecution', 'ApiOwnedFullReturn', 'OwnershipLiteralSpatial']:
            self.assertNotIn(forbidden, s)
        for name, p in [('Production', g.SOURCE), ('Probe', g.PROBE)]:
            self.assertEqual((LOG / f'gate01/{name}.v.snapshot.txt').read_bytes(), (ROOT / p).read_bytes())
        builds = json.loads((LOG / 'fixture-builds.json').read_text())
        self.assertEqual(len(builds), 14)
        self.assertTrue(all(x['exit'] == 0 for x in builds))

    def test_previous_evidence_and_bad_results_unchanged(self):
        b = json.loads((LOG / 'baseline.json').read_text())
        self.assertEqual(len(b['history']), 8746)
        for p, h in b['history'].items():
            self.assertEqual(sha(ROOT / p), h, p)
        self.assertFalse(json.loads((LOG / 'protocol.json').read_text())['controls']['DroppedOtherTaskFrame']['downstream_credit'])
