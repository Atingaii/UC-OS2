"""Evidence/protocol checks; semantic credit requires actual Coq checks."""
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage26-api-task-ownership'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def driver():
    spec = importlib.util.spec_from_file_location('api_owned_gate', ROOT / 'scripts/check-v293-api-task-ownership.py')
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class ApiTaskOwnershipTests(unittest.TestCase):
    def test_fixed_subject_append_only(self):
        g = driver()
        b = json.loads((LOG / 'baseline.json').read_text())
        prefix = (LOG / 'Before_Ownership.v.snapshot.txt').read_bytes()
        self.assertEqual(hashlib.sha256(prefix).hexdigest(), b['sources'][g.SOURCE])
        self.assertEqual(len(prefix.decode().splitlines()), 422)
        self.assertTrue((ROOT / g.SOURCE).read_bytes().startswith(prefix))
        self.assertEqual(len(b['sources']), 167)
        self.assertEqual(len(b['protected']), 12)
        for p, h in {**{p: h for p, h in b['sources'].items() if p != g.SOURCE}, **b['protected']}.items():
            self.assertEqual(sha(ROOT / p), h, p)

    def test_controls_change_one_header_and_preserve_entire_suffix(self):
        g = driver()
        s = (ROOT / g.SOURCE).read_text()
        negatives = g.controls(s)
        self.assertEqual(set(negatives), {'DroppedPermissionFrame', 'StaleReturnedPriority'})
        for name, root in [('DroppedPermissionFrame', 'Theorem V293_owned_task_record_block_frame'),
                           ('StaleReturnedPriority', 'Theorem V293_critical_wait_record_owned_execution')]:
            n = negatives[name]
            self.assertEqual(n[n.index('Proof.', n.index(root)):], s[s.index('Proof.', s.index(root)):])
            self.assertEqual(n, (LOG / f'gate01/{name}.v.snapshot.txt').read_text())
            self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.', n)

    def test_eight_actual_checks_frozen_inputs_and_assumptions(self):
        g = driver()
        r = json.loads((LOG / 'gate01/result.json').read_text())
        for key in ['passed', 'inputs_unchanged', 'temporary_tree_removed']:
            self.assertTrue(r[key])
        self.assertEqual(len(r['checks']), 8)
        self.assertEqual(len({c['name'] for c in r['checks']}), 8)
        for c in r['checks']:
            self.assertEqual(c['exit_code'], c['expected_exit_code'])
            if c['name'] in {'DroppedPermissionFrame', 'StaleReturnedPriority'}:
                self.assertEqual(c['exit_code'], 1)
                self.assertFalse(c['downstream_credit'])
                self.assertTrue(c['entire_proof_suffix_unchanged'])
                self.assertGreater(c['error_line'], c['proof_line'])
        for p, h in r['inputs'].items():
            self.assertEqual(sha(ROOT / p), h, p)
        check = g.helper(g.HELPERS[0]).checked_assumptions
        self.assertEqual(check((LOG / 'gate01/Positive.log').read_text(), 4), r['positive_assumptions'])
        self.assertEqual(check((LOG / 'gate01/Probe.log').read_text(), 5), r['probe_assumptions'])

    def test_same_return_memory_not_assumed_execution(self):
        g = driver()
        s = (ROOT / g.SOURCE).read_text()
        root = s[s.index('Theorem V293_critical_wait_record_owned_execution'):]
        header, proof = root.split('Proof.', 1)
        self.assertNotIn('V293_tcb_update_writable M bt base ->', header)
        self.assertEqual(proof.count('V293_critical_event_return_tcb_owned_block'), 1)
        self.assertEqual(proof.count('V293_wait_prio_owned_step'), 1)
        self.assertIn('exact ExactBlock', proof)
        self.assertIn('V293_owned_task_fields_reconstruct', proof)
        lower = s[s.index('Theorem V293_critical_event_return_tcb_owned_block'):s.index('Lemma V293_owned_cells_block_local')]
        self.assertEqual(lower.count('V293_success_tail_return_execution'), 1)
        self.assertIn('V293_critical_event_update_execution_writable_event_frame', lower)

    def test_literal_entry_and_same_final_semantic_controls(self):
        g = driver()
        s = (ROOT / g.PROBE).read_text()
        for token in ['ApiRecordSub', 'ApiEntryJoint', 'ApiOwnedFullReturn', 'ApiRejectsOldPriority',
                      'ApiFinalWritePermission', 'ApiPermissionMatters', 'rewrite Actual in Old']:
            self.assertIn(token, s)
        self.assertNotIn('RecordProbeExecution', s)
        self.assertEqual(s.count('V293_critical_wait_record_owned_execution'), 1)
        self.assertEqual(s.count('Print Assumptions '), 5)
        for name, p in [('Production', g.SOURCE), ('Probe', g.PROBE)]:
            self.assertEqual((LOG / f'gate01/{name}.v.snapshot.txt').read_bytes(), (ROOT / p).read_bytes())
        builds = json.loads((LOG / 'fixture-builds.json').read_text())
        self.assertEqual(len(builds), 13)
        self.assertTrue(all(x['exit'] == 0 for x in builds))

    def test_prior_evidence_and_actual_failure_diagnostics_retained(self):
        b = json.loads((LOG / 'baseline.json').read_text())
        self.assertEqual(len(b['history']), 8547)
        for p, h in b['history'].items():
            self.assertEqual(sha(ROOT / p), h, p)
        c = json.loads((LOG / 'old-diagnostic-comparison.json').read_text())
        self.assertEqual(c['removed'], [])
        self.assertEqual(c['previous_diagnostics'], 322)
        self.assertEqual(c['current_diagnostics'], 325)
        self.assertEqual(len(c['added']), 3)


if __name__ == '__main__':
    unittest.main()
