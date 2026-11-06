"""Protocol/identity regressions; semantic credit requires the Coq gate."""
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage26-task-owned-update'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def driver():
    spec = importlib.util.spec_from_file_location('owned_update_gate', ROOT / 'scripts/check-v293-task-owned-update.py')
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class TaskOwnedUpdateTests(unittest.TestCase):
    def test_append_only_and_fixed_registered_sources(self):
        g = driver()
        b = json.loads((LOG / 'baseline.json').read_text())
        before = (LOG / 'Before_Ownership.v.snapshot.txt').read_bytes()
        self.assertEqual(hashlib.sha256(before).hexdigest(), b['sources'][g.SOURCE])
        self.assertEqual(len(before.decode().splitlines()), 227)
        self.assertTrue((ROOT / g.SOURCE).read_bytes().startswith(before))
        self.assertEqual(len(b['sources']), 167)
        self.assertEqual(len(b['protected']), 12)
        for p, h in {**{p: h for p, h in b['sources'].items() if p != g.SOURCE}, **b['protected']}.items():
            self.assertEqual(sha(ROOT / p), h, p)

    def test_single_factor_controls_keep_entire_proof_suffix(self):
        g = driver()
        s = (ROOT / g.SOURCE).read_text()
        negatives = g.controls(s)
        self.assertEqual(set(negatives), {'StaleCellValue', 'StaleTaskPriority'})
        for name, root in [('StaleCellValue', 'Lemma V293_owned_record_cell_update'),
                           ('StaleTaskPriority', 'Theorem V293_owned_task_record_update')]:
            n = negatives[name]
            self.assertEqual(n[n.index('Proof.', n.index(root)):], s[s.index('Proof.', s.index(root)):])
            self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.', n)
            self.assertEqual(n, (LOG / f'gate01/{name}.v.snapshot.txt').read_text())

    def test_nine_actual_checks_and_frozen_inputs(self):
        r = json.loads((LOG / 'gate01/result.json').read_text())
        for key in ['passed', 'inputs_unchanged', 'temporary_tree_removed']:
            self.assertTrue(r[key])
        self.assertEqual(len(r['checks']), 9)
        self.assertEqual(len({c['name'] for c in r['checks']}), 9)
        for c in r['checks']:
            self.assertEqual(c['exit_code'], c['expected_exit_code'])
            if c['name'] in {'StaleCellValue', 'StaleTaskPriority'}:
                self.assertEqual(c['exit_code'], 1)
                self.assertFalse(c['downstream_credit'])
                self.assertTrue(c['entire_target_proof_suffix_unchanged'])
                self.assertGreater(c['error_line'], c['target_proof_line'])
        for p, h in r['inputs'].items():
            self.assertEqual(sha(ROOT / p), h, p)

    def test_assumptions_and_actual_source_snapshots(self):
        g = driver()
        r = json.loads((LOG / 'gate01/result.json').read_text())
        check = g.helper('check-v293-task-prio-rekey.py').checked_assumptions
        self.assertEqual(check((LOG / 'gate01/Positive.log').read_text(), 4), r['positive_assumptions'])
        self.assertEqual(check((LOG / 'gate01/Probe.log').read_text(), 7), r['probe_assumptions'])
        for name, p in [('Production', g.SOURCE), ('Probe', g.PROBE)]:
            self.assertEqual((LOG / f'gate01/{name}.v.snapshot.txt').read_bytes(), (ROOT / p).read_bytes())

    def test_literal_entry_actual_execution_and_stale_semantic_control(self):
        g = driver()
        s = (ROOT / g.PROBE).read_text()
        for token in ['UpdateCellsSpatial', 'UpdateEntrySpatial', 'UpdateEntryPointer', 'UpdateEntryLocals',
                      'UpdateFiveAssignments', 'UpdateLiteralExecution', 'UpdateFinalFrameLoads',
                      'UpdateRejectsStaleOwnership', 'rewrite UpdateFinalPriority in Old']:
            self.assertIn(token, s)
        literal = s[s.index('Definition UpdateFiveAssignments'):s.index('Theorem UpdateLiteralExecution')]
        self.assertEqual(literal.count('sassign'), 5)
        self.assertEqual(s.count('Print Assumptions '), 7)
        production = (ROOT / g.SOURCE).read_text()
        root = production[production.index('Theorem V293_task_prio_tcb_owned_execution'):]
        self.assertNotIn('V293_tcb_update_writable M bt base ->', root[:root.index('Proof.')])
        self.assertEqual(root.count('V293_task_prio_tcb_update_execution'), 1)

    def test_existing_evidence_preserved_without_rebinding(self):
        b = json.loads((LOG / 'baseline.json').read_text())
        self.assertEqual(len(b['history']), 8426)
        for p, h in b['history'].items():
            self.assertEqual(sha(ROOT / p), h, p)
        c = json.loads((LOG / 'old-diagnostic-comparison.json').read_text())
        self.assertEqual(c['removed'], [])
        self.assertEqual(c['previous_diagnostics'], 320)
        self.assertEqual(c['current_diagnostics'], 322)
        self.assertEqual(len(c['added']), 2)


if __name__ == '__main__':
    unittest.main()
