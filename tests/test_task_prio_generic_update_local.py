"""Static scope/contract tests; semantic checking is --generic-update."""
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage26-task-prio-generic-update'
spec = importlib.util.spec_from_file_location('generic_gate', ROOT / 'scripts/check-v293-task-prio-rekey.py')
GATE = importlib.util.module_from_spec(spec)
spec.loader.exec_module(GATE)
NAME = 'Theorem V293_task_prio_coordinates_update_execution :'


class GenericUpdateLocalTests(unittest.TestCase):
    def setUp(self):
        self.proof = (ROOT / GATE.PROOF).read_text()
        self.header = self.proof.split(NAME, 1)[1].split('Proof.', 1)[0]
        self.entry, self.post = self.header.split('  exists Mg,', 1)
        self.body = self.proof.split(NAME, 1)[1].split('Proof.', 1)[1].split('Qed.', 1)[0]
        self.probe = (ROOT / 'audit/probes/V293TaskPrioGenericUpdateProbe.v').read_text()

    def test_existing_sources_and_protected_inputs_preserved(self):
        base = json.loads((LOG / 'baseline.json').read_text())
        for path, sha in {**base['sources'], **base['protected']}.items():
            if path != GATE.PROOF:
                self.assertEqual(hashlib.sha256((ROOT / path).read_bytes()).hexdigest(), sha, path)
        self.assertTrue((ROOT / GATE.PROOF).read_bytes().startswith((LOG / 'V293TaskPrioRekey.v.before.txt').read_bytes()))

    def test_entry_is_generic_and_not_supplied_coordinate_results(self):
        for token in ['old < 13', 'new < 13', 'old <> new', 'exists v, get M (c,0%Z) = Some (true,v)']:
            self.assertIn(token, self.entry)
        for token in ['cstepstar', 'store ', 'V293_coordinate_memory', 'V293_rekey_locals',
                      'load Tint8 M (bi,0%Z)', 'load Tint8 M (ny,0%Z)',
                      'load Tint8 M (nby,0%Z)', 'load Tint8 M (nbx,0%Z)']:
            self.assertNotIn(token, self.entry)
        self.assertNotIn('8 6', self.header)

    def test_proof_uses_real_coordinates_resource_frame_and_generic_suffix(self):
        for token in ['V293_task_prio_coordinates_execution', 'V293_coordinate_memory M',
                      'assert (CF :', 'assert (LF :', 'assert (NewLoc :',
                      'V293_task_prio_prefix_event_update_preserves P ks ge le Mc',
                      'V293_rekey_sequence_execution']:
            self.assertIn(token, self.body)
        self.assertNotIn('V293_coordinate_fixture_restore', self.body)

    def test_one_output_state_and_correct_expanded_frame(self):
        for token in ['V293_task_prio_coordinates_update table oldprio',
                      'V293_tcb_updated_loads Mh', 'V293_rekey_bitmap_loads Mh',
                      'V293_table_loads V293_tcb_type Mh', 'V293_event_bitmap_loads Mh',
                      'load (Tcom_ptr 411%Z) Mh', 'get Mh (bt,i) = get M (bt,i)',
                      'c <> ny -> c <> bi -> c <> nby -> c <> nbx ->']:
            self.assertIn(token, self.post)

    def test_stale_entry_instantiates_this_generic_interface(self):
        witness = self.proof.split('Theorem V293_generic_coordinate_update_witness :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('V293_task_prio_coordinates_update_execution P ks', witness)
        self.assertIn('V293_coordinate_fixture_mem live elo ehi', witness)
        self.assertIn('apply V293_coordinate_fixture_stale', witness)
        self.assertNotIn('V293_coordinate_fixture_restore', witness)
        self.assertNotIn('V293_tcb_update_frame_witness', witness)
        self.assertNotIn('assert (HNewLoc :', witness)
        self.assertNotIn('assert (HLi :', witness)

    def test_two_static_literal_roots(self):
        self.assertEqual(self.probe.count('Print Assumptions checked_'), 2)
        self.assertIn(':= V293_task_prio_coordinates_update_execution.', self.probe)
        self.assertIn(':= V293_generic_coordinate_update_witness.', self.probe)
        for token in ['V293_tcb_type', 'V293_rekey_locals', 'V293_task_prio_coordinates_update table',
                      'V293_coordinate_memory', 'V293_coordinate_update_observes']:
            self.assertNotIn(token, self.probe)
        self.assertIn('checked_coordinate_all table oldprio', self.probe)

    def test_four_prospective_single_header_ablations(self):
        cases = GATE.mutations(self.proof, generic_update=True)
        self.assertEqual(len(cases), 4)
        for label, (candidate, decl) in cases.items():
            a = self.proof.index(decl)
            b = self.proof.index('Proof.', a)
            c = candidate.index('Proof.', a)
            self.assertEqual(self.proof[:a], candidate[:a], label)
            self.assertEqual(self.proof[b:], candidate[c:], label)
            self.assertNotEqual(self.proof[a:b], candidate[a:c], label)
            self.assertEqual(decl, NAME)

    def test_assumptions_parser_requires_both_actual_prints(self):
        self.assertEqual(GATE.checked_assumptions('Closed under the global context\n' * 2, 2), [])
        for output in ['Closed under the global context\n', 'Axioms:\nInjected : False\n' * 2]:
            with self.assertRaises(ValueError):
                GATE.checked_assumptions(output, 2)


if __name__ == '__main__':
    unittest.main()
