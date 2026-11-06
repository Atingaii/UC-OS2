"""Static scope guards; executable Coq validation is --nonnull-frame."""
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage26-task-prio-nonnull-frame'
spec = importlib.util.spec_from_file_location('nonnull_frame_gate', ROOT / 'scripts/check-v293-task-prio-rekey.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


class NonnullFrameLocalTests(unittest.TestCase):
    def setUp(self):
        self.proof = (ROOT / CHECK.PROOF).read_text()
        self.probe = (ROOT / 'audit/probes/V293TaskPrioNonnullFrameProbe.v').read_text()

    def header(self, name):
        return self.proof.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]

    def test_fixed_source_same_ast_and_append_only(self):
        base = json.loads((LOG / 'baseline.json').read_text())
        self.assertEqual(hashlib.sha256((ROOT / CHECK.CODE).read_bytes()).hexdigest(), base['sources'][CHECK.CODE])
        self.assertTrue((ROOT / CHECK.PROOF).read_bytes().startswith((LOG / 'V293TaskPrioRekey.v.before.txt').read_bytes()))
        self.assertEqual((LOG / 'configured-function-identity.json').read_bytes(),
                         (ROOT / 'audit/logs/stage26-task-prio-null-update/configured-function-identity.json').read_bytes())
        event = json.loads((LOG / 'configured-event-ast.json').read_text())
        self.assertEqual(event['independent_if']['inner'][0]['opcode'], '!=')

    def test_stronger_interface_has_identical_entry_resources(self):
        old = self.header('V293_task_prio_prefix_event_update_execution').split('exists Mg,')[0]
        new = self.header('V293_task_prio_prefix_event_update_preserves').split('exists Mg,')[0]
        self.assertEqual(old, new)
        for token in ['cstepstar', 'store ', 'V293_tcb_updated_loads', ' Mh ', ' Mg ']:
            self.assertNotIn(token, new)

    def test_same_final_state_keeps_all_original_observations_and_internal_fields(self):
        out = self.header('V293_task_prio_prefix_event_update_preserves').split('exists Mg,')[1]
        for token in ['V293_task_prio_prefix_event_update', 'V293_tcb_updated_loads Mh',
                      'V293_table_loads V293_tcb_type Mh', 'V293_rekey_bitmap_loads Mh',
                      'V293_event_bitmap_loads Mh', 'V293_tcb_update_writable Mh bt base',
                      'load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some (Vptr (be,Int.repr ebase))',
                      'get Mh (bt,i) = get M (bt,i)', 'get Mh (c,i) = get M (c,i)']:
            self.assertIn(token, out)
        self.assertIn('(i < base+50)%Z \/ (base+54 < i)%Z', out)

    def test_no_fixture_changes_or_initialization_claim(self):
        tail = self.proof.split('Theorem V293_task_prio_prefix_event_update_preserves :')[1]
        self.assertNotIn('Definition V293_tcb_update_fixture', tail)
        obs = tail.split('Definition V293_tcb_update_frame_observes')[1].split('Theorem ')[0]
        self.assertIn('V293_tcb_update_fixture_mem live elo ehi', obs)
        self.assertIn('load (Tcom_ptr 411%Z) Mh (41%positive,36%Z)', obs)
        self.assertIn('get Mh (41%positive,i)', obs)
        self.assertEqual(self.header('V293_tcb_update_frame_witness').count('->'), 2)

    def test_four_real_boundary_controls(self):
        h = self.header('V293_tcb_update_frame_controls')
        for args in ['false 0 1 16 64 0 1', 'true 0 1 80 64 0 1',
                     'false 16 3 16 80 2 3', 'false 0 129 16 64 128 3']:
            self.assertIn('V293_tcb_update_frame_observes ' + args, h)

    def test_probe_is_static_and_has_three_literal_roots(self):
        for name in ['V293_tcb_type', 'V293_task_prio_prefix_event_update', 'V293_tcb_update_memory',
                     'V293_tcb_updated_loads', 'V293_tcb_update_frame_observes',
                     'V293_tcb_update_fixture_mem', 'V293_rekey_locals']:
            self.assertNotRegex(self.probe, r'\b' + name + r'\b')
        self.assertEqual(self.probe.count('Print Assumptions checked_'), 3)

    def test_four_mutations_change_only_designated_head(self):
        cases = CHECK.mutations(self.proof, nonnull_frame=True)
        self.assertEqual(len(cases), 4)
        for label, (candidate, declaration) in cases.items():
            a = self.proof.index(declaration)
            b = self.proof.index('Proof.', a)
            c = candidate.index('Proof.', a)
            self.assertEqual(candidate[:a], self.proof[:a], label)
            self.assertEqual(candidate[c:], self.proof[b:], label)
            self.assertNotEqual(candidate[a:c], self.proof[a:b], label)

    def test_actual_assumption_parser_rejects_missing_or_extra_axioms(self):
        self.assertEqual(CHECK.checked_assumptions('Closed under the global context\n' * 3, 3), [])
        for value in ['Closed under the global context\n' * 2, 'Axioms:\nInjected : False\n' * 3]:
            with self.assertRaises(ValueError):
                CHECK.checked_assumptions(value, 3)


if __name__ == '__main__':
    unittest.main()
