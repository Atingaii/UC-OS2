"""Static checks only; actual Coq execution gate is --event-prefix."""
import importlib.util
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('event_prefix_check', ROOT/'scripts/check-v293-task-prio-rekey.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


class EventPrefixLocalTests(unittest.TestCase):
    def setUp(self):
        self.proof = (ROOT/CHECK.PROOF).read_text()
        self.probe = (ROOT/'audit/probes/V293TaskPrioEventPrefixProbe.v').read_text()

    def header(self, name):
        return re.split(r'(?:Theorem|Lemma) '+name+r' :', self.proof, maxsplit=1)[1].split('Proof.', 1)[0]

    def test_same_frozen_function_relocated(self):
        d = ROOT/'audit/logs/stage26-task-prio-event-prefix'
        identity = json.loads((d/'source-identity.json').read_text())
        self.assertTrue(identity['function_record_matches_frozen'])
        self.assertEqual((d/'configured-function-identity.json').read_bytes(),
                         (ROOT/'audit/logs/stage26-task-prio-event-body/configured-function-identity.json').read_bytes())

    def test_continuous_execution_no_suffix_oracle(self):
        h = self.header('V293_task_prio_prefix_event_nonnull_execution')
        entry, out = h.split('exists M1 M2 Me,', 1)
        for oracle in ['store ', 'cstepstar', 'evalval', 'Mf', 'Me', 'Mg']:
            self.assertNotIn(oracle, entry)
        self.assertIn('V293_event_bitmap_writable M be ebase', entry)
        self.assertIn('be <> br -> be <> bg ->', entry)
        self.assertIn('V293_task_prio_prefix_event table', out)
        self.assertIn('(ge,le,Mg)', out)
        for observable in ['V293_rekey_bitmap_loads Mg', 'V293_table_loads V293_tcb_type Mg',
                           'V293_event_bitmap_loads Mg', 'V293_rekey_locals ge le Mg',
                           'load (Tptr V293_event_type) Mg', 'get Mg (c,i) = get M (c,i)']:
            self.assertIn(observable, out)

    def test_witness_has_only_byte_bounds_and_literal_memory(self):
        h = self.header('V293_prefix_event_nonnull_execution_witness')
        self.assertEqual(h.count('->'), 2)
        self.assertNotIn('cstepstar', h.split('V293_prefix_event_nonnull_observes', 1)[0])
        obs = self.proof.split('Definition V293_prefix_event_nonnull_observes', 1)[1].split('Theorem ', 1)[0]
        self.assertIn('cstepstar', obs)
        self.assertIn('V293_prefix_event_nonnull_mem live elo ehi', obs)
        self.assertIn('Some Vnull', obs)
        self.assertIn('Some (Vptr (41%positive,Int.repr 8))', obs)
        controls = self.header('V293_prefix_event_nonnull_controls')
        for case in ['false 0 1 16 64 0 1', 'true 0 1 80 64 0 1',
                     'false 16 3 16 80 2 3', 'false 0 129 16 64 128 3']:
            self.assertIn(case, controls)

    def test_static_probe_has_no_candidate_type_program_or_fixture_aliases(self):
        for alias in ['V293_tcb_type', 'V293_task_prio_prefix_event', 'V293_event_type',
                      'V293_event_rekey_memory', 'V293_prefix_event_nonnull_mem',
                      'V293_prefix_event_nonnull_observes', 'V293_rekey_locals', 'V293_table_loads']:
            self.assertNotRegex(self.probe, r'\b'+alias+r'\b')
        for definition in ['checked_full', 'checked_full_mem', 'checked_continuous', 'checked_observes']:
            self.assertIn('Definition '+definition, self.probe)

    def test_four_single_header_controls_preserve_entire_proof_suffix(self):
        cases = CHECK.mutations(self.proof, event_prefix=True)
        self.assertEqual(len(cases), 4)
        for label, (candidate, declaration) in cases.items():
            a = self.proof.index(declaration)
            b = self.proof.index('Proof.', a)
            c = candidate.index('Proof.', a)
            self.assertEqual(self.proof[:a], candidate[:a], label)
            self.assertEqual(self.proof[b:], candidate[c:], label)
            self.assertNotEqual(self.proof[a:b], candidate[a:c], label)

    def test_actual_three_assumption_outputs_and_unknown_axiom_rejected(self):
        self.assertEqual(self.probe.count('Print Assumptions checked_'), 3)
        self.assertEqual(CHECK.checked_assumptions('Closed under the global context\n'*3, 3), [])
        for output in ['Closed under the global context\n'*2, 'Axioms:\nInjected : False\n'*3]:
            with self.assertRaises(ValueError):
                CHECK.checked_assumptions(output, 3)


if __name__ == '__main__':
    unittest.main()
