"""Static checks; actual null-path proof/assumptions gate is --null-update."""
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage26-task-prio-null-update'
spec = importlib.util.spec_from_file_location('null_update_gate', ROOT / 'scripts/check-v293-task-prio-rekey.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


class NullUpdateLocalTests(unittest.TestCase):
    def setUp(self):
        self.proof = (ROOT / CHECK.PROOF).read_text()
        self.probe = (ROOT / 'audit/probes/V293TaskPrioNullUpdateProbe.v').read_text()

    def header(self, name):
        return self.proof.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]

    def test_same_source_and_unchanged_program_ast(self):
        base = json.loads((LOG / 'baseline.json').read_text())
        import hashlib
        self.assertEqual(hashlib.sha256((ROOT / CHECK.CODE).read_bytes()).hexdigest(), base['sources'][CHECK.CODE])
        self.assertEqual((LOG / 'configured-function-identity.json').read_bytes(),
                         (ROOT / 'audit/logs/stage26-task-prio-tcb-update/configured-function-identity.json').read_bytes())
        self.assertTrue(json.loads((LOG / 'source-identity.json').read_text())['source_hashes_match_frozen'])
        event = json.loads((LOG / 'configured-event-ast.json').read_text())
        self.assertEqual(event['read_field']['name'], 'OSTCBEventPtr')
        condition = event['independent_if']['inner'][0]
        self.assertEqual(condition['kind'], 'BinaryOperator')
        self.assertEqual(condition['opcode'], '!=')

    def test_old_proof_prefix_is_byte_identical(self):
        self.assertTrue((ROOT / CHECK.PROOF).read_bytes().startswith((LOG / 'V293TaskPrioRekey.v.before.txt').read_bytes()))

    def test_entry_resources_are_not_suffix_execution_or_poststate_oracles(self):
        entry, out = self.header('V293_task_prio_prefix_null_update_execution').split('exists Me,', 1)
        for token in ['cstepstar', 'store ', 'evalval', 'V293_tcb_updated_loads', ' Mh ', ' Me ']:
            self.assertNotIn(token, entry)
        self.assertIn('load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some Vnull', entry)
        self.assertIn('V293_tcb_update_writable M bt base', entry)
        self.assertNotIn('V293_event_bitmap_writable', entry)
        self.assertIn('V293_task_prio_prefix_event_update', out)

    def test_final_same_memory_observes_five_fields_table_ready_and_null_event(self):
        out = self.header('V293_task_prio_prefix_null_update_execution').split('exists Me,', 1)[1]
        for token in ['V293_tcb_updated_loads Mh', 'V293_table_loads V293_tcb_type Mh',
                      'V293_rekey_bitmap_loads Mh', 'load (Tptr V293_event_type) Mh (bp,0%Z) = Some Vnull',
                      'load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some Vnull',
                      'get Mh (bt,i) = get M (bt,i)', 'get Mh (c,i) = get M (c,i)']:
            self.assertIn(token, out)

    def test_single_entry_field_change_and_real_witness(self):
        delta = self.header('V293_null_update_entry_delta')
        self.assertIn('c <> 41%positive \/ (i < 36)%Z \/ (40 <= i)%Z', delta)
        self.assertEqual(self.header('V293_null_update_continuous_witness').count('->'), 2)
        controls = self.header('V293_null_update_branch_controls')
        for token in ['V293_null_update_observes false 0 1 16',
                      'V293_null_update_observes true 0 1 80',
                      'V293_tcb_update_observes false 0 1 16 64 0 1']:
            self.assertIn(token, controls)
        obs = self.proof.split('Definition V293_null_update_observes', 1)[1].split('Theorem ', 1)[0]
        self.assertIn('cstepstar', obs)
        self.assertIn('forall i, get Mh (72%positive,i)', obs)

    def test_literal_probe_does_not_alias_candidate_new_definitions(self):
        for token in ['V293_tcb_type', 'V293_task_prio_prefix_event_update', 'V293_tcb_update_memory',
                      'V293_tcb_updated_loads', 'V293_null_update_fixture_mem', 'V293_null_update_observes',
                      'V293_tcb_update_fixture_mem', 'V293_tcb_update_fixture_le', 'V293_rekey_locals']:
            self.assertNotRegex(self.probe, r'\b' + token + r'\b')
        for name in ['checked_null_continuous', 'checked_null_mem', 'checked_null_observes',
                     'checked_null_witness', 'checked_null_delta', 'checked_null_controls']:
            self.assertIn('Definition ' + name, self.probe)

    def test_four_single_header_mutations_keep_complete_proof_suffix(self):
        cases = CHECK.mutations(self.proof, null_update=True)
        self.assertEqual(len(cases), 4)
        for label, (candidate, declaration) in cases.items():
            a = self.proof.index(declaration)
            b = self.proof.index('Proof.', a)
            c = candidate.index('Proof.', a)
            self.assertEqual(self.proof[:a], candidate[:a], label)
            self.assertEqual(self.proof[b:], candidate[c:], label)
            self.assertNotEqual(self.proof[a:b], candidate[a:c], label)

    def test_four_actual_assumption_outputs_and_unknown_axiom_rejection(self):
        self.assertEqual(self.probe.count('Print Assumptions checked_null_'), 4)
        self.assertEqual(CHECK.checked_assumptions('Closed under the global context\n' * 4, 4), [])
        for value in ['Closed under the global context\n' * 3, 'Axioms:\nInjected : False\n' * 4]:
            with self.assertRaises(ValueError):
                CHECK.checked_assumptions(value, 4)


if __name__ == '__main__':
    unittest.main()
