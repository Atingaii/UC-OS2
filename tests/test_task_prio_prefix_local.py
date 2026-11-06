"""Structural companions, not substitutes for actual Coq/kernel checking."""
import importlib.util
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('prefix_local_check', ROOT / 'scripts/check-v293-task-prio-rekey.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


class TaskPrioPrefixTests(unittest.TestCase):
    def setUp(self):
        self.code = (ROOT / CHECK.CODE).read_text()
        self.proof = (ROOT / CHECK.PROOF).read_text()
        self.probe = (ROOT / 'audit/probes/V293TaskPrioPrefixProbe.v').read_text()

    def header(self, name):
        return self.proof.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]

    def test_real_order_and_same_middle_final_memories(self):
        code = self.code.split('Definition V293_task_prio_prefix', 1)[1]
        self.assertIn('sseq (V293_task_prio_rekey table oldprio newprio ptcb)', code)
        self.assertIn('(V293_task_prio_read_ready ptcb rows group yo yn xo xn byo byn)', code)
        h = self.header('V293_task_prio_prefix_execution')
        entry, output = h.split('exists M1 M2,', 1)
        for oracle in ['cstepstar', 'evalval', 'store ', 'M1', 'M2', 'Mr', 'Mf']:
            self.assertNotIn(oracle, entry)
        self.assertIn('V293_tcb_read_memory M2', output)
        self.assertIn('V293_ready_branch_memory Mr', output)
        self.assertIn('(ge,le,Mr)', output)
        self.assertIn('(ge,le,Mf)', output)
        self.assertIn('TableFinalFrame', self.proof)

    def test_preserves_full_thirteen_slot_view_at_final_not_only_after_table_writes(self):
        h = self.header('V293_task_prio_prefix_execution')
        self.assertIn('length entries = 13 -> V293_table_loads V293_tcb_type M b entries', h)
        self.assertIn('V293_table_loads V293_tcb_type Mf b', h)
        self.assertIn('load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat old)%Z) = Some Vnull', h)
        self.assertIn('load (Tptr V293_tcb_type) Mf (b,(4*Z.of_nat new)%Z) = Some (Vptr', h)
        self.assertIn('forall p, p < 13 -> load (Tptr tp)', self.probe)

    def test_separation_covers_table_fields_locals_and_bitmap(self):
        entry = self.header('V293_task_prio_prefix_execution').split('exists M1 M2,', 1)[0]
        for block in ['bo', 'bn', 'bc', 'bt', 'dy', 'dby', 'dx', 'br', 'bg']:
            self.assertIn('b <> ' + block + ' ->', entry)
        self.assertIn('-> c <> b /\\ c <> dy /\\ c <> dby /\\ c <> dx)', entry)
        self.assertIn('V293_rekey_new_bindings yn xn byn new', entry)
        self.assertNotIn('V293_rekey_ready_bindings', entry)

    def test_same_concrete_entry_contains_table_and_all_suffix_resources(self):
        table = self.header('V293_prefix_fixture_table_entry')
        body = self.header('V293_prefix_fixture_body_entry')
        self.assertIn('(V293_prefix_fixture_mem live)', table)
        self.assertEqual(table.count('V293_bytes_writable'), 2)
        self.assertIn('let M := V293_prefix_fixture_mem live', body)
        for resource in ['load (Tptr V293_tcb_type)', 'V293_tcb_old_loads',
                         'V293_rekey_bitmap_loads', 'V293_rekey_bitmap_writable', 'V293_rekey_new_bindings']:
            self.assertIn(resource, body)
        self.assertEqual(body.count('(exists v, get M'), 3)
        literal = self.probe.split('Definition checked_entries', 1)[1].split('Definition checked_prefix_ge', 1)[0]
        self.assertEqual(literal.count('Vnull'), 11)
        self.assertEqual(literal.count('Vptr'), 2)

    def test_combined_task_table_bitmap_relations_and_actual_execution_share_entry(self):
        h = self.header('V293_prefix_combined_witness')
        for resource in ['let M := V293_prefix_fixture_mem live', 'V293_table_loads V293_tcb_type M',
                         'V293_priority_table', 'V293_bitmap_tasks', 'get tasks',
                         'nth 6 V293_prefix_fixture_entries Vnull = Vnull', 'V293_prefix_observes live live']:
            self.assertIn(resource, h)
        self.assertNotIn(' ->', h)
        controls = self.header('V293_prefix_physical_controls')
        self.assertIn('true true 80 0 1 Vnull', controls)
        self.assertIn('false false 16 0 1 Vnull', controls)
        obs = self.probe.split('Definition checked_observes', 1)[1].split('Definition checked_execution', 1)[0]
        self.assertEqual(obs.count('store (Tptr checked_tcb)'), 2)
        self.assertIn('cstepstar', obs)
        self.assertIn('checked_table_loads checked_tcb Mf', obs)
        # Across these controls both the ready bit and its group summary change;
        # the abstract status changes too. They are not a single-factor ablation.
        self.assertIn('(if live then rdy else wait os_stat_time Int.one)', self.probe)

    def test_expected_program_memory_and_relations_are_literal_not_candidate_aliases(self):
        for alias in ['V293_task_prio_prefix', 'V293_task_prio_read_ready', 'V293_task_prio_ready_test',
                      'V293_ready_branch_memory', 'V293_tcb_read_memory', 'V293_tcb_type',
                      'V293_prefix_fixture_mem', 'V293_prefix_fixture_entries', 'V293_prefix_fixture_tasks',
                      'V293_fixture_put_table', 'V293_fixture_put_bytes', 'V293_priority_table',
                      'V293_bitmap_tasks', 'V293_ready_group', 'V293_bitmap_ready']:
            self.assertNotRegex(self.probe, r'\b' + re.escape(alias) + r'\b')
        self.assertIn('sseq (sseq (sassign (earrayelem (evar table) (evar oldprio)) enull)', self.probe)
        self.assertIn('Fixpoint checked_put_table', self.probe)
        self.assertIn('Fixpoint checked_put_bytes', self.probe)
        self.assertIn('Definition checked_priority_table', self.probe)
        self.assertIn('Nat.testbit hi (p-8)', self.probe)

    def test_four_prospective_single_header_controls_keep_complete_proof_suffix(self):
        cases = CHECK.mutations(self.proof, prefix=True)
        self.assertEqual(len(cases), 4)
        for label, (candidate, declaration) in cases.items():
            with self.subTest(label=label):
                start = self.proof.index(declaration)
                end = self.proof.index('Proof.', start)
                new_end = candidate.index('Proof.', start)
                self.assertEqual(candidate[:start], self.proof[:start])
                self.assertEqual(candidate[new_end:], self.proof[end:])
                self.assertNotEqual(candidate[start:new_end], self.proof[start:end])

    def test_exact_seven_actual_assumptions_and_unknown_axioms_fail_closed(self):
        self.assertEqual(self.probe.count('Print Assumptions checked_'), 7)
        self.assertEqual(CHECK.checked_assumptions('Closed under the global context\n' * 7, 7), [])
        for output in ['Closed under the global context\n' * 6, 'Axioms:\nInjected : False\n' * 7]:
            with self.assertRaises(ValueError):
                CHECK.checked_assumptions(output, 7)


if __name__ == '__main__':
    unittest.main()
