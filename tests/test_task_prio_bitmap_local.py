"""Supplementary structural checks; actual Coq remains the proof oracle."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('task_bitmap_local', ROOT / 'scripts/check-v293-task-prio-rekey.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


class TaskPrioBitmapTests(unittest.TestCase):
    def setUp(self):
        self.proof = (ROOT / CHECK.PROOF).read_text()
        self.probe = (ROOT / 'audit/probes/V293TaskPrioBitmapProbe.v').read_text()

    def header(self, name):
        return self.proof.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]

    def test_forward_interface_requires_entry_not_post_relations(self):
        header = self.header('V293_task_prio_rekey_ready_correspondence')
        before, after = header.split('let rows :=', 1)
        self.assertIn('V293_priority_table entries tasks ->', before)
        self.assertIn('V293_bitmap_tasks lo hi tasks ->', before)
        self.assertIn('nth new entries Vnull = Vnull ->', before)
        self.assertNotIn("tasks'", before)
        self.assertIn('V293_bitmap_tasks (fst rows) (snd rows) tasks\'', after)
        self.assertIn('V293_highest_ready', after)
        self.assertNotIn('cstepstar', header)

    def test_finite_check_covers_all_byte_bit_pairs(self):
        self.assertIn('forallb (V293_rekey_byte_check row) (seq 0 8)) (seq 0 256)', self.proof)
        self.assertIn('Int.modu (Int.not (Int.shl Int.one', self.proof)
        self.assertIn('Nat.clearbit row bit <? 256', self.proof)
        self.assertIn('Nat.setbit row bit <? 256', self.proof)

    def test_exact_promotions_and_narrowing_in_independent_probe(self):
        self.assertIn('(ecast (ecast (eunop negation (ecast mask Tint32)) Tint8) Tint32)', self.probe)
        self.assertIn('ecast (ebinop obitor (ecast row Tint32) (ecast mask Tint32)) Tint8', self.probe)
        self.assertNotIn('V293_task_prio_clear_expr', self.probe)
        self.assertNotIn('V293_ready_rekey_rows', self.probe)
        self.assertEqual(self.probe.count('Print Assumptions checked_'), 8)

    def test_same_row_updates_read_cleared_row(self):
        block = self.proof.split('Definition V293_ready_rekey_rows', 1)[1].split('Lemma ', 1)[0]
        self.assertIn('V293_ready_set_rows (fst cleared) (snd cleared) new', block)
        self.assertIn('V293_ready_rekey_rows 20 0 2 6 = (80,0)', self.proof)
        self.assertIn('V293_ready_rekey_rows 0 1 8 10 = (0,4)', self.proof)

    def test_unused_high_bits_are_preserved_not_forbidden(self):
        header = self.header('V293_ready_rekey_high_bits')
        self.assertIn('5 <= bit ->', header)
        self.assertNotIn('hi <', header)
        self.assertIn('V293_ready_rekey_group 0 129 8 6 = 3', self.proof)

    def test_four_single_header_controls_keep_every_proof(self):
        controls = CHECK.mutations(self.proof, bitmap=True)
        self.assertEqual(len(controls), 4)
        for label, (candidate, declaration) in controls.items():
            with self.subTest(label=label):
                start = self.proof.index(declaration)
                end = self.proof.index('Proof.', start)
                new_end = candidate.index('Proof.', start)
                self.assertEqual(candidate[:start], self.proof[:start])
                self.assertEqual(candidate[new_end:], self.proof[end:])
                self.assertNotEqual(candidate[start:new_end], self.proof[start:end])

    def test_eight_root_trust_parser_remains_fail_closed(self):
        output = 'Closed under the global context\n' * 8
        self.assertEqual(CHECK.checked_assumptions(output, 8), [])
        for wrong in [output[:-1].rsplit('Closed', 1)[0], output + 'Axioms:\nInjected : False\n']:
            with self.assertRaises(ValueError):
                CHECK.checked_assumptions(wrong, 8)

    def test_helpers_do_not_keep_unused_priority_distinction(self):
        for name in ('V293_rekey_task_table_preserved', 'V293_rekey_ready_tasks_preserved'):
            self.assertNotIn('old <> new ->', self.header(name))
        self.assertIn('old <> new ->', self.header('V293_task_prio_rekey_ready_correspondence'))


if __name__ == '__main__':
    unittest.main()
