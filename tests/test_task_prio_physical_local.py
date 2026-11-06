"""Structural companions only; actual Coq compilation is the semantic oracle."""
import importlib.util
from pathlib import Path
import unittest
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('task_physical_local', ROOT / 'scripts/check-v293-task-prio-rekey.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


class TaskPrioPhysicalTests(unittest.TestCase):
    def setUp(self):
        self.proof = (ROOT / CHECK.PROOF).read_text()
        self.code = (ROOT / CHECK.CODE).read_text()
        self.probe = (ROOT / 'audit/probes/V293TaskPrioPhysicalProbe.v').read_text()

    def header(self, name):
        return self.proof.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]

    def test_execution_requires_only_entry_memory(self):
        before, after = self.header('V293_task_prio_ready_then_execution').split("let M' :=", 1)
        self.assertIn('V293_rekey_bitmap_loads M br bg lo hi (V293_ready_group lo hi) ->', before)
        self.assertIn('V293_rekey_bitmap_writable M br bg ->', before)
        self.assertNotIn('store ', before)
        self.assertNotIn("M'", before)
        self.assertIn('cstepstar', after)
        self.assertIn("V293_rekey_bitmap_loads M'", after)

    def test_real_rhs_and_statement_order_in_literal_probe(self):
        self.assertNotIn('V293_task_prio_ready_then', self.probe.split('Definition checked_execution :', 1)[1].split(':=', 1)[0])
        self.assertNotIn('V293_task_prio_clear_expr', self.probe)
        self.assertNotIn('V293_rekey_ready_memory', self.probe)
        seq = self.probe.split('Definition checked_then', 1)[1].split('Definition checked_put', 1)[0]
        self.assertEqual(seq.count('sassign'), 4)
        self.assertEqual(seq.count('sifthen'), 1)
        self.assertLess(seq.index('checked_clear (evar group)'), seq.index('checked_set (evar group)'))
        self.assertLess(seq.index('checked_set (evar group)'), seq.rindex('checked_set (earrayelem'))

    def test_generic_rmw_constructs_store_from_permission(self):
        before, after = self.header('V293_rekey_byte_rmw_execution').split('let value :=', 1)
        self.assertIn('(exists v, get M (b,off) = Some (true,v)) ->', before)
        self.assertNotIn('store ', before)
        self.assertIn('evalval lhs', before)
        self.assertIn('load Tint8', after)

    def test_witness_inhabits_full_same_state_entry(self):
        header = self.header('V293_ready_fragment_entry_witness')
        self.assertIn('V293_rekey_bitmap_loads', header)
        self.assertIn('V293_rekey_bitmap_writable', header)
        self.assertIn('V293_rekey_locals', header)
        self.assertNotIn('->\n  V293_rekey_locals', header)
        self.assertIn('V293_ready_fragment_execution_witness', self.probe)

    def test_all_four_single_header_controls_preserve_proofs(self):
        controls = CHECK.mutations(self.proof, physical=True)
        self.assertEqual(len(controls), 4)
        for label, (candidate, declaration) in controls.items():
            with self.subTest(label=label):
                start = self.proof.index(declaration)
                end = self.proof.index('Proof.', start)
                new_end = candidate.index('Proof.', start)
                self.assertEqual(self.proof[:start], candidate[:start])
                self.assertEqual(self.proof[end:], candidate[new_end:])
                self.assertNotEqual(self.proof[start:end], candidate[start:new_end])

    def test_bounds_include_same_row_and_unused_high_bits(self):
        header = self.header('V293_task_prio_ready_then_execution')
        self.assertNotIn('old <> new', header)
        self.assertNotIn('hi < 128', header)
        controls = self.header('V293_ready_fragment_physical_controls')
        self.assertIn('20 0 2 6 80 0 1', controls)
        self.assertIn('0 129 8 6 64 128 3', controls)

    def test_alias_is_real_store_readback_not_an_api_counterexample(self):
        header = self.header('V293_ready_fragment_alias_control')
        self.assertIn('store Tint8 M', header)
        self.assertIn("load Tint8 M'", header)
        self.assertIn('Removing only the no-alias restriction', self.proof)

    def test_seven_actual_root_trust_prints(self):
        self.assertEqual(self.probe.count('Print Assumptions checked_'), 7)
        self.assertEqual(CHECK.checked_assumptions('Closed under the global context\n' * 7, 7), [])
        with self.assertRaises(ValueError):
            CHECK.checked_assumptions('Closed under the global context\n' * 6, 7)
        with self.assertRaises(ValueError):
            CHECK.checked_assumptions('Axioms:\nInjected : False\n' * 7, 7)


if __name__ == '__main__':
    unittest.main()
