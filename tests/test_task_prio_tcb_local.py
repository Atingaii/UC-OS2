"""Structural companions; real Coq/coqchk remains the semantic oracle."""
import importlib.util
import json
import re
from pathlib import Path
import unittest
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('task_tcb_local', ROOT / 'scripts/check-v293-task-prio-rekey.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


class TaskPrioTCBTests(unittest.TestCase):
    def setUp(self):
        self.proof = (ROOT / CHECK.PROOF).read_text()
        self.code = (ROOT / CHECK.CODE).read_text()
        self.probe = (ROOT / 'audit/probes/V293TaskPrioTCBProbe.v').read_text()

    def header(self, name):
        return self.proof.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]

    def test_full_configured_record_and_explicit_padding(self):
        fields = self.code.split('Definition V293_tcb_fields', 1)[1].split('Definition V293_tcb_type', 1)[0]
        self.assertEqual(fields.count('dcons'), 22)
        self.assertIn('dcons 12%Z Tint16', fields)
        self.assertIn('dcons (-1)%Z (Tarray Tint8 2)', fields)
        self.assertIn('dcons 13%Z Tint32', fields)
        h = self.header('V293_tcb_old_field_layout')
        for offset in (52, 54, 53):
            self.assertIn(f'Some (Int.repr {offset})', h)
        source = json.loads((ROOT / 'audit/logs/stage26-task-prio-tcb/source-identity.json').read_text())
        self.assertTrue(source['materialized_source_hashes_match_frozen'])
        self.assertTrue(source['function_record_matches_frozen_inventory'])

    def test_literal_source_read_order_and_not_implementation_alias(self):
        body = self.probe.split('Definition checked_reads', 1)[1].split('Definition checked_put', 1)[0]
        self.assertEqual(body.count('sassign'), 3)
        self.assertLess(body.index('18%Z'), body.index('20%Z'))
        self.assertLess(body.index('20%Z'), body.index('19%Z'))
        for alias in ['V293_task_prio_read_old', 'V293_tcb_type', 'V293_tcb_fields',
                      'V293_tcb_read_memory', 'V293_tcb_fixture_memory']:
            self.assertNotRegex(self.probe, r'\b' + re.escape(alias) + r'\b')

    def test_store_success_is_derived_from_destination_permission(self):
        h = self.header('V293_tcb_field_assignment')
        before, after = h.split("let M' :=", 1)
        self.assertIn('(exists v, get M (bd,0%Z) = Some (true,v)) ->', before)
        self.assertIn('load Tint8 M (bt,(base+delta)%Z)', before)
        self.assertNotIn('store ', before)
        self.assertIn('cstepstar', after)
        self.assertIn("load Tint8 M'", after)

    def test_three_reads_require_only_entry_not_intermediate_or_exit_loads(self):
        before, after = self.header('V293_task_prio_read_old_execution').split("let M' :=", 1)
        self.assertNotIn('M1', before)
        self.assertNotIn('M2', before)
        self.assertNotIn('cstepstar', before)
        self.assertNotIn('store ', before)
        self.assertIn('b <> bc /\\ b <> bt', before)
        self.assertIn("V293_tcb_old_loads M'", after)
        body = self.proof.split('Theorem V293_task_prio_read_old_execution :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('P1', body)
        self.assertIn('P2', body)
        self.assertIn('V293_put_byte_pointer_frame', body)

    def test_same_state_witness_has_pointer_fields_and_all_write_permissions(self):
        h = self.header('V293_tcb_read_entry_witness')
        self.assertIn('V293_tcb_old_loads M', h)
        self.assertIn('load (Tptr V293_tcb_type) M', h)
        self.assertEqual(h.count('(exists v, get M'), 3)
        self.assertIn('8%Z', h)
        self.assertIn('V293_tcb_read_execution_witness', self.probe)

    def test_four_designated_header_mutations_preserve_every_proof(self):
        controls = CHECK.mutations(self.proof, tcb=True)
        self.assertEqual(len(controls), 4)
        for label, (candidate, declaration) in controls.items():
            with self.subTest(label=label):
                start = self.proof.index(declaration)
                end = self.proof.index('Proof.', start)
                new_end = candidate.index('Proof.', start)
                self.assertEqual(self.proof[:start], candidate[:start])
                self.assertEqual(self.proof[end:], candidate[new_end:])
                self.assertNotEqual(self.proof[start:end], candidate[start:new_end])

    def test_alias_is_an_actual_pointer_decoding_control(self):
        h = self.header('V293_tcb_pointer_alias_control')
        self.assertIn('store Tint8 M', h)
        self.assertIn("load (Tptr V293_tcb_type) M'", h)
        self.assertIn('Some Vundef', h)

    def test_concrete_control_fixes_arguments_before_conversion(self):
        body = self.proof.split('Theorem V293_tcb_read_physical_control :', 1)[1].split('Proof.', 1)[1].split('Qed.', 1)[0]
        self.assertIn('V293_tcb_read_execution_witness P ks 1 2 4', body)
        self.assertNotIn('apply V293_tcb_read_execution_witness', body)

    def test_seven_actual_root_assumption_prints(self):
        self.assertEqual(self.probe.count('Print Assumptions checked_'), 7)
        self.assertEqual(CHECK.checked_assumptions('Closed under the global context\n' * 7, 7), [])
        with self.assertRaises(ValueError):
            CHECK.checked_assumptions('Closed under the global context\n' * 6, 7)
        with self.assertRaises(ValueError):
            CHECK.checked_assumptions('Axioms:\nInjected : False\n' * 7, 7)


if __name__ == '__main__':
    unittest.main()
