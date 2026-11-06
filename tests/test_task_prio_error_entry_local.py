"""Narrow mapping/protocol checks; Coq execution is checked by the live gate."""
import importlib.util
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
PROOF = ROOT / 'certiucos/v293/proofs/V293TaskPrioRekey.v'


def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT/'scripts'/name)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def declaration(name):
    return PROOF.read_text().split('Theorem '+name+' :', 1)[1].split('Proof.', 1)[0]


class ErrorEntryTests(unittest.TestCase):
    def test_fresh_fixed_c_and_three_address_arguments(self):
        mapping = module('check-v293-critical-args.py')
        fresh = mapping.configured_calls()
        self.assertEqual(fresh['function']['preprocessed_definition_sha256'],
                         'c29b633e71cf54c2d244eb87c7a5910a1f2973e6cd23d7a23769070b24bc2dbf')
        self.assertEqual(len(fresh['calls']), 5)
        mapping.check_model((ROOT/mapping.CODE).read_text())

    def test_occupied_requires_no_old_ptcb_or_reserved_reads(self):
        header = declaration('V293_task_prio_occupied_entry_execution').split('cstepstar P', 1)[0]
        self.assertNotIn('get le oldprio', header)
        self.assertNotIn('get le ptcb', header)
        self.assertNotIn('get le reserved', header)
        self.assertIn('Some (Vptr next) ->', header)

    def test_absent_has_no_different_slot_or_initial_ptcb_value(self):
        header = declaration('V293_task_prio_absent_entry_execution')
        premises = header.split('exists Mf,', 1)[0]
        self.assertNotIn('resolved <> new', premises)
        self.assertNotIn('load (Tptr V293_tcb_type) M (bc,', premises)
        self.assertIn('V293_bytes_writable M bc 0%Z 4 ->', premises)
        self.assertNotIn('cstepstar', premises)
        self.assertNotIn('store ', premises)
        self.assertIn('forall i, i < 13', header)
        witness = declaration('V293_task_prio_absent_same_slot_witness')
        self.assertIn('Vptr (70%positive,Int.zero)', witness)
        self.assertIn('load Tint8 Mf (51%positive,0%Z) = Some (V293_byteval 8)', witness)
        self.assertIn('load Tint8 Mf (52%positive,0%Z) = Some (V293_byteval 8)', witness)

    def test_reserved_comes_from_original_table_not_ptcb_or_execution_oracle(self):
        premises = declaration('V293_task_prio_reserved_entry_error_execution').split('exists Mf,', 1)[0]
        self.assertIn('M (b,(4*Z.of_nat resolved)%Z) = Some (Vptr (br,Int.zero))', premises)
        self.assertNotIn('load (Tptr V293_tcb_type) M (bc,', premises)
        self.assertNotIn('cstepstar', premises)
        self.assertNotIn('P exit_id', premises)

    def test_prospective_controls_change_one_header_only(self):
        gate = module('check-v293-task-prio-error-entry.py')
        suffix = gate.MARKER+PROOF.read_text().split(gate.MARKER, 1)[1]
        cases = gate.controls(suffix)
        self.assertEqual(len(cases), 4)
        for label, mutated, root, _ in cases:
            start = suffix.index('Theorem '+root+' :')
            proof = suffix.index('Proof.', start)
            changed_proof = mutated.index('Proof.', mutated.index('Theorem '+root+' :'))
            self.assertEqual(suffix[:start], mutated[:start], label)
            self.assertEqual(suffix[proof:], mutated[changed_proof:], label)
            self.assertNotEqual(suffix[start:proof], mutated[start:changed_proof], label)
        source = (ROOT/'scripts/check-v293-task-prio-error-entry.py').read_text()
        self.assertIn("all(root not in prefix for root in ROOTS)", source)
        self.assertIn('int(match[1]) > target_proof_line', source)
        self.assertIn('downstream_credit=False', source)

    def test_handwritten_probe_and_no_new_trust_primitives(self):
        probe = (ROOT/'audit/probes/V293TaskPrioErrorEntryProbe.v').read_text()
        for name in ['checked_occupied', 'checked_absent', 'checked_reserved']:
            self.assertRegex(probe, r'Definition '+name+r'\s*:\s*\n?\s*forall')
        self.assertEqual(probe.count('Print Assumptions '), 7)
        suffix = PROOF.read_text().split('(* Compose a skip-terminating prefix', 1)[1]
        uncommented = re.sub(r'\(\*.*?\*\)', '', suffix, flags=re.S)
        self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture)\b', uncommented))


if __name__ == '__main__':
    unittest.main()
