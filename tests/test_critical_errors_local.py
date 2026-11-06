"""Narrow source/interface regressions; proof credit comes only from the Coq gate."""
import hashlib
import importlib.util
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT/'certiucos/v293/proofs/V293CriticalReturn.v'
LOG = ROOT/'audit/logs/stage26-critical-errors'


def gate():
    spec = importlib.util.spec_from_file_location('critical_errors', ROOT/'scripts/check-v293-critical-errors.py')
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def section(name):
    return SOURCE.read_text().split('Theorem '+name+' :', 1)[1].split('Qed.', 1)[0]


class CriticalErrorsTests(unittest.TestCase):
    def test_original_659_lines_preserved(self):
        old = (LOG/'original-critical-return.v.snapshot.txt').read_bytes()
        self.assertEqual(hashlib.sha256(old).hexdigest(), '8ba9dde984c7eac06c50e8fda09675b89ec033d6d5b0e32f20b2f1d651f2e058')
        self.assertTrue(SOURCE.read_bytes().startswith(old))
        bare = re.sub(r'\(\*.*?\*\)', '', SOURCE.read_text(), flags=re.S)
        self.assertIsNone(re.search(r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Inductive)\b', bare))

    def test_same_program_both_branches_and_ie(self):
        h = section('V293_lookup_error_critical_return').split('Proof.', 1)[0]
        self.assertIn('V293_primitive_critical_prefix table oldprio newprio ptcb current reserved', h)
        self.assertIn('Some (if absent then Vnull else Vptr (br,Int.zero))', h)
        self.assertIn('(Int.repr (if absent then 41 else 67))', h)
        self.assertEqual(h.count('(enabled,si,ci)'), 2)
        self.assertIn('(ge,caller,Mf)', h)
        self.assertNotIn('resolved <> new', h)
        self.assertNotIn('V293_raw_critical_prefix', h)
        self.assertIn('(absent = false -> get le reserved = None', h)

    def test_no_intermediate_execution_store_free_oracle(self):
        for name in ['V293_resolve_lookup_resources', 'V293_lookup_error_critical_return']:
            h = section(name).split('Proof.', 1)[0].split('exists Ml,', 1)[0].split('exists Mf,', 1)[0]
            for forbidden in ['cstepstar', 'loststep', 'V293_local_steps', 'storebytes', 'free ', 'V293_saved_ie']:
                self.assertNotIn(forbidden, h)
        h = section('V293_lookup_error_critical_return').split('Proof.', 1)[0]
        self.assertIn('NoDup (map fst (getaddr le))', h)
        self.assertIn('V293_bytes_writable M c 0%Z (typelen t)', h)

    def test_resources_come_from_actual_writes(self):
        helper = section('V293_resolve_lookup_resources').split('Proof.', 1)[1]
        for used in ['V293_coordinate_local_assignment', 'V293_assign_pointer_execution',
                     'V293_storebytes_exists', 'V293_store_readback', 'V293_storebytes_preserves_writable']:
            self.assertIn(used, helper)
        proof = section('V293_lookup_error_critical_return').split('Proof.', 1)[1]
        for used in ['V293_resolve_lookup_resources', 'eapply Permissions', 'V293_error_return_execution',
                     'apply encrit_step', 'apply excrit_step', 'V293_task_prio_argument_accepts']:
            self.assertIn(used, proof)

    def test_witness_not_preinitialized_and_aliasing_slot_covered(self):
        s = section('V293_lookup_error_critical_witness')
        h = s.split('Proof.', 1)[0]
        self.assertIn('forall P self absent enabled ir,', h)
        self.assertIn('Some (Vptr (70%positive,Int.zero))', h)
        self.assertIn('(Int.repr 23)', h)
        self.assertIn('scall 999%Z nil', h)
        self.assertNotIn('P 999', h)
        self.assertIn('(if self then 255 else 8) (if absent then 8 else 6) 8 90%positive absent', s)
        self.assertIn('get Mf (40%positive,Z.of_nat k) = None', h)
        self.assertIn('get Mf (61%positive,Z.of_nat k) = None', h)
        fixture = SOURCE.read_text().split('Definition V293_lookup_critical_fixture_mem ', 1)[1].split('Theorem ', 1)[0]
        self.assertNotIn('enabled', re.sub(r'\(\*.*?\*\)', '', fixture, flags=re.S))

    def test_projections_remove_early_correlated_roots(self):
        g = gate()
        lookup, error = g.projections(SOURCE.read_text())
        for s in [lookup, error]:
            self.assertNotIn('Theorem V293_critical_prefix_normalization :', s)
            self.assertNotIn('Theorem V293_occupied_critical_return :', s)
            self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn', s)
        self.assertIn('Theorem '+g.LOOKUP+' :', lookup)
        self.assertNotIn('Theorem '+g.ERROR+' :', lookup)
        self.assertIn('Theorem '+g.ERROR+' :', error)

    def test_single_factor_controls_preserve_entire_proof_suffix(self):
        g = gate()
        cases = g.controls(SOURCE.read_text())
        self.assertEqual([c[0] for c in cases], ['SkipSelf', 'SkipLookup', 'WrongReturn', 'ExitSti'])
        for label, changed, target, original in cases:
            i = original.index('Proof.', original.index('Theorem '+target+' :'))
            j = changed.index('Proof.', changed.index('Theorem '+target+' :'))
            self.assertEqual(original[i:], changed[j:], label)
            self.assertNotEqual(original[:i], changed[:j], label)

    def test_literal_probe_has_no_signature_generator(self):
        probe = (ROOT/'audit/probes/V293CriticalErrorsProbe.v').read_text()
        self.assertIn('Example expected_error_interface :', probe)
        self.assertIn('Example expected_physical_errors :', probe)
        self.assertIn('Example expected_permission_transport :', probe)
        self.assertEqual(probe.count('Print Assumptions '), 3)
        self.assertNotIn('Admitted', probe)


if __name__ == '__main__':
    unittest.main()
