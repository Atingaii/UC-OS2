"""Narrow boundary/protocol checks; live Coq checking is the separate gate."""
import importlib.util
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT/'certiucos/v293/proofs/V293CriticalReturn.v'


def gate():
    spec = importlib.util.spec_from_file_location('critical_return', ROOT/'scripts/check-v293-critical-return.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def header(name):
    return SOURCE.read_text().split('Theorem '+name+' :', 1)[1].split('Proof.', 1)[0]


class CriticalReturnTests(unittest.TestCase):
    def test_port_call_not_replaced_by_a_new_execution_rule(self):
        source = SOURCE.read_text()
        bare = re.sub(r'\(\*.*?\*\)', '', source, flags=re.S)
        self.assertIsNone(re.search(r'\b(?:Inductive|Axiom|Parameter|Conjecture|Admitted|admit)\b', bare))
        missing = header('V293_missing_port_has_no_step')
        self.assertIn('P exit_id = None ->', missing)
        self.assertIn('~ exists C\' state\'', missing)
        self.assertIn('sfexec exit_id args types', missing)

    def test_reserved_saved_premises_are_raw_not_intermediate_oracles(self):
        h = header('V293_reserved_entry_preserves_saved')
        premises = h.split('exists Mf,', 1)[0]
        self.assertNotIn('cstepstar', premises)
        self.assertNotIn('store ', premises)
        self.assertNotIn('load (Tptr V293_tcb_type) M (bc,', premises)
        self.assertIn('bs <> bo -> bs <> bc -> V293_saved_ie M bs saved ->', premises)
        self.assertIn('V293_task_prio_entry_reserved', h)
        self.assertIn('sfexec exit_id (Vptr (bs,Int.zero)::nil)', h)
        self.assertIn('V293_saved_ie Mf bs saved', h)

    def test_return_constructs_and_frees_locals_not_assumes_execution(self):
        h = header('V293_error_return_execution')
        premises = h.split('exists M\',', 1)[0]
        self.assertNotIn('cstepstar', premises)
        self.assertNotIn('free ', premises)
        self.assertIn('NoDup (map fst (getaddr le)) ->', premises)
        self.assertIn('V293_bytes_writable M b 0%Z (typelen t)', premises)
        self.assertIn('(ge,caller,M\')', h)
        self.assertIn('get M\' (b,Z.of_nat k) = None', h)

    def test_witnesses_cover_both_saved_values_and_pending_undefined_call(self):
        self.assertIn('forall self saved P ks,', header('V293_reserved_saved_witness'))
        h = header('V293_error_return_locals_witness')
        self.assertIn('forall P saved,', h)
        self.assertIn('kseq (scall 999%Z nil)', h)
        self.assertNotIn('P 999', h)
        self.assertIn('k < 4 -> get Mf (61%positive,Z.of_nat k) = None', h)
        probe = (ROOT/'audit/probes/V293CriticalReturnProbe.v').read_text()
        self.assertIn('Definition checked_disabled : forall', probe)
        self.assertIn('((ge,le,M),ir,(false,si,ci))', probe)

    def test_alias_counterexample_changes_only_one_byte(self):
        h = header('V293_saved_byte_alias_counterexample')
        self.assertIn('~ V293_saved_ie (V293_put_byte M (61%positive,0%Z) 8)', h)
        self.assertIn('(c,i) <> (61%positive,0%Z)', h)
        self.assertIn('get M (c,i)', h)
        self.assertNotIn('vm_compute', SOURCE.read_text())

    def test_four_controls_preserve_original_proof_suffix(self):
        source = SOURCE.read_text()
        module = gate()
        cases = module.controls(source)
        self.assertEqual(len(cases), 4)
        for label, mutated, root in cases:
            start = source.index('Theorem '+root+' :')
            proof = source.index('Proof.', start)
            changed = mutated.index('Proof.', mutated.index('Theorem '+root+' :'))
            self.assertEqual(source[:start], mutated[:start], label)
            self.assertNotEqual(source[start:proof], mutated[start:changed], label)
            self.assertEqual(source[proof:], mutated[changed:], label)
        self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn', source)

    def test_literal_probe_is_not_generated_by_the_gate(self):
        probe = (ROOT/'audit/probes/V293CriticalReturnProbe.v').read_text()
        for name in ['checked_restore', 'checked_disabled', 'checked_missing', 'checked_return', 'checked_reserved']:
            self.assertRegex(probe, r'Definition '+name+r'\s*:\s*forall')
        self.assertEqual(probe.count('Print Assumptions '), 9)
        script = (ROOT/'scripts/check-v293-critical-return.py').read_text()
        self.assertIn('int(match[1]) > proof_line', script)
        self.assertIn('downstream_credit=False', script)
        self.assertNotIn("(ROOT/PROBE).write_text", script)


if __name__ == '__main__':
    unittest.main()
