"""Structural regressions only; Coq gate provides the execution proof credit."""
import hashlib
import importlib.util
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT/'certiucos/v293/proofs/V293CriticalReturn.v'
LOG = ROOT/'audit/logs/stage26-critical-invalid'


def section(name):
    return SOURCE.read_text().split(name+' :', 1)[1].split('Qed.', 1)[0]


def gate():
    spec = importlib.util.spec_from_file_location('critical_invalid', ROOT/'scripts/check-v293-critical-invalid.py')
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


class CriticalInvalidTests(unittest.TestCase):
    def test_original_980_lines_preserved_and_no_new_axioms(self):
        old = (LOG/'original-critical-return.v.snapshot.txt').read_bytes()
        self.assertEqual(hashlib.sha256(old).hexdigest(), 'c00c990eeff444c280718deb072bc7b459783b3347460edb9d187671a317fb05')
        self.assertTrue(SOURCE.read_bytes().startswith(old))
        bare = re.sub(r'\(\*.*?\*\)', '', SOURCE.read_text(), flags=re.S)
        self.assertIsNone(re.search(r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit)\b', bare))

    def test_stable_same_program_interface_has_no_shared_or_execution_oracle(self):
        h = section('V293_invalid_critical_return').split('Proof.', 1)[0]
        before = h.split('exists Mf,', 1)[0]
        self.assertIn('((12 <= old /\\ old <> 255) \\/ 12 <= new)', h)
        self.assertIn('V293_primitive_critical_prefix table oldprio newprio ptcb current reserved', h)
        self.assertEqual(h.count('(enabled,si,ci)'), 2)
        self.assertIn('(Int.repr 42)', h)
        self.assertIn('NoDup (map fst (getaddr le))', before)
        self.assertIn('V293_bytes_writable M c', before)
        for unwanted in ['get ge', 'get le table', 'get le current', 'get le reserved',
                         'get le ptcb', 'cstepstar', 'loststep', 'V293_local_steps', 'storebytes', 'free ']:
            self.assertNotIn(unwanted, before)

    def test_guard_execution_is_connected_to_evaluated_return_and_real_free(self):
        p = section('V293_invalid_critical_return').split('Proof.', 1)[1]
        for used in ['V293_task_prio_argument_execution', 'V293_evaluated_return_execution',
                     'V293_csteps_local', 'exact Guards', 'exact Return']:
            self.assertIn(used, p)
        self.assertNotIn('apply encrit_step', p)
        self.assertNotIn('apply excrit_step', p)
        q = section('V293_evaluated_return_execution').split('Proof.', 1)[1]
        for used in ['V293_sfree_construct_execution', 'sretv_step', 'sfreeend_step']:
            self.assertIn(used, q)
        self.assertNotIn('apply srete_step', q)

    def test_physical_witness_empty_globals_and_all_interrupt_states(self):
        h = section('V293_invalid_critical_witness').split('Proof.', 1)[0]
        for needed in ['forall P old new enabled ir si ci', '(scall 999%Z nil)',
                       '((emp,V293_critical_fixture_le,', '((emp,emp,Mf),ir,(enabled,si,ci))',
                       'get Mf (61%positive,Z.of_nat k) = None',
                       'get Mf (51%positive,0%Z) = None', 'get Mf (52%positive,0%Z) = None',
                       'load Tint8 Mf (90%positive,0%Z) = Some (V293_byteval 23)']:
            self.assertIn(needed, h)
        self.assertNotIn('P 999', h)

    def test_single_factor_controls_and_isolated_positive(self):
        g = gate()
        focused = g.projection(SOURCE.read_text())
        for old_root in ['V293_critical_prefix_normalization', 'V293_occupied_critical_return',
                         'V293_lookup_error_critical_return']:
            self.assertNotIn('Theorem '+old_root+' :', focused)
        self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn', focused)
        cases = g.controls(SOURCE.read_text())
        self.assertEqual([c[0] for c in cases], ['WrongReturn', 'AdmitValidOld', 'WrongIE', 'NoWritable'])
        for label, changed, target, original in cases:
            i = original.index('Proof.', original.index('Theorem '+target+' :'))
            j = changed.index('Proof.', changed.index('Theorem '+target+' :'))
            self.assertEqual(original[i:], changed[j:], label)
            self.assertNotEqual(original[:i], changed[:j], label)

    def test_handwritten_probe_includes_three_guard_routes(self):
        p = (ROOT/'audit/probes/V293CriticalInvalidProbe.v').read_text()
        self.assertEqual(p.count('Print Assumptions '), 3)
        for old, new in [(12, 6), (8, 12), (255, 12)]:
            self.assertIn(f'expected_invalid_physical P {old} {new} enabled ir si ci', p)
        self.assertIn('(sseq (V293_task_prio_argument_guards oldprio newprio)', p)
        self.assertNotIn('Admitted', p)


if __name__ == '__main__':
    unittest.main()
