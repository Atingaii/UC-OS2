"""Local success trace shape and gate evidence, not whole-kernel coverage."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT/'audit/logs/stage26-critical-success'
SOURCE = ROOT/'certiucos/v293/proofs/V293CriticalReturn.v'


def gate():
    spec = importlib.util.spec_from_file_location('critical_success_gate', ROOT/'scripts/check-v293-critical-success.py')
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def section(name):
    s = SOURCE.read_text()
    i = s.index(name+' :')
    return s[i:s.index('\nQed.', i)]


class CriticalSuccessLocalTests(unittest.TestCase):
    def test_original_1132_lines_and_axiom_boundary_preserved(self):
        old = (LOG/'V293CriticalReturn.before.v.snapshot.txt').read_bytes()
        self.assertEqual(hashlib.sha256(old).hexdigest(), '5b2d8a4cdf877f03a0c372290e8092e2d635a4050a66c65c00e04a8b76477d8a')
        self.assertTrue(SOURCE.read_bytes().startswith(old))
        bare = re.sub(r'\(\*.*?\*\)', '', SOURCE.read_text(), flags=re.S)
        self.assertIsNone(re.search(r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit)\b', bare))

    def test_public_roots_have_original_memory_resources_not_execution_oracles(self):
        for name in [gate().NULL, gate().EVENT]:
            h = section(name).split('Proof.', 1)[0]
            pre = h.split('exists Mg,', 1)[0]
            for unwanted in ['cstepstar', 'loststep', 'V293_local_steps', 'storebytes', 'free ']:
                self.assertNotIn(unwanted, pre)
            self.assertIn('(initial < 12 \\/ initial = 255)', pre)
            self.assertIn('V293_bytes_writable M bc', pre)
            self.assertIn('V293_tcb_update_writable M bt base', pre)
            self.assertEqual(h.count('(enabled,si,ci)'), 2)
            self.assertIn('V293_primitive_success_update', h)

    def test_success_entry_constructs_resolve_lookup_and_false_guards(self):
        p = section(gate().ENTRY).split('Proof.', 1)[1]
        for item in ['V293_task_prio_resolve_execution', 'V293_storebytes_exists',
                     'V293_assign_pointer_execution', 'exact TargetTest', 'exact NullTest',
                     'V293_reserved_test_eval', 'exact ReservedTest']:
            self.assertIn(item, p)
        self.assertNotIn('V293_task_prio_entry_reserved_execution', p)

    def test_resources_feed_actual_current_backend_and_same_excrit_trace(self):
        for name, backend in [(gate().NULL, 'V293_task_prio_coordinates_null_update_execution'),
                              (gate().EVENT, 'V293_task_prio_coordinates_update_execution')]:
            p = section(name).split('Proof.', 1)[1]
            for item in ['V293_primitive_entry_success', 'EntryFrame', 'assert (Resources',
                         backend, 'V293_success_segment_execution']:
                self.assertIn(item, p)
        p = section(gate().SEGMENT).split('Proof.', 1)[1]
        self.assertIn('V293_task_prio_argument_accepts', p)
        self.assertIn('apply encrit_step', p)
        self.assertIn('exact Entry', p)
        self.assertIn('exact Update', p)
        self.assertIn('apply excrit_step', p)
        self.assertNotIn('scall', p)

    def test_physical_witnesses_cover_both_selectors_ready_choices_and_ie(self):
        for name in ['V293_critical_null_update_witness', 'V293_critical_event_update_witness']:
            h = section(name).split('Proof.', 1)[0]
            for item in ['forall self live elo ehi', 'forall P ks ir enabled si ci',
                         'Some Vnull', 'Some (V293_byteval 255)',
                         '(if live then 80 else 16)', 'V293_tcb_updated_loads Mh 41%positive 8%Z 6']:
                self.assertIn(item, h)
        self.assertIn('get Mh (72%positive,i)', section('V293_critical_null_update_witness'))
        self.assertIn('V293_event_bitmap_loads Mh 72%positive', section('V293_critical_event_update_witness'))

    def test_projections_exclude_historical_error_and_normalization_roots(self):
        g = gate()
        for target in [g.ENTRY, g.SEGMENT, g.NULL, g.EVENT]:
            s = g.projection(SOURCE.read_text(), target)
            for name in ['V293_critical_prefix_normalization', 'V293_occupied_critical_return',
                         'V293_lookup_error_critical_return', 'V293_invalid_critical_return']:
                self.assertNotIn('Theorem '+name+' :', s)
            self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn', s)
            self.assertIn(target+' :', s)

    def test_single_factor_controls_preserve_entire_target_proof_suffix(self):
        g = gate()
        cases = g.controls(SOURCE.read_text())
        self.assertEqual([c[0] for c in cases], ['SkipSelf', 'SkipLookup', 'EnterCli', 'ExitSti', 'WrongIE', 'WrongTCB', 'WrongEvent'])
        for label, changed, target, original in cases:
            i = original.index('Proof.', original.index(target+' :'))
            j = changed.index('Proof.', changed.index(target+' :'))
            self.assertEqual(original[i:], changed[j:], label)
            self.assertNotEqual(original[:i], changed[:j], label)
        _, changed, _, original = cases[3]
        i = original.index('Definition V293_primitive_success_update ')
        j = original.index('Proof.', original.index(g.SEGMENT+' :'))
        self.assertEqual(original[i:j].count('(sprim excrit)'), 5)
        self.assertEqual(changed[i:j].count('(sprim sti)'), 5)

    def test_fixed_literal_probe_does_not_alias_candidate_program(self):
        s = (ROOT/'audit/probes/V293CriticalSuccessProbe.v').read_text()
        self.assertEqual(s.count('Print Assumptions '), 6)
        self.assertIn('(sseq (sprim encrit) (expected_success_entry', s)
        self.assertIn('(sprim excrit)).', s)
        self.assertIn('(srete (econst32 (Int.repr 67)))', s)
        self.assertNotIn('V293_primitive_success_update', s)
        for name in ['expected_null_physical', 'expected_event_physical']:
            self.assertIn(name+' self live 23 1 P ks ir enabled si ci', s)

    def test_canonical_gate_checked_actual_assumptions_and_target_rejections(self):
        result = json.loads((LOG/'gate01/result.json').read_text())
        self.assertTrue(result['passed'])
        self.assertTrue(result['inputs_unchanged'])
        self.assertEqual(len(result['checks']), 16)
        # Bind the result to its frozen source snapshot. Later append-only work
        # does not retroactively acquire this checkpoint's gate credit.
        snapshot = (LOG/'gate01/PositiveFull.v.snapshot.txt').read_bytes()
        original = snapshot.split(b'\nPrint Assumptions V293_primitive_entry_success.', 1)[0]
        self.assertEqual(hashlib.sha256(original).hexdigest(), result['inputs'][str(SOURCE.relative_to(ROOT))])
        self.assertTrue(SOURCE.read_bytes().startswith(original))
        for label,row in result['checks'].items():
            if label.startswith('negative-'):
                self.assertEqual(row['exit_code'], 1)
                self.assertGreater(row['error_line'], row['target_proof_line'])
                self.assertTrue(row['proof_suffix_unchanged'])
                self.assertFalse(row['downstream_credit'])
            else:
                self.assertEqual(row['exit_code'], 0)
        self.assertEqual(set(result['positive_assumptions']), {'PositiveFull', 'PositiveEntry', 'PositiveSegment', 'PositiveNull', 'PositiveEvent'})


if __name__ == '__main__':
    unittest.main()
