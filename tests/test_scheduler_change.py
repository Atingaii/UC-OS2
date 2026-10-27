"""Prospective one-factor controls and fixed interfaces for the same OS_Sched."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / name)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


CHANGE = load('v293-scheduler-change.py')
CALLER = load('v293-scheduler-caller.py')


class ChangeMutationTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / CHANGE.CORE).read_text()
        self.mutants = CHANGE.mutations(self.source, CALLER.replace_once)

    def assert_inverse(self, label, old, new):
        mutant, _ = self.mutants[label]
        self.assertNotEqual(mutant, self.source)
        self.assertEqual(mutant.replace(new, old), self.source)

    def test_source_emission_is_exact(self):
        self.assertEqual((ROOT / CHANGE.CODE).read_text(), CHANGE.EMISSION)
        self.assertIn('eunop oppsite (ebinop oeq', CHANGE.EMISSION)
        self.assertIn('ebinop oplus (evar counter) (econst32 Int.one)', CHANGE.EMISSION)

    def test_controls_and_original_are_fixed(self):
        self.assertEqual(set(self.mutants), set(CHANGE.CONTROLS))
        self.assertEqual(self.source, (ROOT / CHANGE.CORE).read_text())
        for text, _ in self.mutants.values():
            self.assertNotEqual(text, self.source)

    def test_comparison_mutation_only_changes_result(self):
        self.assert_inverse('priority_comparison_inverted_only',
                            'then Int.zero else Int.one)) /\\', 'then Int.one else Int.zero)) /\\')

    def test_permission_mutation_only_changes_counter_cell(self):
        self.assert_inverse('counter_write_permission_removed_only',
            'V293_counter_bindings counter b ** PV (b, Int.zero) @ Tint32 |-> (Vint32 c).',
            'V293_counter_bindings counter b ** Amapsto (b, 0%Z) Tint32 false (Vint32 c).')

    def test_increment_mutation_only_changes_post_value(self):
        self.assert_inverse('counter_result_adds_two_only',
            '(frame ** V293_counter_cell counter b (Int.add c Int.one))) tid.',
            '(frame ** V293_counter_cell counter b (Int.add c (Int.repr 2)))) tid.')

    def test_equal_path_mutation_only_changes_postcondition(self):
        self.assert_inverse('equal_priority_post_inverted_only',
            'then V293_OSSched_tail_state c else q) tid.',
            'then q else V293_OSSched_tail_state c) tid.')

    def check_extra_premise(self, label, premise):
        mutant, obligation = self.mutants[label]
        self.assertEqual(obligation, 'Definition checked_guarded_change :')
        marker = 'Theorem V293_OSSched_guarded_changed_prefix'
        self.assertEqual(mutant.split(marker)[0], self.source.split(marker)[0])
        self.assertEqual(mutant.replace(premise + ' -> lo < 256', 'lo < 256')
                         .replace('Hli Hextra Hlo', 'Hli Hlo'), self.source)

    def test_no_wrap_premise_does_not_restrict_other_roots(self):
        self.check_extra_premise('counter_no_wrap_premise_added_only', 'c <> Int.repr 4294967295')

    def test_false_premise_does_not_change_downstream_witness(self):
        self.check_extra_premise('guarded_change_false_premise_added_only', 'False')

    def test_probe_is_independent_and_keeps_real_suffix(self):
        for abbreviation in ['V293_counter_cell', 'V293_OSSched_tail_state',
                             'V293_OSSched_change high', 'V293_OSSched_increment counter',
                             'V293_prefix_frame', 'V293_prefix_output']:
            self.assertNotIn(abbreviation, CHANGE.PROBE)
        self.assertIn('mid (Int.add c Int.one)) suffix q tid', CHANGE.PROBE)
        self.assertNotIn('scall OSCtxSw', CHANGE.PROBE)
        self.assertIn('forall ni nl nc c,', CHANGE.PROBE)
        self.assertIn('Int.add (Int.repr 4294967295) Int.one = Int.zero', CHANGE.PROBE)

    def test_probe_has_no_no_overflow_or_false_premise(self):
        self.assertNotIn('c <> Int.repr 4294967295', CHANGE.PROBE)
        self.assertNotIn('False ->', CHANGE.PROBE)

    def test_command_identities_are_unique(self):
        labels = [CHANGE.unit_label(f) for f in CHANGE.FILES]
        self.assertEqual(len(labels), len(set(labels)))

    def test_normalization_does_not_claim_verified_compiler(self):
        self.assertEqual(CHANGE.NORMALIZATION['boundary'],
                         'TRUSTED_RESTRICTED_AST_NORMALIZATION_NOT_VERIFIED_C_COMPILER')
        self.assertIn('UINT32_DISCARDED_POSTFIX', CHANGE.NORMALIZATION['counter'])
