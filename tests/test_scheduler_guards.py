"""Single-factor guard mutations and independently fixed interfaces."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / name)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


GUARDS = load('v293-scheduler-guards.py')
CALLER = load('v293-scheduler-caller.py')


class GuardMutationTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / GUARDS.CORE).read_text()
        self.mutants = GUARDS.mutations(self.source, CALLER.replace_once)

    def test_source_emission_is_exact(self):
        self.assertEqual((ROOT / GUARDS.CODE).read_text(), GUARDS.EMISSION)
        self.assertIn('ecast (evar x) Tint32', GUARDS.EMISSION)

    def test_control_set_and_original_are_unchanged(self):
        self.assertEqual(set(self.mutants), set(GUARDS.CONTROLS))
        self.assertEqual(self.source, (ROOT / GUARDS.CORE).read_text())

    def test_result_inversion_only_changes_conclusion(self):
        s, root = self.mutants['guard_result_inverted_only']
        self.assertEqual(root, 'Lemma V293_guard_eval')
        self.assertEqual(s.replace('if Nat.eqb n 0 then Int.zero else Int.one',
                                   'if Nat.eqb n 0 then Int.one else Int.zero'), self.source)

    def test_inner_variable_only_changes_requested_program(self):
        s, root = self.mutants['lock_guard_replaced_with_interrupt_only']
        self.assertEqual(root, 'Theorem V293_OSSched_guards_rule')
        self.assertEqual(s.replace('(V293_OSSched_guards x x body)',
                                   '(V293_OSSched_guards x lock body)'), self.source)

    def test_enabled_result_only_changes_postcondition(self):
        s, root = self.mutants['enabled_post_ignores_lock_only']
        self.assertEqual(root, 'Theorem V293_OSSched_guards_rule')
        self.assertEqual(s.replace('if Nat.eqb ni 0 then q else p',
                                   'if Nat.eqb ni 0 && Nat.eqb nl 0 then q else p'), self.source)

    def test_false_premise_only_changes_continuation(self):
        s, root = self.mutants['continuation_false_premise_added_only']
        self.assertEqual(root, 'Definition checked_guarded_prefix :')
        marker = 'Theorem V293_OSSched_guarded_prefix_continuation'
        self.assertEqual(s.split(marker)[0], self.source.split(marker)[0])
        self.assertEqual(s.replace('False -> lo < 256', 'lo < 256').replace('Hfalse Hlo Hhi', 'Hlo Hhi'), self.source)

    def test_probe_exposes_actual_guards_and_open_suffix(self):
        for abbreviation in ['V293_guard_cell', 'V293_OSSched_guards interrupt',
                             'V293_prefix_frame', 'V293_prefix_output', 'V293_OSSched_unlocked_prefix sched_id']:
            self.assertNotIn(abbreviation, GUARDS.PROBE)
        self.assertIn('InfRules Spec sd li I r ri mid suffix q tid', GUARDS.PROBE)
        self.assertIn('evar lock', GUARDS.PROBE)
        self.assertIn('Definition checked_guarded_witness : forall ni nl,', GUARDS.PROBE)
        skip = GUARDS.PROBE.split('Definition checked_interrupt_skip')[1].split('Definition checked_guards')[0]
        self.assertNotIn('checked_guard_cell lock', skip)
        self.assertNotIn('-> InfRules', skip)

    def test_code_and_proof_commands_have_distinct_identities(self):
        labels = [GUARDS.unit_label(f) for f in GUARDS.FILES]
        self.assertEqual(len(labels), len(set(labels)))
        self.assertNotEqual(GUARDS.unit_label(GUARDS.CODE), GUARDS.unit_label(GUARDS.CORE))
