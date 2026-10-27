"""Prospective single-factor mutations for current/target source linkage."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / name)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


CURRENT = load('v293-scheduler-current.py')
CALLER = load('v293-scheduler-caller.py')


class CurrentMutationTests(unittest.TestCase):
    def setUp(self):
        self.core = (ROOT / CURRENT.CORE).read_text()
        self.witness = (ROOT / CURRENT.WITNESS).read_text()
        self.mutants = CURRENT.mutations(self.core, self.witness, CALLER.replace_once)

    def inverse(self, label, old, new, witness=False):
        core, wit, _, _ = self.mutants[label]
        if witness:
            self.assertEqual(core, self.core)
            self.assertNotEqual(wit, self.witness)
            self.assertEqual(wit.replace(new, old), self.witness)
        else:
            self.assertEqual(wit, self.witness)
            self.assertNotEqual(core, self.core)
            self.assertEqual(core.replace(new, old), self.core)

    def test_controls_are_complete_and_nontrivial(self):
        self.assertEqual(set(self.mutants), set(CURRENT.CONTROLS))
        for core, witness, _, _ in self.mutants.values():
            self.assertNotEqual((core, witness), (self.core, self.witness))

    def test_only_target_equality_changes(self):
        self.inverse('target_equality_inverted_only', '(next = current <->', '(next <> current <->')

    def test_only_target_pointer_permission_changes(self):
        self.inverse('target_output_read_permission_only',
            'V293_prefix_output tp bo (Vptr next) ==>',
            'Amapsto (bo, 0%Z) (Tptr tp) false (Vptr next) ==>')

    def test_only_spatial_table_is_removed(self):
        self.inverse('target_abstract_table_removed_only',
                     's |= Aabsdata abstcblsid (abstcblist tasks) **', 's |= Aemp **')

    def test_only_blocked_current_claim_is_changed(self):
        self.inverse('blocked_current_forced_ready_only',
            'get V293_current_tasks V293_idle_tid =\n    Some (Int.repr 4, wait os_stat_time Int.one, Vnull)',
            'get V293_current_tasks V293_idle_tid =\n    Some (Int.repr 4, rdy, Vnull)', witness=True)

    def test_false_premise_only_adds_unused_argument(self):
        core, wit, _, declaration = self.mutants['current_prefix_false_premise_added_only']
        core = core.replace('  False -> lo < 256 -> hi < 256 ->', '  lo < 256 -> hi < 256 ->')
        core = core.replace('    Hli Hfalse Hlo Hhi Hr Hb', '    Hli Hlo Hhi Hr Hb')
        self.assertEqual(core, self.core)
        self.assertEqual(wit, self.witness)
        self.assertEqual(declaration, 'Definition checked_guarded_current :')

    def test_probe_preserves_blocked_fixture_and_no_false_premise(self):
        self.assertIn('wait os_stat_time Int.one', CURRENT.PROBE)
        self.assertIn('AHprio checked_scheduler next', CURRENT.PROBE)
        self.assertIn('GV target @ (Tptr p) |-> (Vptr next)', CURRENT.PROBE)
        self.assertNotIn('False ->', CURRENT.PROBE)
        self.assertNotIn('V293_current_mode_tasks', CURRENT.PROBE)
        self.assertNotIn('V293_current_mode_entries', CURRENT.PROBE)

    def test_stage_does_not_claim_whole_switch_or_coverage(self):
        self.assertIn('NOT_SWPRE_OR_GOOD_OS', CURRENT.SCOPE)
        self.assertEqual(len(CURRENT.ROOTS), 4)
