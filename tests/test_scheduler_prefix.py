"""Prospective single-factor mutations must alter only their intended seam."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]

def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / name)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module

PREFIX = load('v293-scheduler-prefix.py')
CALLER = load('v293-scheduler-caller.py')


class PrefixMutationTests(unittest.TestCase):
    def setUp(self):
        self.original = (ROOT / PREFIX.CORE).read_text()
        self.mutants = PREFIX.mutations(self.original, CALLER.replace_once)

    def test_control_set_is_exact_and_source_remains_unchanged(self):
        self.assertEqual(set(self.mutants), set(PREFIX.CONTROLS))
        self.assertEqual(self.original, (ROOT / PREFIX.CORE).read_text())

    def test_load_mutation_only_changes_selected_read_conclusion(self):
        mutant, target = self.mutants['selected_load_changed_only']
        self.assertEqual(target, 'Lemma V293_prefix_selected_load')
        self.assertEqual(mutant.replace('Some (V293_byteval (S (V293_ready_select lo hi (V293_ready_group lo hi)))).',
                                       'Some (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))).'), self.original)

    def test_permission_mutation_only_changes_output_permission(self):
        mutant, target = self.mutants['output_write_permission_removed_only']
        self.assertEqual(target, 'Theorem V293_OSSched_target_assign')
        self.assertEqual(mutant.replace('Definition V293_prefix_output tp bo v := Amapsto (bo, 0%Z) (Tptr tp) false v.',
                                       'Definition V293_prefix_output tp bo v := Amapsto (bo, 0%Z) (Tptr tp) true v.'), self.original)

    def test_order_mutation_keeps_old_source_emission_and_assignment(self):
        mutant, target = self.mutants['statement_order_reversed_only']
        self.assertEqual(target, 'Theorem V293_OSSched_unlocked_prefix_hoare')
        self.assertEqual(mutant.replace('(sseq (V293_OSSched_target_update table high target) (scall sched_id nil))\n',
                                       '(V293_OSSched_unlocked_prefix sched_id table high target)\n'), self.original)
        self.assertEqual((ROOT / CALLER.CODE).read_text(), CALLER.EMISSION)

    def test_false_premise_does_not_modify_prior_assignment_or_witness(self):
        mutant, target = self.mutants['prefix_false_premise_added_only']
        self.assertEqual(target, 'Definition checked_prefix :')
        marker = 'Theorem V293_OSSched_unlocked_prefix_hoare'
        self.assertEqual(mutant.split(marker)[0], self.original.split(marker)[0])
        self.assertEqual(mutant.replace('False -> lo < 256', 'lo < 256').replace('Hli Hfalse Hlo', 'Hli Hlo'), self.original)

    def test_fixed_probe_does_not_use_tested_prefix_abbreviations(self):
        for symbol in ['V293_prefix_frame', 'V293_prefix_output', 'V293_OSSched_unlocked_prefix sched_id',
                       'V293_OSSched_target_update table']:
            self.assertNotIn(symbol, PREFIX.PROBE)
        self.assertIn('sseq (scall sched_id nil)', PREFIX.PROBE)
        self.assertIn('checked_prefix_output tp bo v := Amapsto (bo, 0%Z) (Tptr tp) true v.', PREFIX.PROBE)
