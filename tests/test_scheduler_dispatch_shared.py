"""Same ownership for the real guarded prefix and the actual switch boundary."""
import copy
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]

def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / name)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module

DISPATCH = load('v293-scheduler-dispatch-shared.py')
CALLER = load('v293-scheduler-caller.py')

class DispatchSharedTests(unittest.TestCase):
    def setUp(self):
        self.core = (ROOT / DISPATCH.CORE).read_text()
        self.witness = (ROOT / DISPATCH.WITNESS).read_text()
        self.variants = DISPATCH.mutations(self.core, self.witness, CALLER.replace_once)

    def test_exact_six_nontrivial_controls(self):
        self.assertEqual(len(self.variants), 6)
        self.assertEqual(set(self.variants), set(DISPATCH.CONTROLS))
        self.assertEqual(set(self.variants), set(DISPATCH.OBLIGATIONS))
        for core, witness, _, _ in self.variants.values():
            self.assertNotEqual((core, witness), (self.core, self.witness))

    def test_only_returned_time_changes(self):
        c, w, _, _ = self.variants['post_time_changed_only']
        self.assertEqual(w, self.witness)
        self.assertEqual(c.replace('events (Int.add now Int.one) next **', 'events now next **'), self.core)
        self.assertIn('Definition V293_dispatch_prefix_post ', c[:c.index('(Int.add now Int.one)')])

    def test_only_both_callee_selectors_in_prefix_change(self):
        c, w, _, _ = self.variants['callee_owns_dispatch_core_only']
        self.assertEqual(w, self.witness)
        self.assertEqual(c.count('li (V293_dispatch_inv target tp) Hli'), 2)
        self.assertEqual(c.replace('li (V293_dispatch_inv target tp) Hli', 'li V293_opened_inv Hli'), self.core)
        a = c.index('Theorem V293_OSSched_dispatch_prefix :'); b = c.index('Proof.', a)
        self.assertNotIn('li (V293_dispatch_inv target tp) Hli', c[:a] + c[b:])

    def test_only_returned_target_changes(self):
        c, w, _, _ = self.variants['target_returned_old_only']
        self.assertEqual(w, self.witness)
        self.assertEqual(c.replace('tasks events now tid **', 'tasks events now next **'), self.core)

    def test_only_guard_premise_and_intro_change(self):
        c, w, _, _ = self.variants['guard_false_premise_added_only']
        self.assertEqual(w, self.witness)
        self.assertEqual(c.replace('  False -> lo < 256', '  lo < 256')
            .replace('Hli Hfalse Hlo Hhi', 'Hli Hlo Hhi'), self.core)
        a = c.index('Theorem V293_OSSched_guarded_dispatch_prefix :')
        self.assertNotIn('False ->', c[:a])
        self.assertNotIn('False ->', DISPATCH.PROBE)

    def test_only_reused_fixture_time_changes(self):
        c, w, _, _ = self.variants['witness_stale_time_only']
        self.assertEqual(c, self.core)
        self.assertEqual(w.replace('different events (Int.add now Int.one))', 'different events now)'), self.witness)

    def test_only_disabled_branch_post_changes(self):
        c, w, _, _ = self.variants['disabled_guard_post_changed_only']
        self.assertEqual(w, self.witness)
        self.assertEqual(c.replace('then post else post) tid.', 'then post else pre) tid.'), self.core)

    def test_probe_has_literal_unique_fields_and_typed_shared_target(self):
        for slot in ['curtid', 'abstcblsid', 'absecblsid', 'ostmid']:
            self.assertIn('Aabsdata ' + slot, DISPATCH.PROBE)
        self.assertIn('EX v : val,', DISPATCH.PROBE)
        self.assertIn('rule_type_val_match (Tptr tp) v = true', DISPATCH.PROBE)
        self.assertIn('match k with O => checked_core target tp | S _ => Aemp end', DISPATCH.PROBE)
        for alias in ['V293_dispatch_entry ', 'V293_dispatch_snapshot ',
                      'V293_dispatch_prefix_pre ', 'V293_dispatch_prefix_post ']:
            self.assertNotIn(alias, DISPATCH.PROBE)
        self.assertIn('getinv (V293_opened_inv k) = Aemp', DISPATCH.PROBE)

    def test_probe_checks_guard_disabled_preservation_and_no_suffix(self):
        self.assertIn('then post else pre) tid :=', DISPATCH.PROBE)
        self.assertNotIn('suffix', DISPATCH.PROBE)
        self.assertIn('InfRules Spec sd li (V293_dispatch_inv target tp)', DISPATCH.PROBE)

    def test_complete_witness_has_both_modes_arbitrary_events_time_but_not_pending(self):
        self.assertIn('forall different es n, exists s,', DISPATCH.PROBE)
        self.assertIn('<-> different = true', DISPATCH.PROBE)
        self.assertIn('es n Aemp nil nil', DISPATCH.PROBE)
        self.assertIn('(spec_done None)', DISPATCH.PROBE)
        self.assertNotIn('pending scheduler action', self.witness)

    def test_bound_scope_and_early_rejections(self):
        self.assertEqual(len(DISPATCH.ROOTS), 5)
        self.assertIn('NOT_COMPARE_COUNTER_SWITCH_OR_GOOD_OS', DISPATCH.SCOPE)
        for label in ['post_time_changed_only', 'target_returned_old_only', 'callee_owns_dispatch_core_only']:
            self.assertEqual(DISPATCH.OBLIGATIONS[label][0], DISPATCH.CORE)
            self.assertIn('NOT_DOWNSTREAM_CREDIT', DISPATCH.CONTROLS[label])

    def test_registered_sources_checker_and_validator(self):
        for rel in DISPATCH.FILES:
            self.assertIn(rel, (ROOT / '_CoqProject').read_text().splitlines())
        g = (ROOT / 'scripts/check-v293-functions.py').read_text()
        self.assertIn("'scripts/v293-scheduler-dispatch-shared.py'", g)
        self.assertIn("report['scheduler_dispatch_shared_checkpoint'] = dispatch.check", g)
        self.assertIn("report['scheduler_dispatch_shared_checkpoint'], checks, load", g)

    def test_designated_location_is_accepted(self):
        for label, (core, witness, rel, decl) in self.variants.items():
            source = DISPATCH.PROBE if rel is None else core if rel == DISPATCH.CORE else witness
            line = source[:source.index(decl)].count('\n') + 2
            file = 'checks/Contract.v' if rel is None else rel
            row = dict(exit_code=1, stderr=f'File "/tmp/{file}", line {line}, characters 0-1:\nError: mismatch\n')
            DISPATCH.check_rejection(row, source, rel, decl, label)

    def test_wrong_exit_timeout_file_line_or_warning_cannot_pass(self):
        c, _, rel, decl = self.variants['post_time_changed_only']
        line = c[:c.index(decl)].count('\n') + 2
        row = dict(exit_code=1, stderr=f'File "/tmp/{rel}", line {line}, characters 0-1:\nError: mismatch\n')
        for change in [dict(exit_code=0), dict(exit_code=124),
            dict(stderr=row['stderr'].replace('Error:', 'Warning:')),
            dict(stderr=row['stderr'].replace(rel, 'other.v')),
            dict(stderr=row['stderr'].replace(f'line {line}', 'line 1'))]:
            test = copy.deepcopy(row); test.update(change)
            with self.subTest(change=change), self.assertRaises(ValueError):
                DISPATCH.check_rejection(test, c, rel, decl, 'post_time_changed_only')

    def test_guard_contract_range_includes_final_assignment_after_lets(self):
        label = 'guard_false_premise_added_only'
        _, _, rel, decl = self.variants[label]
        source = DISPATCH.PROBE
        line = source[:source.index('tid := V293_OSSched_guarded_dispatch_prefix.')].count('\n') + 1
        row = dict(exit_code=1, stderr=f'File "/tmp/checks/Contract.v", line {line}, characters 0-1:\nError: mismatch\n')
        DISPATCH.check_rejection(row, source, rel, decl, label)

if __name__ == '__main__':
    unittest.main()
