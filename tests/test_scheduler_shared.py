"""Unique table ownership and prospective, obligation-specific controls."""
import copy
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / name)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


SHARED = load('v293-scheduler-shared.py')
CALLER = load('v293-scheduler-caller.py')


class SharedPrefixTests(unittest.TestCase):
    def setUp(self):
        self.core = (ROOT / SHARED.CORE).read_text()
        self.witness = (ROOT / SHARED.WITNESS).read_text()
        self.variants = SHARED.mutations(self.core, self.witness, CALLER.replace_once)

    def test_four_controls_are_exact_and_nontrivial(self):
        self.assertEqual(set(self.variants), set(SHARED.CONTROLS))
        self.assertEqual(set(self.variants), set(SHARED.OBLIGATIONS))
        for c, w, _, _ in self.variants.values():
            self.assertNotEqual((c, w), (self.core, self.witness))

    def test_time_control_only_changes_returned_snapshot(self):
        c, w, _, _ = self.variants['post_time_changed_only']
        self.assertEqual(w, self.witness)
        self.assertEqual(c.replace('events (Int.add now Int.one) **', 'events now **'), self.core)
        self.assertIn('V293_shared_prefix_post', c[:c.index('(Int.add now Int.one)')])

    def test_callee_control_changes_only_both_spec_selectors(self):
        c, w, _, _ = self.variants['callee_owns_shared_core_only']
        self.assertEqual(w, self.witness)
        self.assertEqual(c.count('li V293_shared_inv Hli'), 2)
        self.assertEqual(c.replace('li V293_shared_inv Hli', 'li V293_opened_inv Hli'), self.core)
        a = c.index('Theorem V293_OSSched_shared_prefix :'); b = c.index('Proof.', a)
        self.assertNotIn('li V293_shared_inv Hli', c[:a] + c[b:])

    def test_witness_control_removes_only_time_singleton(self):
        c, w, _, _ = self.variants['witness_time_slot_removed_only']
        self.assertEqual(c, self.core)
        self.assertEqual(w.replace('(emp : osabst)', '(sig ostmid (ostm n))'), self.witness)

    def test_false_control_changes_only_argument_and_introduction(self):
        c, w, _, _ = self.variants['prefix_false_premise_added_only']
        self.assertEqual(w, self.witness)
        self.assertEqual(c.replace('  False -> lo < 256', '  lo < 256')
                         .replace('Hli Hfalse Hlo Hhi', 'Hli Hlo Hhi'), self.core)
        self.assertNotIn('False ->', SHARED.PROBE)

    def test_probe_has_fixed_ownership_and_returned_time(self):
        for slot in ['curtid', 'abstcblsid', 'absecblsid', 'ostmid']:
            self.assertIn('Aabsdata ' + slot, SHARED.PROBE)
        self.assertIn('SWINV V293_shared_inv //\\', SHARED.PROBE)
        self.assertNotIn('V293_shared_prefix_pre ', SHARED.PROBE)
        self.assertNotIn('V293_shared_prefix_post ', SHARED.PROBE)
        self.assertNotIn('V293_shared_snapshot ', SHARED.PROBE)
        self.assertIn('getinv (V293_opened_inv k) = Aemp', SHARED.PROBE)
        self.assertIn(') sd li RI :=', SHARED.PROBE)

    def test_both_modes_arbitrary_events_time_have_same_complete_pre(self):
        self.assertIn('forall different es n, exists s,', SHARED.PROBE)
        self.assertIn('<-> different = true', SHARED.PROBE)
        self.assertIn('es n Aemp Vnull nil nil', SHARED.PROBE)

    def test_no_downstream_credit_or_full_kernel_claim(self):
        self.assertIn('NOT_SWITCH_OR_PHYSICAL_KERNEL_OR_GOOD_OS', SHARED.SCOPE)
        self.assertEqual(len(SHARED.ROOTS), 5)
        for label in ['post_time_changed_only', 'callee_owns_shared_core_only']:
            self.assertEqual(SHARED.OBLIGATIONS[label][0], SHARED.CORE)

    def test_new_modules_and_checker_are_active(self):
        for path in SHARED.FILES:
            self.assertIn(path, (ROOT / '_CoqProject').read_text().splitlines())
        gate = (ROOT / 'scripts/check-v293-functions.py').read_text()
        self.assertIn("'scripts/v293-scheduler-shared.py'", gate)
        self.assertIn("report['scheduler_shared_checkpoint'] = shared_prefix.check", gate)
        self.assertIn("report['scheduler_shared_checkpoint'], checks, load", gate)

    def row(self):
        label = 'post_time_changed_only'
        c, _, rel, decl = self.variants[label]
        line = c[:c.index(decl)].count('\n') + 2
        row = dict(exit_code=1, stdout='', stderr=f'File "/tmp/isolation/{rel}", line {line}, characters 0-1:\nError: mismatch\n')
        return c, rel, decl, label, row

    def test_designated_rejection_is_accepted(self):
        c, rel, decl, label, row = self.row()
        SHARED.check_rejection(row, c, rel, decl, label)

    def test_wrong_location_file_exit_and_non_error_are_rejected(self):
        c, rel, decl, label, row = self.row()
        changes = [dict(exit_code=0), dict(exit_code=124), dict(stderr=row['stderr'].replace('Error:', 'Warning:')),
                   dict(stderr=row['stderr'].replace(rel, 'other.v')),
                   dict(stderr=row['stderr'].replace('line ' + str(c[:c.index(decl)].count('\n') + 2), 'line 1'))]
        for change in changes:
            candidate = copy.deepcopy(row); candidate.update(change)
            with self.subTest(change=change), self.assertRaises(ValueError):
                SHARED.check_rejection(candidate, c, rel, decl, label)


if __name__ == '__main__':
    unittest.main()
