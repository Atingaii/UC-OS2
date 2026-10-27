"""Independent enabled-completion contracts and single-factor controls."""
import copy
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]


def load(root, name):
    spec = importlib.util.spec_from_file_location(name, root / 'scripts' / name)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


FINISH = load(ROOT, 'v293-scheduler-dispatch-finish.py')
CALLER = load(ROOT, 'v293-scheduler-caller.py')


class DispatchFinishTests(unittest.TestCase):
    def setUp(self):
        self.core = (ROOT / FINISH.CORE).read_text()
        self.witness = (ROOT / FINISH.WITNESS).read_text()
        self.variants = FINISH.mutations(self.core, self.witness, CALLER.replace_once)
        self.probe = FINISH.contract(load, ROOT)

    def test_exact_four_nontrivial_controls(self):
        self.assertEqual(len(self.variants), 4)
        self.assertEqual(set(self.variants), set(FINISH.OBLIGATIONS))
        self.assertEqual(set(self.variants), set(FINISH.CONTROLS))
        for c, w, _, _ in self.variants.values():
            self.assertNotEqual(c, self.core)
            self.assertEqual(w, self.witness)

    def test_only_equal_finish_post_action_changes(self):
        c, _, _, _ = self.variants['equal_pending_post_only']
        self.assertEqual(c.replace('(tail c) (resumed (sched;;aop) c) tid.',
                                   '(tail c) (resumed aop c) tid.'), self.core)

    def test_only_counter_condition_changes(self):
        c, _, _, _ = self.variants['counter_condition_inverted_only']
        self.assertEqual(c.replace('if negb (Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc)',
                                   'if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc'), self.core)

    def test_only_final_guard_false_premise_and_introduction_change(self):
        c, _, _, _ = self.variants['guard_false_premise_only']
        self.assertEqual(c.replace('  False -> lo < 256', '  lo < 256')
                         .replace('nc c Hfalse Hlo Hhi', 'nc c Hlo Hhi'), self.core)
        self.assertNotIn('False ->', FINISH.PROBE)

    def test_only_final_guard_entry_action_changes(self):
        c, _, _, _ = self.variants['guard_entry_action_only']
        start = self.core.index('Theorem V293_OSSched_guarded_dispatch_finish :')
        self.assertEqual(c[:start], self.core[:start])
        self.assertEqual(c[start:].replace('V293_shared_li tid aop',
                                          'V293_shared_li tid (sched;;aop)'), self.core[start:])

    def test_all_six_roots_have_fixed_contracts(self):
        self.assertEqual(len(FINISH.ROOTS), 6)
        for name in FINISH.ROOTS:
            self.assertIn('Definition checked_' + name + ' :', FINISH.PROBE)
            self.assertIn('eapply ' + name + '; eassumption. Qed.', FINISH.PROBE)

    def test_resource_expected_types_not_candidate_assertions(self):
        for name in ['V293_dispatch_self_resources ', 'V293_dispatch_completed_counter ',
                     'V293_dispatch_tail ', 'V293_dispatch_resumed ',
                     'V293_dispatch_locals ', 'V293_dispatch_prefix_pre ', 'V293_switch_resume ']:
            self.assertNotIn(name, self.probe)
        self.assertIn('frame ** Atrue', self.probe)
        self.assertIn('checked_switch_resume target tp tid aop', FINISH.PROBE)

    def test_both_enabled_branches_use_one_resumed_action(self):
        self.assertIn('(resumed aop (checked_completed_counter c)) tid.', FINISH.PROBE)
        self.assertIn('nc then c else Int.add c Int.one.', FINISH.PROBE)
        self.assertIn('(tail c) (resumed aop c) tid.', FINISH.PROBE)

    def test_disabled_branch_retains_full_pending_entry(self):
        self.assertIn('if Nat.eqb ni 0 && Nat.eqb nl 0 then post else pre', FINISH.PROBE)
        self.assertIn('V293_shared_li tid (sched;;aop)', FINISH.PROBE)

    def test_locked_counterexample_has_complete_same_state_entry(self):
        witness = FINISH.PROBE[FINISH.PROBE.index('Definition checked_V293_locked_dispatch_deferred_witness'):]
        self.assertIn('forall c events now aop, exists s,', witness)
        self.assertIn('s |= checked_lent_pre ', witness)
        self.assertIn('V293_guard_cell 109%Z 12%positive 1', witness)
        self.assertIn('V293_current_mode_tasks true', witness)
        self.assertIn('~ sched_self V293_scheduler (getabst s)', witness)

    def test_reuses_literal_full_entry_witness_for_both_modes(self):
        self.assertIn('checked_V293_dispatch_full_precondition_witness : forall different ni nl c events now aop,', self.probe)
        self.assertIn('V293_shared_li V293_idle_tid (sched;;aop)', self.probe)

    def test_actual_ast_and_no_suffix_oracle(self):
        self.assertNotIn('suffix', FINISH.PROBE)
        self.assertIn('(V293_OSSched_change high current counter (sprim (switch target)))', FINISH.PROBE)
        self.assertIn('V293_OSSched_unlocked_prefix sched_id table high target', FINISH.PROBE)

    def test_sources_and_checker_registered(self):
        for rel in FINISH.FILES:
            self.assertIn(rel, (ROOT / '_CoqProject').read_text().splitlines())
        gate = (ROOT / 'scripts/check-v293-functions.py').read_text()
        self.assertIn("'scripts/v293-scheduler-dispatch-finish.py'", gate)
        self.assertIn("report['scheduler_dispatch_finish_checkpoint'] = finish.check", gate)
        self.assertIn("report['scheduler_dispatch_finish_checkpoint'], checks, load", gate)

    def test_scope_does_not_claim_full_function_or_kernel(self):
        self.assertIn('DISABLED_DEFERS_NOT_FULL_OS_SCHED_OR_GOOD_OS', FINISH.SCOPE)
        for name in ['equal_pending_post_only', 'counter_condition_inverted_only', 'guard_entry_action_only']:
            self.assertIn('NOT_DOWNSTREAM_CREDIT', FINISH.CONTROLS[name])

    def test_designated_rejection_accepts_proof_but_not_unrelated_line(self):
        for label, (c, w, rel, decl) in self.variants.items():
            source = self.probe if rel is None else c if rel == FINISH.CORE else w
            for offset in [source.index(decl), source.index('Qed.', source.index(decl))]:
                line = source[:offset].count('\n') + 1
                file = rel or 'checks/Contract.v'
                row = dict(exit_code=1, stderr=f'File "/tmp/{file}", line {line}, characters 0-1:\nError: mismatch\n')
                FINISH.check_rejection(row, source, rel, decl, label)

    def test_success_timeout_wrong_file_line_or_warning_not_rejection(self):
        c, _, rel, decl = self.variants['equal_pending_post_only']
        line = c[:c.index(decl)].count('\n') + 2
        row = dict(exit_code=1, stderr=f'File "/tmp/{rel}", line {line}, characters 0-1:\nError: mismatch\n')
        for change in [dict(exit_code=0), dict(exit_code=124),
                       dict(stderr=row['stderr'].replace('Error:', 'Warning:')),
                       dict(stderr=row['stderr'].replace(rel, 'unrelated.v')),
                       dict(stderr=row['stderr'].replace(f'line {line}', 'line 1'))]:
            test = copy.deepcopy(row)
            test.update(change)
            with self.subTest(change=change), self.assertRaises(ValueError):
                FINISH.check_rejection(test, c, rel, decl, 'equal_pending_post_only')


if __name__ == '__main__':
    unittest.main()
