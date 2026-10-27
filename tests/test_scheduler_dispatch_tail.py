"""Literal ordinary-switch chain contracts and prospective single-factor controls."""
import copy
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]

def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / name)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module

TAIL = load('v293-scheduler-dispatch-tail.py')
CALLER = load('v293-scheduler-caller.py')

class DispatchTailTests(unittest.TestCase):
    def setUp(self):
        self.core = (ROOT / TAIL.CORE).read_text()
        self.witness = (ROOT / TAIL.WITNESS).read_text()
        self.variants = TAIL.mutations(self.core, self.witness, CALLER.replace_once)

    def test_exact_six_nontrivial_controls(self):
        self.assertEqual(len(self.variants), 6)
        self.assertEqual(set(self.variants), set(TAIL.CONTROLS))
        self.assertEqual(set(self.variants), set(TAIL.OBLIGATIONS))
        for core, witness, _, _ in self.variants.values():
            self.assertNotEqual((core, witness), (self.core, self.witness))

    def test_only_counter_post_changes(self):
        c, w, _, _ = self.variants['counter_post_two_only']
        self.assertEqual(w, self.witness)
        self.assertEqual(c.replace('(V293_dispatch_tail (Int.add c (Int.repr 2)))',
                                   '(V293_dispatch_tail (Int.add c Int.one))'), self.core)
        self.assertEqual(c.count('Int.repr 2'), 1)

    def test_only_resumed_action_changes(self):
        c, w, _, _ = self.variants['resumed_pending_action_only']
        self.assertEqual(w, self.witness)
        self.assertEqual(c.replace('tp tid (sched;;aop) stack critical',
                                   'tp tid aop stack critical'), self.core)

    def test_only_branch_polarity_changes(self):
        c, w, _, _ = self.variants['branch_condition_inverted_only']
        self.assertEqual(w, self.witness)
        self.assertEqual(c.replace('if negb (Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc)',
                                   'if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc'), self.core)

    def test_only_final_chain_false_premise_and_intro_change(self):
        c, w, _, _ = self.variants['guard_false_premise_only']
        self.assertEqual(w, self.witness)
        self.assertEqual(c.replace('  False -> lo < 256', '  lo < 256')
            .replace('nc c Hfalse Hlo Hhi', 'nc c Hlo Hhi'), self.core)
        self.assertNotIn('False ->', TAIL.PROBE)

    def test_only_actual_witness_action_changes(self):
        c, w, _, _ = self.variants['witness_pending_removed_only']
        self.assertEqual(c, self.core)
        self.assertEqual(w.replace('(false, nil, nil), O, aop) : RstateOP)',
                                   '(false, nil, nil), O, (sched;;aop)) : RstateOP)'), self.witness)
        # The expected entry is still pending; only the constructed state changes.
        self.assertIn('V293_shared_li V293_idle_tid (sched;;aop)', w)

    def test_reserved_half_neutralization_preserves_rest_and_output(self):
        c, w, _, _ = self.variants['reserved_half_neutralized_only']
        self.assertEqual(w, self.witness)
        a = c.index('(* This frame'); b = self.core.index('(* This frame')
        self.assertEqual(c[a:], self.core[b:])
        changed = c[c.index('Definition V293_dispatch_tail c :='):a]
        self.assertIn('(LINV V293_shared_li tid nil ** Atrue)', changed)
        self.assertNotIn('CurLINV ', changed)
        for resource in ['V293_dispatch_snapshot', 'Aie false', 'Ais stack', 'Acs critical',
                         'V293_sched_globals', 'V293_sched_inputs', 'PV (bh, Int.zero)',
                         'V293_prefix_bindings', 'V293_read_pointers', 'V293_guard_cell', 'V293_counter_cell']:
            self.assertIn(resource, changed)
        self.assertIn('V293_switch_payload target tp tid tasks events now next aop', c[a:])

    def test_probe_literal_assertions_not_candidate_aliases(self):
        for name in ['V293_dispatch_tail ', 'V293_dispatch_resumed ', 'V293_dispatch_locals ',
                     'V293_dispatch_changed_post ', 'V293_dispatch_prefix_pre ',
                     'V293_dispatch_prefix_post ', 'V293_switch_payload ', 'V293_switch_resume ']:
            self.assertNotIn(name, TAIL.PROBE)
        self.assertIn('<||aop||> ** SWINVt', TAIL.PROBE)
        self.assertIn('** CurTid tid)', TAIL.PROBE)
        self.assertIn('frame ** Atrue', TAIL.PROBE)

    def test_probe_checks_all_new_roots(self):
        self.assertEqual(len(TAIL.ROOTS), 9)
        for name in TAIL.ROOTS:
            self.assertIn('Definition checked_' + name + ' :', TAIL.PROBE)
            self.assertIn('eapply ' + name + '; eassumption. Qed.', TAIL.PROBE)

    def test_no_suffix_oracle_or_shared_value_freeze_in_resume(self):
        self.assertNotIn('suffix', TAIL.PROBE)
        a = TAIL.PROBE.index('Definition checked_switch_resume ')
        b = TAIL.PROBE.index('Section CheckedDispatchTail.', a)
        resume = TAIL.PROBE[a:b]
        for value in ['tasks', 'events', 'now', 'next']:
            self.assertNotIn(value, resume)
        self.assertIn('(sprim (switch target))', TAIL.PROBE)

    def test_witness_both_modes_arbitrary_guards_counter_events_time_action(self):
        self.assertIn('forall different ni nl c events now aop,', TAIL.PROBE)
        self.assertIn('<-> different = true', TAIL.PROBE)
        self.assertIn('V293_shared_li V293_idle_tid (sched;;aop)', TAIL.PROBE)
        for item in ['108%Z 11%positive ni', '109%Z 12%positive nl',
                     '110%Z 13%positive', '111%Z 14%positive c']:
            self.assertIn(item, TAIL.PROBE)
        self.assertNotIn('c <> Int.repr', TAIL.PROBE)

    def test_guard_disabled_preserves_complete_pending_entry(self):
        self.assertIn('if Nat.eqb ni 0 && Nat.eqb nl 0 then post else pre', TAIL.PROBE)
        self.assertIn('then checked_dispatch_tail c else checked_dispatch_resumed (Int.add c Int.one)', TAIL.PROBE)

    def test_scope_and_early_rejections_are_bounded(self):
        self.assertIn('NOT_PORT_CORRESPONDENCE_OR_GOOD_OS', TAIL.SCOPE)
        for label in ['counter_post_two_only', 'resumed_pending_action_only',
                      'branch_condition_inverted_only', 'reserved_half_neutralized_only']:
            self.assertIn('NOT_DOWNSTREAM_CREDIT', TAIL.CONTROLS[label])

    def test_registered_sources_checker_and_validator(self):
        for rel in TAIL.FILES:
            self.assertIn(rel, (ROOT / '_CoqProject').read_text().splitlines())
        g = (ROOT / 'scripts/check-v293-functions.py').read_text()
        self.assertIn("'scripts/v293-scheduler-dispatch-tail.py'", g)
        self.assertIn("report['scheduler_dispatch_tail_checkpoint'] = tail.check", g)
        self.assertIn("report['scheduler_dispatch_tail_checkpoint'], checks, load", g)

    def test_designated_file_line_is_accepted_including_proof(self):
        for label, (c, w, rel, decl) in self.variants.items():
            source = TAIL.PROBE if rel is None else c if rel == TAIL.CORE else w
            for offset in [source.index(decl), source.index('Qed.', source.index(decl))]:
                line = source[:offset].count('\n') + 1
                file = 'checks/Contract.v' if rel is None else rel
                row = dict(exit_code=1, stderr=f'File "/tmp/{file}", line {line}, characters 0-1:\nError: mismatch\n')
                TAIL.check_rejection(row, source, rel, decl, label)

    def test_success_timeout_wrong_file_line_or_warning_not_rejection(self):
        c, _, rel, decl = self.variants['counter_post_two_only']
        line = c[:c.index(decl)].count('\n') + 2
        row = dict(exit_code=1, stderr=f'File "/tmp/{rel}", line {line}, characters 0-1:\nError: mismatch\n')
        for change in [dict(exit_code=0), dict(exit_code=124),
            dict(stderr=row['stderr'].replace('Error:', 'Warning:')),
            dict(stderr=row['stderr'].replace(rel, 'unrelated.v')),
            dict(stderr=row['stderr'].replace(f'line {line}', 'line 1'))]:
            test = copy.deepcopy(row); test.update(change)
            with self.subTest(change=change), self.assertRaises(ValueError):
                TAIL.check_rejection(test, c, rel, decl, 'counter_post_two_only')

if __name__ == '__main__':
    unittest.main()
