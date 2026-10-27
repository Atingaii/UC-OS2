"""Normal-switch ownership and prospective, single-factor rejection controls."""
import copy
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / name)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module
SWITCH = load('v293-scheduler-switch.py')
CALLER = load('v293-scheduler-caller.py')

class NormalSwitchTests(unittest.TestCase):
    def setUp(self):
        self.triple = tuple((ROOT / p).read_text() for p in SWITCH.FILES)
        self.variants = SWITCH.mutations(*self.triple, CALLER.replace_once)

    def test_five_controls_are_exact_and_nontrivial(self):
        self.assertEqual(set(self.variants), set(SWITCH.CONTROLS))
        self.assertEqual(set(self.variants), set(SWITCH.OBLIGATIONS))
        for label, (*triple, rel, decl) in self.variants.items():
            with self.subTest(label=label):
                self.assertEqual(sum(a != b for a,b in zip(triple,self.triple)),1)
                self.assertEqual((rel,decl),SWITCH.OBLIGATIONS[label])

    def test_resume_control_only_changes_post_action(self):
        state,core,witness,*_ = self.variants['resumed_action_pending_only']
        self.assertEqual(state,self.triple[0]); self.assertEqual(witness,self.triple[2])
        self.assertEqual(core.replace('<||sched;;aop||> ** SWINVt','<||aop||> ** SWINVt'),self.triple[1])

    def test_half_control_only_removes_reserved_half(self):
        _,core,_,*_ = self.variants['reserved_current_half_removed_only']
        self.assertEqual(core.replace('next ** Aemp) **','next ** CurTid tid) **'),self.triple[1])

    def test_false_control_only_changes_premise_and_intro(self):
        _,core,_,*_ = self.variants['switch_false_premise_added_only']
        self.assertEqual(core.replace('  False -> indom tasks tid','  indom tasks tid')
                         .replace('px Hfalse Hmember','px Hmember'),self.triple[1])
        self.assertNotIn('False ->',SWITCH.PROBE)

    def test_pending_control_only_changes_actual_witness_state(self):
        _,_,witness,*_ = self.variants['witness_pending_action_removed_only']
        self.assertEqual(witness.replace('O, aop) : RstateOP).','O, (sched;;aop)) : RstateOP).'),self.triple[2])

    def test_full_view_control_does_not_change_inv(self):
        state,_,_,*_ = self.variants['full_view_target_cell_omitted_only']
        a=state.index('Definition V293_dispatch_full ')
        self.assertEqual(state[:a],self.triple[0][:self.triple[0].index('Definition V293_dispatch_full ')])
        self.assertEqual(state.replace('Definition V293_dispatch_full (target : var) (tp : type) t :=',
                         'Definition V293_dispatch_full target tp t :=')
            .replace('(V293_shared_fields t ts es n ** Aemp).',
                     '(V293_shared_fields t ts es n ** V293_dispatch_cell target tp).'),self.triple[0])

    def test_probe_fixes_slots_target_and_inv_shape(self):
        for slot in ['curtid','abstcblsid','absecblsid','ostmid']:
            self.assertIn('Aabsdata '+slot,SWITCH.PROBE)
        self.assertIn('rule_type_val_match (Tptr tp) v = true',SWITCH.PROBE)
        self.assertIn('getinv (V293_dispatch_inv target tp k)',SWITCH.PROBE)
        self.assertIn('O => checked_core target tp | S _ => Aemp',SWITCH.PROBE)
        self.assertNotIn('V293_switch_payload ',SWITCH.PROBE)
        self.assertNotIn('V293_dispatch_snapshot ',SWITCH.PROBE)
        self.assertNotIn('V293_switch_resume ',SWITCH.PROBE)

    def test_probe_fixes_actual_primitive_and_resumed_thread(self):
        self.assertIn('(sprim (switch target))',SWITCH.PROBE)
        self.assertIn('<||sched;;aop||> ** ((checked_snapshot',SWITCH.PROBE)
        self.assertIn('(<||aop||> ** SWINVt (V293_dispatch_inv target tp) t',SWITCH.PROBE)
        self.assertNotIn('suffix',SWITCH.PROBE)

    def test_both_cases_have_arbitrary_continuation_events_time(self):
        self.assertIn('forall different events now aop, exists s,',SWITCH.PROBE)
        self.assertIn('wait os_stat_time Int.one',SWITCH.PROBE)
        self.assertIn('aop nil nil ** Aemp',SWITCH.PROBE)

    def test_no_downstream_credit_or_source_caller_claim(self):
        self.assertIn('NOT_SOURCE_CALLER_OR_PHYSICAL_KERNEL_OR_GOOD_OS',SWITCH.SCOPE)
        self.assertEqual(len(SWITCH.ROOTS),8)
        self.assertIn('NOT_DOWNSTREAM_CREDIT',SWITCH.CONTROLS['reserved_current_half_removed_only'])
        self.assertIn('NOT_DOWNSTREAM_CREDIT',SWITCH.CONTROLS['full_view_target_cell_omitted_only'])

    def test_all_modules_and_checker_active(self):
        for path in SWITCH.FILES:
            self.assertIn(path,(ROOT/'_CoqProject').read_text().splitlines())
        gate=(ROOT/'scripts/check-v293-functions.py').read_text()
        self.assertIn("'scripts/v293-scheduler-switch.py'",gate)
        self.assertIn("report['scheduler_switch_checkpoint'] = normal_switch.check",gate)
        self.assertIn("report['scheduler_switch_checkpoint'], checks, load",gate)

    def row(self):
        label='reserved_current_half_removed_only'
        _,core,_,rel,decl=self.variants[label]
        line=core[:core.index(decl)].count('\n')+2
        row=dict(exit_code=1,stdout='',stderr=f'File "/tmp/isolated/{rel}", line {line}, characters 0-1:\nError: mismatch\n')
        return core,rel,decl,label,row

    def test_designated_rejection_accepted(self):
        core,rel,decl,label,row=self.row()
        SWITCH.check_rejection(row,core,rel,decl,label)

    def test_wrong_exit_line_file_and_non_error_rejected(self):
        core,rel,decl,label,row=self.row()
        import re
        changes=[dict(exit_code=0),dict(exit_code=124),dict(stderr=row['stderr'].replace('Error:','Warning:')),
                 dict(stderr=row['stderr'].replace(rel,'unrelated.v')),
                 dict(stderr=re.sub(r'line \d+,','line 1,',row['stderr']))]
        for change in changes:
            candidate=copy.deepcopy(row); candidate.update(change)
            with self.subTest(change=change),self.assertRaises(ValueError):
                SWITCH.check_rejection(candidate,core,rel,decl,label)

if __name__=='__main__': unittest.main()
