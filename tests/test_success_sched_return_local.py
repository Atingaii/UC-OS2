"""Structural and frozen-evidence checks; actual Coq executions live in gate04."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT/'certiucos/v293/proofs/V293CriticalReturn.v'
LOG = ROOT/'audit/logs/stage26-success-sched-return'


def gate():
    spec = importlib.util.spec_from_file_location('success_sched_return_gate', ROOT/'scripts/check-v293-success-sched-return.py')
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def section(name):
    text = SOURCE.read_text()
    i = text.index(name+' :')
    return text[i:text.index('\nQed.', i)+6]


class SuccessSchedReturn(unittest.TestCase):
    def test_previous_1934_lines_are_byte_exact(self):
        old = (LOG/'V293CriticalReturn.before.v.snapshot.txt').read_bytes()
        self.assertEqual(len(old), 123526)
        self.assertEqual(old.count(b'\n'), 1934)
        self.assertEqual(hashlib.sha256(old).hexdigest(), gate().PREFIX_SHA)
        self.assertTrue(SOURCE.read_bytes().startswith(old))

    def test_no_new_proof_oracle(self):
        bare = re.sub(r'\(\*.*?\*\)', '', SOURCE.read_text(), flags=re.S)
        self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture)\b', bare))
        for name in [gate().CALL, gate().SCHEDULE, gate().TAIL]:
            header = section(name).split('Proof.', 1)[0]
            pre = header.split('V293_local_steps P', 1)[0]
            for forbidden in ['cstepstar', 'loststep', 'store Tint32', 'free Tint32', 'fresh M']:
                self.assertNotIn(forbidden, pre)

    def test_scheduler_ast_keeps_full_unlocked_body(self):
        s = SOURCE.read_text().split('Definition V293_OSSched_success_body ', 1)[1].split('Definition V293_task_prio_running ', 1)[0]
        for item in ['sassign (evar saved) (econst32 Int.zero)', '(sprim encrit)',
                     'V293_OSSched_guards interrupt lock', 'V293_OSSched_unlocked_prefix schednew table high target',
                     'V293_OSSched_change high current counter', '(sprim (switch target))', '(sprim excrit) sret',
                     '(Tvoid,dnil,dcons saved Tint32 dnil,']:
            self.assertIn(item, s)

    def test_real_call_alloc_initialization_guard_exit_free_restore(self):
        proof = section(gate().CALL).split('Proof.', 1)[1]
        for item in ['memory_has_fresh_block M', 'V293_success_scheduler_storage', 'snpcall_step',
                     'sfexec_step', 'salloclv_step', 'sallocend_step', 'V293_success_assign_zero',
                     'apply encrit_step', 'V293_success_sched_guard_skip', 'apply excrit_step',
                     'sret_step', 'sfree_step', 'sfreeend_step']:
            self.assertIn(item, proof)
        header = section(gate().CALL).split('Proof.', 1)[0]
        self.assertEqual(header.count('((ge,caller,M),ir,(enabled,si,ci))'), 2)
        self.assertNotIn('bs', header)

    def test_storage_is_constructed_and_returns_original_memory(self):
        s = section('V293_success_scheduler_storage')
        for item in ['free Tint32 bs Ms = Some M', 'V293_storebytes_exists', 'V293_freeb_construct',
                     'HalfPermMap.extensionality', 'V293_success_fresh_none']:
            self.assertIn(item, s)

    def test_nonrunning_resources_are_conditional_and_isr_needs_no_lock(self):
        h = section(gate().SCHEDULE).split('Proof.', 1)[0]
        self.assertLess(h.index('(run = 1 ->'), h.index('P sched = Some'))
        self.assertIn('Some (V293_byteval run)', h)
        blocked = SOURCE.read_text().split('Definition V293_success_sched_blocked ', 1)[1].split('Lemma V293_success_sched_guard_skip ', 1)[0]
        self.assertLess(blocked.index('ni <> 0 \\/ exists bl nl'), blocked.index('get ge lock'))

    def test_original_memory_roots_construct_updates_before_actual_schedule(self):
        for kind in ['null', 'event']:
            s = section('V293_critical_'+kind+'_schedule_execution')
            h,p = s.split('Proof.', 1)
            pre = h.split('exists Mg,', 1)[0]
            for unwanted in ['cstepstar', 'V293_local_steps', 'storebytes', 'free Tint32']:
                self.assertNotIn(unwanted, pre)
            self.assertIn('V293_success_sched_blocked ge M interrupt lock', pre)
            self.assertIn('V293_success_globals_away ge [running;interrupt;lock]', pre)
            for item in ['V293_critical_'+kind+'_update_execution P (kseq', 'RunLoad',
                         'V293_success_sched_blocked_frame', 'exact Exec', 'V293_success_schedule_execution']:
                self.assertIn(item, p)
            self.assertIn('(curs (sseq (V293_primitive_success_update', h)
            self.assertNotIn('sskip (Some', h)

    def test_tail_free_starts_at_boundary_not_whole_api(self):
        h,p = section(gate().TAIL).split('Proof.', 1)
        self.assertIn('V293_task_prio_success_tail running sched', h)
        self.assertIn('V293_bytes_writable M b 0%Z (typelen t)', h)
        self.assertIn('callcont ks = Some (kcall f body caller next)', h)
        self.assertIn('((ge,caller,Mf),ir,(enabled,si,ci))', h)
        self.assertIn('sskip (Some (Vint32 Int.zero))', h)
        self.assertIn('V293_error_return_execution P ks ge le caller M f body next 0%Z', p)

    def test_physical_tail_witness_is_simultaneous_and_universal_ie(self):
        h,p = section('V293_success_tail_return_witness').split('Proof.', 1)
        for item in ['forall saved run nesting locked enabled si ci ir', 'run < 256',
                     '(run = 1 -> nesting <> 0 \\/ locked <> 0)', 'V293_success_tail_fixture_program',
                     'get Mf (51%positive,0%Z) = None', 'get Mf (61%positive,Z.of_nat k) = None',
                     'load Tint8 Mf (100%positive,0%Z)', 'load Tint8 Mf (101%positive,0%Z)', 'load Tint8 Mf (102%positive,0%Z)']:
            self.assertIn(item, h)
        self.assertIn('V293_success_tail_return_execution', p)

    def test_literal_probe_is_fixed_and_does_not_alias_new_asts(self):
        s = (ROOT/gate().PROBE).read_text()
        definitions = s.split('Theorem expected_root_0', 1)[0]
        for unwanted in ['V293_OSSched_success_body', 'V293_OSSched_success_function',
                         'V293_task_prio_running', 'V293_task_prio_schedule', 'V293_success_sched_blocked']:
            self.assertNotIn(unwanted, definitions)
        self.assertEqual(s.count('Print Assumptions '), 6)
        for name in ['expected_nonrunning', 'expected_isr', 'expected_locked',
                     'expected_nonrunning_missing_function', 'expected_isr_missing_lock_binding']:
            self.assertIn('Example '+name+' :', s)
        self.assertIn('(fun _ => None)', s)

    def test_single_factor_control_proofs_unchanged(self):
        cases = gate().controls(SOURCE.read_text())
        self.assertEqual([x[0] for x in cases], ['RunningZero', 'WrongCall', 'NoFunctionBinding', 'ExitSti', 'ReturnOne', 'CallerNotRestored'])
        wrong_call = next(changed for label, changed, _, _ in cases if label == 'WrongCall')
        self.assertIn('(let original : fid := sched in 999999999%Z)', wrong_call)
        no_binding = next(changed for label, changed, _, _ in cases if label == 'NoFunctionBinding')
        self.assertIn('(let original : function := V293_OSSched_success_function', no_binding)
        self.assertIn('in True) ->', no_binding)
        for label, changed, target, original in cases:
            i = original.index('Proof.', original.index('Theorem '+target+' :'))
            j = changed.index('Proof.', changed.index('Theorem '+target+' :'))
            self.assertEqual(original[i:], changed[j:], label)
            self.assertNotEqual(original[:i], changed[:j], label)
            self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn', changed)

    def test_current_c_snapshots_preserve_running_condition_and_scheduler(self):
        task = (LOG/'OSTaskChangePrio.configured.c.snapshot.txt').read_text()
        sched = (LOG/'OS_Sched.configured.c.snapshot.txt').read_text()
        self.assertIn('if (OSRunning == 1u)', task)
        self.assertIn('OS_Sched();', task)
        for item in ['OS_CPU_SR cpu_sr = 0u;', 'V293_EnterCritical(&cpu_sr);', 'if (OSIntNesting == 0u)',
                     'if (OSLockNesting == 0u)', 'OS_SchedNew();', 'OSCtxSw();', 'V293_ExitCritical(&cpu_sr);']:
            self.assertIn(item, sched)

    def test_actual_gate_checks_and_unchanged_input_identity(self):
        result = json.loads((LOG/'gate04/result.json').read_text())
        self.assertTrue(result['passed'])
        self.assertTrue(result['inputs_unchanged'])
        self.assertTrue(result['temporary_tree_removed'])
        self.assertEqual(len(result['checks']), 16)
        snapshot = (LOG/'gate04/Production.v.snapshot.txt').read_bytes()
        self.assertEqual(hashlib.sha256(snapshot).hexdigest(), result['inputs'][gate().SOURCE])
        self.assertTrue(SOURCE.read_bytes().startswith(snapshot))
        for label,row in result['checks'].items():
            if label.startswith('negative-'):
                self.assertEqual(row['exit_code'], 1)
                self.assertGreater(row['error_line'], row['target_proof_line'])
                self.assertTrue(row['proof_suffix_unchanged'])
                self.assertFalse(row['downstream_credit'])
            else:
                self.assertEqual(row['exit_code'], 0)
        self.assertEqual(set(result['positive_assumptions']), {'PositiveAll','PositiveCall','PositiveSchedule','PositiveTail'})


if __name__ == '__main__':
    unittest.main()
