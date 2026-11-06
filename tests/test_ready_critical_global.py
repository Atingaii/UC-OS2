"""结构与证据身份回归；语义另由 Coq／coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage141-ready-critical-global'
LIFT = 'certiucos/v293/proofs/V293LocalGlobalTrace.v'
CONTROL = 'certiucos/v293/proofs/V293ReadyCriticalGlobal.v'
PROBE = 'audit/probes/V293ReadyCriticalGlobalProbe.v'


class ReadyCriticalGlobalTests(unittest.TestCase):
    def setUp(self):
        self.lift, self.control, self.probe = [(R / n).read_text() for n in [LIFT, CONTROL, PROBE]]

    def section(self, name, text):
        return text.split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_registered_hole_free_sources(self):
        for n in [LIFT, CONTROL]:
            self.assertEqual((R / '_CoqProject').read_text().splitlines().count(n), 1)
        for s in [self.lift, self.control, self.probe]:
            self.assertNotRegex(s, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        for s in [self.lift, self.control]:
            self.assertNotIn('CertiOS.audit.', s)
        self.assertEqual(sum(len(re.findall(r'^(?:Lemma|Theorem) \w+\s*:', s, re.M))
                             for s in [self.lift, self.control, self.probe]), 27)

    def test_original_local_steps_lift_real_aux(self):
        for s in ['V293_local_steps', 'V293_global_steps', 'loststep_cont_locality',
                  'V293_enclosing_inos', 'inapi_step', 'pt_step', 'ltstep_goodks', 'set aus t au']:
            self.assertIn(s, self.lift)
        self.assertNotIn('Inductive', self.lift)
        hypotheses = self.section('V293_local_steps_global', self.lift).split('Proof.', 1)[0]
        self.assertNotIn('InOS', hypotheses)

    def test_critical_entry_exit_are_real_steps(self):
        enter = self.section('V293_sched_control_enter', self.control)
        for s in ['ni<256', 'nl<256', 'load Tint8 M (bi,0%Z)', 'load Tint8 M (bl,0%Z)',
                  'enabled::ci', 'encrit_step', 'V293_success_global_byte_eq']:
            self.assertIn(s, enter)
        exit_body = self.section('V293_sched_control_exit', self.control)
        for s in ['saved::ci', '(saved,si,ci)', 'excrit_step', 'curs sret']:
            self.assertIn(s, exit_body)
        stack = self.section('V293_ready_critical_stack', self.control)
        for s in ['GoodInvAsrt R', '(false,si,ci)', '(false,si,ci\')', 'V293_ready_core_aux']:
            self.assertIn(s, stack)

    def test_same_ready_body_and_independent_guard_controls(self):
        for s in ['CGexact_existing_body', 'CGinterrupt_only_byte', 'CGlock_only_byte',
                  'CGmemory ct different 1 0', 'CGmemory ct different 0 1']:
            self.assertIn(s, self.probe)
        self.assertIn('V293_ready_source_dispatch', self.section('CGsource_tail', self.probe))
        self.assertIn('V293_local_steps_global', self.section('CGglobal_independent_guards', self.probe))
        for s in ['CGlocal_ready false enabled ci', 'V293_sched_control_exit',
                  'Some (Vint32 Int.mone)', 'Some (V293_byteval 4)']:
            self.assertIn(s, self.section('CGglobal_no_switch_restore', self.probe))

    def test_actual_switch_keeps_old_exit_and_cache_gap(self):
        body = self.section('CGglobal_switch_pending_exit', self.probe)
        for s in ['V293_ready_switch_step', 'CGglobal_ready true enabled ci',
                  'kseq (sseq (sprim excrit) sret) CGouter', 'Some (false,nil,enabled::ci)',
                  'Some (false,nil,nil)', 'Some (Vint32 Int.zero)', 'Some (V293_byteval 6)',
                  '~ V293_current_task OwnershipTasks OwnershipReady 6']:
            self.assertIn(s, body)

    def test_encrit_only_ablation_measures_actual_wrong_pop(self):
        body = self.section('CGonly_enter_ablation', self.probe)
        for s in ['CGcontrol=sseq (sprim encrit) CGdeleted', 'negb enabled::ci',
                  '(negb enabled,nil,ci)', 'CGlocal_blocked', 'V293_sched_control_exit']:
            self.assertIn(s, body)
        boundary = self.section('CGdeleted_empty_stack_boundary', self.probe)
        for s in ['CGdeleted_to_skip', '~ (exists C\' st\', loststep', 'V293_missing_enter_control']:
            self.assertIn(s, boundary)

    def test_stable_compiles_and_prospective_protocol(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for k, n in [('lift', LIFT), ('control', CONTROL), ('probe', PROBE)]:
            row = json.loads((D / (stable[k] + '.json')).read_text())
            data = (R / n).read_bytes()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256(data).hexdigest())
            self.assertEqual(data, (D / (stable[k] + '.v.snapshot.txt')).read_bytes())
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertEqual(len(protocol['checks']), 6)
        self.assertEqual(len(protocol['limits']), 4)

    def test_chinese_claims_remain_bounded(self):
        doc = (R / 'audit/STAGE141_READY_CRITICAL_GLOBAL.md').read_text()
        for s in ['推导每步 InOS', '不是完整 `OS_Sched` 调用', '仅删除 encrit',
                  '旧任务保留待执行 excrit', '存在性、无交错', 'CurLINV',
                  '生产全局语义 Inv', 'GOOD_OS', 'K1–K4', 'uCOS3 未开始', '失败 ID 集合']:
            self.assertIn(s, doc)


if __name__ == '__main__':
    unittest.main()
