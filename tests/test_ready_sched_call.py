"""真实调用返回连接的结构和证据身份；语义由 Coq/coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage137-ready-call-return'
SOURCE = 'certiucos/v293/proofs/V293ReadySchedCall.v'
PROBE = 'audit/probes/V293ReadySchedCallProbe.v'


class ReadySchedCallTests(unittest.TestCase):
    def setUp(self):
        self.source = (R / SOURCE).read_text()
        self.probe = (R / PROBE).read_text()

    def section(self, name, probe=False):
        return (self.probe if probe else self.source).split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_registered_hole_free_and_production_independent_of_probes(self):
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(SOURCE), 1)
        self.assertNotIn('CertiOS.audit.', self.source)
        for text in [self.source, self.probe]:
            self.assertNotRegex(text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')

    def test_local_address_output_and_highest_derived_from_same_ready_invariant(self):
        body = self.section('V293_ready_sched_call')
        pre = body.split('  exists tasks lo hi entries next message b Ms Mf,', 1)[0]
        for text in ['fresh M', 'get caller y', 'AHprio', 'V293_scheduler O', 'oldy', 'byblock']:
            self.assertNotIn(text, pre)
        for text in ['V293_ready_fresh_avoiding M', 'V293_ready_sched_raw_updates',
                     'SWINVt (V293_ready_inv br bg bp) current', 'GoodInvAsrt R']:
            self.assertIn(text, body)
        self.assertIn('V293_ready_switch_selected', self.section('V293_ready_sched_raw_updates'))

    def test_actual_call_allocate_body_return_free_and_restored_caller(self):
        body = self.section('V293_ready_sched_call')
        for text in ['snpcall_step', 'sfexec_step', 'salloclv_step', 'sallocend_step',
                     'sret_step', 'sfree_step', 'sfreeend_step', 'V293_tick_allocate_frame',
                     'V293_ready_release_byte', 'V293_ready_lenv_frame',
                     '(curs (sskip None),(kenil,ks)) (ge,caller,Mf)',
                     'free Tint8 b Ms=Some Mf', 'get Mf (b,0%Z)=None',
                     'get Mf (c,i)=get M (c,i)']:
            self.assertIn(text, body)

    def test_raw_undef_first_original_assignment_not_fake_initialization(self):
        raw = self.section('V293_ready_sched_raw_updates')
        for text in ['Amapsto (byblock,0%Z) Tint8 true oldy', 'V293_tick_raw_slot_update',
                     'V293_OSSchedNew_updates_execution', 'V293_owned_byte_update']:
            self.assertIn(text, raw)
        self.assertIn('Amapsto (b,0%Z) Tint8 true Vundef', self.section('V293_ready_sched_call'))
        reject = self.section('RCundef_not_typed_byte', True)
        for text in ['~ s |= V293_owned_record_cell ((b,0%Z),Tint8,Vundef)',
                     'astar_l_apure_elim', 'discriminate']:
            self.assertIn(text, reject)

    def test_real_call_then_original_target_store_builds_switch_preconditions(self):
        body = self.section('V293_ready_dispatch_call')
        for text in ['V293_ready_sched_call', 'V293_OSSched_unlocked_prefix f table high target',
                     'V293_eval_pointer_array', 'V293_owned_record_cell_update',
                     'store (Tptr V293_tcb_type) Mskip (bo,0%Z) (Vptr next)=Some Mf',
                     'V293_assign_pointer_execution', 'V293_ready_target_pre',
                     'SWPRE_NDEAD', 'SWPRE_DEAD', 'assert (x=tasks) by congruence']:
            self.assertIn(text, body)

    def test_joint_concrete_program_both_current_cases_and_caller_canary(self):
        self.assertIn('Definition RCprogram : progunit', self.probe)
        self.assertIn('Z.eq_dec f 107%Z', self.probe)
        body = self.section('RCjoint_call_handoff_and_omission', True)
        for text in ['forall ks live', 'cstepstar RCprogram', 'RCframe_good (RHlookup ct) (RCentry ct)',
                     'RTonly_ready', 'RIfixed_tasks', 'live=true', 'live=false',
                     'free Tint8 b Ms=Some Mskip', 'get Mskip (b,0%Z)=None',
                     'load Tint8 Mskip (90%positive,0%Z)=Some (V293_byteval 99)',
                     'load Tint8 Mf (90%positive,0%Z)=Some (V293_byteval 99)',
                     '~ RHstate (RIcurrent live) Mskip |= SWPRE', 'RHreject_waiting_target',
                     'get Mf (c,i)=get Mskip (c,i)']:
            self.assertIn(text, body)

    def test_stable_compiles_and_prospective_protocol(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('proof', SOURCE), ('probe', PROBE)]:
            label = stable[kind]
            row = json.loads((D / (label + '.json')).read_text())
            data = (R / path).read_bytes()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256(data).hexdigest())
            self.assertEqual(data, (D / (label + '.v.snapshot.txt')).read_bytes())
        self.assertEqual(len(json.loads((D / 'protocol.json').read_text())['prospective_checks']), 6)

    def test_chinese_bounds_no_full_kernel_or_cross_switch_frame_claim(self):
        doc = (R / 'audit/STAGE137_READY_CALL_RETURN.md').read_text()
        for text in ['单因素', '共同前缀', '其他全部地址', '目标四字节之外',
                     '不把目标指针当作私有 frame 跨上下文切换保存',
                     '无交错存在性执行', '不是生产全局语义 Inv', 'WFIFun', 'GOOD_OS',
                     'K1–K4', 'uCOS3 未开始', '423', '失败 ID 集合', 'GoodInvAsrt',
                     'Vundef', '初始化可达性', '所有交错', '任意分配选择']:
            self.assertIn(text, doc)
