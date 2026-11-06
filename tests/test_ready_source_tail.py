"""结构及证据身份回归；Coq 编译／coqchk 才检查证明语义。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage139-ready-source-tail'
SOURCE = 'certiucos/v293/proofs/V293ReadySourceTail.v'
PROBE = 'audit/probes/V293ReadySourceTailProbe.v'


class ReadySourceTailTests(unittest.TestCase):
    def setUp(self):
        self.source = (R / SOURCE).read_text()
        self.probe = (R / PROBE).read_text()

    def section(self, name, probe=False):
        return (self.probe if probe else self.source).split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_registered_hole_free_and_production_independent(self):
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(SOURCE), 1)
        self.assertNotIn('CertiOS.audit.', self.source)
        for text in [self.source, self.probe]:
            self.assertNotRegex(text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')

    def test_original_priority_bytes_determine_both_branches(self):
        body = self.section('V293_ready_source_change')
        for text in ['V293_OSSched_byte_comparison_eval', 'destruct (Nat.eqb nh nc)',
                     'then SKIP else curs (sprim (switch target))',
                     'V293_OSSched_change high cached counter', 'ReadHigh', 'ReadCache']:
            self.assertIn(text, body)
        self.assertNotIn('V293_OSSched_pointer_guard', body)

    def test_counter_store_is_constructed_and_modular_with_outside_frame(self):
        body = self.section('V293_ready_source_change')
        self.assertNotIn('store Tint32', body.split('  exists Mf,', 1)[0])
        for text in ['V293_owned_record_cell_update', 'Int.add c Int.one',
                     'V293_tick_assign32_execution', 'V293_storebytes_outside',
                     'V293_owned_record_cell_load', '(4<=i)%Z']:
            self.assertIn(text, body)
        self.assertIn('Int.add Int.mone Int.one=Int.zero', self.section('STjoint_source_tail', True))

    def test_call_target_and_tail_are_one_continuous_control_trace(self):
        body = self.section('V293_ready_source_dispatch')
        for text in ['V293_ready_dispatch_call', 'V293_ready_source_change',
                     '(kseq (V293_OSSched_change', 'curs (sseq (V293_OSSched_unlocked_prefix',
                     'then SKIP else curs (sprim (switch target))', 'GoodInvAsrt R',
                     'exists tasks lo hi entries next message Mtarget Mtail',
                     '(ge,caller,Mtail)', 'apply sskip_step']:
            self.assertIn(text, body)
        self.assertNotIn('get T current', body.split('  exists tasks', 1)[0])

    def test_joint_trace_supplies_same_code_and_memory_to_actual_switch(self):
        body = self.section('STjoint_source_switch', True)
        for text in ['cstepstar RCprogram (curs STbody',
                     '(curs (sprim (switch 106%Z)),(kenil,ks)) (STge,RTle,Mtail)',
                     'lpstep (RCprogram,(po,pi,ip))', 'RSles OwnershipWaiting,Mtail',
                     'V293_ready_switch_step', 'SWINVt (V293_ready_inv',
                     'Some (Vptr OwnershipReady)', 'Some (Vint32 Int.zero)']:
            self.assertIn(text, body)

    def test_cache_single_factor_and_remaining_coherence_gap_are_explicit(self):
        body = self.section('STcache_only_control', True)
        for text in ['forall ct a', 'a<>(94%positive,0%Z)',
                     'STmemory ct true', 'STmemory ct false', 'V293_encoded_memory_outside']:
            self.assertIn(text, body)
        body = self.section('STjoint_source_switch', True)
        for text in ['V293_current_task OwnershipTasks OwnershipWaiting 6',
                     '~ V293_current_task OwnershipTasks OwnershipReady 6',
                     'load Tint8 Mf (94%positive,0%Z)=Some (V293_byteval 6)',
                     'load Tint8 Mf (94%positive,0%Z)<>Some (V293_byteval 4)']:
            self.assertIn(text, body)
        body = self.section('STjoint_no_switch', True)
        self.assertIn('V293_current_task OwnershipTasks OwnershipReady 4', body)
        self.assertIn('Some (Vint32 Int.mone)', body)

    def test_stable_compiles_and_prospective_protocol(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('proof', SOURCE), ('probe', PROBE)]:
            row = json.loads((D / (stable[kind] + '.json')).read_text())
            data = (R / path).read_bytes()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256(data).hexdigest())
            self.assertEqual(data, (D / (stable[kind] + '.v.snapshot.txt')).read_bytes())
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertEqual(len(protocol['checks']), 5)
        self.assertIn('不把存在性片段执行当作全局所有轨迹或 GOOD_OS', protocol['limits'])

    def test_chinese_claims_bounded_to_unlocked_mixed_trace(self):
        doc = (R / 'audit/STAGE139_READY_SOURCE_TAIL.md').read_text()
        for text in ['原优先级字节比较', '连续 cstepstar', '同码同内存',
                     'UINT32_MAX', '单因素', '一致性', '不是 C 修复',
                     '不是全局 lpstep 闭包', '不是生产全局语义 Inv',
                     '初始化可达性', '所有交错', 'GoodInvAsrt', 'WFIFun',
                     'GOOD_OS', 'K1–K4', 'uCOS3 未开始', '423', '失败 ID 集合']:
            self.assertIn(text, doc)
