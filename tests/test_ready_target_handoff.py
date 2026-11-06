"""目标写入连接的结构／证据回归；语义由 Coq 和 coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage136-ready-target-handoff'
SOURCE = 'certiucos/v293/proofs/V293ReadyTargetHandoff.v'
PROBE = 'audit/probes/V293ReadyTargetHandoffProbe.v'


class ReadyTargetHandoffTests(unittest.TestCase):
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

    def test_public_interface_derives_highest_from_owned_ready_invariant(self):
        body = self.section('V293_ready_dispatch_updates')
        pre = body.split('  exists tasks lo hi entries next message Mselected Mf,', 1)[0]
        self.assertNotIn('AHprio', pre)
        self.assertNotIn('V293_scheduler O', pre)
        for text in ['V293_ready_sched_updates', 'V293_ready_target_pre',
                     'V293_scheduler O next', 'SWINVt (V293_ready_inv br bg bp) current']:
            self.assertIn(text, body)

    def test_same_prefix_original_sequence_and_actual_constructed_store(self):
        body = self.section('V293_ready_dispatch_updates')
        for text in ['kseq (V293_OSSched_target_update table high target) ks',
                     'sseq (V293_OSSchedNew_updates unmap group rows high y)',
                     'store (Tptr V293_tcb_type) Mselected (bo,0%Z) (Vptr next)=Some Mf',
                     'V293_owned_record_cell_update', 'V293_assign_pointer_execution',
                     'V293_cstepstar_trans', 'V293_storebytes_outside']:
            self.assertIn(text, body)

    def test_real_target_binding_and_same_task_map_feed_switch_precondition(self):
        for text in ['get ge target=Some (bo,Tptr V293_tcb_type)',
                     'V293_ready_named_target_frame', 'V293_tasks_highest_spatial',
                     'V293_ready_switch_full', 'get O abstcblsid', 'assert (x=ts) by congruence']:
            self.assertIn(text, self.section('V293_ready_target_pre'))
        for text in ['SWPRE_NDEAD', 'SWPRE_DEAD', 'indom tasks current']:
            self.assertIn(text, self.section('V293_ready_dispatch_updates'))

    def test_joint_memory_covers_nonempty_tasks_and_both_current_cases(self):
        for text in ['RHbase_entry', 'RHjoin', 'RHlookup', 'RTenv_spatial',
                     'Vptr OwnershipWaiting', 'set RTge 106%Z (93%positive,Tptr V293_tcb_type)']:
            self.assertIn(text, self.probe)
        body = self.section('RHjoint_handoff_and_omission', True)
        for text in ['forall P ks live', 'RHmemory (RIcurrent live)', 'live=true', 'live=false',
                     '(RHlookup ct) (RHentry ct)', 'RTonly_ready', 'RIfixed_tasks',
                     'Some (Vptr OwnershipReady)']:
            self.assertIn(text, body)

    def test_single_factor_omission_preserves_prefix_high_invariant_and_other_bytes(self):
        body = self.section('RHjoint_handoff_and_omission', True)
        for text in ['store (Tptr V293_tcb_type) Mskip (93%positive,0%Z)',
                     'RHstate (RIcurrent live) Mskip |= SWINVt',
                     'load Tint8 Mskip (91%positive,0%Z)=Some (V293_byteval 4)',
                     '~ RHstate (RIcurrent live) Mskip |= SWPRE',
                     'get Mf (b,i)=get Mskip (b,i)', 'RHreject_waiting_target']:
            self.assertIn(text, body)
        reject = self.section('RHreject_waiting_target', True)
        for text in ['load (Tptr V293_tcb_type) M', 'Vptr OwnershipWaiting',
                     'RIfixed_tasks', 'mapstoval_load', 'load_mem_mono', 'destruct Highest']:
            self.assertIn(text, reject)

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

    def test_chinese_bounds_no_full_function_or_cross_switch_private_frame_claim(self):
        doc = (R / 'audit/STAGE136_READY_TARGET_HANDOFF.md').read_text()
        for text in ['单因素', '共同前缀', '其他全部地址', '目标四字节之外',
                     '不把目标指针当作私有 frame 跨上下文切换保存',
                     '无交错', '不是生产全局语义 Inv', 'WFIFun', 'GOOD_OS',
                     'K1–K4', 'uCOS3 未开始', '423', '失败 ID 集合', 'call／return']:
            self.assertIn(text, doc)
