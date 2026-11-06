"""同表任务记录／就绪存储的结构回归；Coq 语义结论另经 coqchk。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage135-ready-task-invariant'
SOURCE = 'certiucos/v293/proofs/V293ReadyTaskInvariant.v'
PROBE = 'audit/probes/V293ReadyTaskInvariantProbe.v'


class ReadyTaskInvariantTests(unittest.TestCase):
    def setUp(self):
        self.source = (R / SOURCE).read_text()
        self.probe = (R / PROBE).read_text()

    def section(self, name, probe=False):
        text = self.probe if probe else self.source
        return text.split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_registered_hole_free_production_has_no_audit_dependency(self):
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(SOURCE), 1)
        self.assertNotIn('CertiOS.audit.', self.source)
        for text in [self.source, self.probe]:
            self.assertNotRegex(text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')

    def test_precise_storage_uses_fixed_footprint_not_equal_existential_values(self):
        body = self.section('V293_ready_owned_precise')
        for text in ['V293_owned_cells_storage', 'V293_ready_types_length', 'V293_storage_precise']:
            self.assertIn(text, body)
        for text in ['V293_owned_task_records tasks ** V293_ready_owned',
                     'V293_bitmap_tasks lo hi tasks', 'V293_priority_table entries tasks']:
            self.assertIn(text, self.source)

    def test_goodi_is_closed_and_uses_actual_current_store(self):
        body = self.section('V293_ready_invariant_good')
        for text in ['GoodI V293_ready_inv V293_scheduler V293_shared_li',
                     'V293_ready_store', 'classic (indom ts ct)', 'V293_scheduler_good']:
            self.assertIn(text, body)
        for text in ['V293_shared_store_global', 'V293_shared_replace_slot',
                     'V293_ready_payload br bg bp x']:
            self.assertIn(text, self.section('V293_ready_store'))

    def test_selection_and_two_source_assignments_derive_not_assume_highest(self):
        body = self.section('V293_ready_sched_updates')
        pre = body.split('  exists tasks lo hi entries t message Mf,', 1)[0]
        self.assertNotIn('AHprio', pre)
        self.assertNotIn('V293_scheduler O', pre)
        for text in ['V293_ready_switch_selected', 'V293_OSSchedNew_updates_execution',
                     'V293_OSSched_target_expr', 'V293_scheduler O t',
                     'get Mf a=get M a', 'SWINVt V293_ready_inv current ** R']:
            self.assertIn(text, body)
        for text in ['get (getabst s) abstcblsid', 'V293_task_records (getmem s) tasks']:
            self.assertIn(text, self.section('V293_ready_switch_sound'))

    def test_joint_actual_memory_nonempty_ready_waiting_and_both_current_cases(self):
        for text in ['Vptr OwnershipReady;Vnull;Vptr OwnershipWaiting',
                     'V293_nat_memory 92%positive 0%Z V293_ready_table']:
            self.assertIn(text, self.probe)
        for text in ['forall live', 'store (Tptr', 'V293_ready_store']:
            self.assertIn(text, self.section('RTswitch_cases', True))
        for text in ['forall P ks live', 'RTexec_memory (RIcurrent live)',
                     'V293_ready_sched_updates', 'RTexec_entry ct', 'RTdecoder_loads ct',
                     'V293_task_records Mf OwnershipTasks', 'Some (Vptr OwnershipReady)']:
            self.assertIn(text, self.section('RTjoint_execution', True))

    def test_independent_single_factor_corruptions_old_survives_new_rejects(self):
        for name, store in [('RTbitmap_ablation', 'store Tint8'),
                            ('RTslot_ablation', 'store (Tptr V293_tcb_type)')]:
            body = self.section(name, True)
            self.assertIn(store, body)
            self.assertIn('SWINVt V293_records_inv OwnershipWaiting ** Atrue', body)
            self.assertIn('forall t R, ~ RTstate OwnershipWaiting Mbad', body)
            self.assertIn('get Mbad', body)
            self.assertIn('get (RTfull OwnershipWaiting)', body)
        self.assertIn('V293_byteval 16', self.section('RTbitmap_ablation', True))
        self.assertIn('V293_byteval 0', self.section('RTbitmap_ablation', True))
        self.assertIn('(82%positive,16%Z)', self.section('RTslot_ablation', True))

    def test_stable_compiles_and_six_prospective_checks(self):
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

    def test_chinese_documentation_bounds_claims_and_keeps_old_failures(self):
        doc = (R / 'audit/STAGE135_READY_TASK_INVARIANT.md').read_text()
        for text in ['单因素', '同一抽象任务映射', '其他全部地址', '仍可满足',
                     '不是生产全局语义 Inv', '空 LocalInv', 'WFIFun', 'GOOD_OS',
                     'K1–K4', 'uCOS3 未开始', '423', '失败 ID 集合', '两条赋值',
                     '不是完整函数', '未使用槽', '13..15', '只读']:
            self.assertIn(text, doc)
