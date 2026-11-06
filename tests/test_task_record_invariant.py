"""有限记录不变式的结构／证据回归；不替代 Coq 语义检查。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage134-task-record-invariant'
SOURCE = 'certiucos/v293/proofs/V293TaskRecordInvariant.v'
PROBE = 'audit/probes/V293TaskRecordInvariantProbe.v'


class TaskRecordInvariantTests(unittest.TestCase):
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

    def test_precision_aligns_same_abstract_witnesses_and_uses_existing_storage(self):
        for text in ['V293_priority_repr_injective', 'V293_storage_precise',
                     'V293_record_types_pend', 'V293_shared_fields_core_get',
                     'OSAbstMod.join_get_l', 'precise_star']:
            self.assertIn(text, self.source)
        self.assertIn('V293_task_list_context', self.section('V293_records_core_aux'))

    def test_closed_goodi_preserves_record_resources_and_both_membership_branches(self):
        body = self.section('V293_records_invariant_good')
        for text in ['GoodI V293_records_inv V293_scheduler V293_shared_li',
                     'V293_shared_no_abstract_frame', 'V293_shared_current_read',
                     'V293_records_store', 'classic (indom ts ct)',
                     'Mx=emp /\\ Ox=emp', 'V293_scheduler_good']:
            self.assertIn(text, body)
        self.assertNotIn('GoodI', self.section('V293_records_store'))

    def test_soundness_is_same_map_full_caller_memory_with_frame(self):
        body = self.section('V293_records_switch_sound')
        for text in ['forall t R s', 'get (getabst s) abstcblsid',
                     'V293_task_records (getmem s) tasks',
                     'V293_owned_task_records_sound', 'V293_task_record_sub']:
            self.assertIn(text, body)

    def test_nonempty_ready_waiting_fixture_instantiates_live_and_dead_current(self):
        for text in ['CertiOS.audit.probes.V293TaskRecordOwnershipProbe',
                     'if live then OwnershipWaiting else (999%positive,Int.zero)',
                     'OwnershipLiteralSpatial']:
            self.assertIn(text, self.probe)
        body = self.section('RIswitch_cases', True)
        for text in ['forall live', 'AHprio V293_scheduler OwnershipReady',
                     'get OwnershipTasks (RIcurrent live)', 'store_exist_join\'',
                     'V293_records_store', 'V293_task_records M\' OwnershipTasks',
                     'V293_storebytes_outside']:
            self.assertIn(text, body)

    def test_single_real_byte_mutation_weak_survives_coupled_rejects(self):
        body = self.section('RIone_byte_ablation', True)
        for text in ['store Tint8 (RImemory OwnershipWaiting) (60%positive,50%Z)',
                     'forall a, a<>(60%positive,50%Z)', 'V293_byteval 4', 'V293_byteval 5',
                     'SWINVt V293_shared_inv OwnershipWaiting ** Atrue',
                     'forall t R, ~ RIstate OwnershipWaiting Mbad',
                     'join_store_join', 'RIweak_frame', 'V293_records_switch_sound',
                     'tasks=OwnershipTasks', 'rewrite NewLoad in OldLoad']:
            self.assertIn(text, body)

    def test_stable_compiles_match_exact_sources_and_five_prospective_checks(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('proof', SOURCE), ('probe', PROBE)]:
            label = stable[kind]
            row = json.loads((D / (label + '.json')).read_text())
            data = (R / path).read_bytes()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256(data).hexdigest())
            self.assertEqual(data, (D / (label + '.v.snapshot.txt')).read_bytes())
        self.assertEqual(len(json.loads((D / 'protocol.json').read_text())['prospective_checks']), 5)

    def test_chinese_documentation_bounds_claims_and_does_not_erase_old_failures(self):
        doc = (R / 'audit/STAGE134_TASK_RECORD_INVARIANT.md').read_text()
        for text in ['单因素', '同一抽象任务映射', '其他全部地址', '仍可满足',
                     '不是生产全局语义 Inv', '空 LocalInv', 'WFIFun', 'GOOD_OS',
                     'K1–K4', 'uCOS3 未开始', '423', '失败 ID 集合']:
            self.assertIn(text, doc)
