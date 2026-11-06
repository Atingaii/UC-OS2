"""结构／身份回归；真实语义由 Coq 编译和 coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage138-ready-switch-step'
SOURCE = 'certiucos/v293/proofs/V293ReadySwitchStep.v'
PROBE = 'audit/probes/V293ReadySwitchStepProbe.v'


class ReadySwitchStepTests(unittest.TestCase):
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

    def test_constructive_current_store_with_same_invariant_and_frame(self):
        body = self.section('V293_ready_current_write')
        pre = body.split('  exists Mf,', 1)[0]
        self.assertNotIn('store (', pre)
        for text in ['V293_ready_switch_full', "store_exist_join'", 'V293_ready_store_frame',
                     'set O curtid (oscurt next)', 'V293_store_readback', 'V293_storebytes_outside']:
            self.assertIn(text, body)
        frame = self.section('V293_ready_store_frame')
        for text in ['V293_shared_store_global', 'V293_shared_replace_slot', 'V293_ready_switch_halves']:
            self.assertIn(text, frame)

    def test_actual_pswitch_common_pointer_type_and_task_code_update(self):
        body = self.section('V293_ready_switch_step')
        for text in ['get ge target=Some (bt,Tptr tp)', 'get ge OSTCBCur=Some (bc,Tptr tp)',
                     'lpstep (pc,(po,pi,ip))', 'pswitch_step', 'projS',
                     'set T current (SKIP,(kenil,ks))', 't<>current', 'V293_ready_current_write']:
            self.assertIn(text, body)

    def test_original_call_target_then_switch_on_same_memory(self):
        body = self.section('V293_ready_call_then_switch')
        for text in ['V293_ready_dispatch_call', 'V293_ready_switch_step', 'Mtarget, exists Mf',
                     'store (Tptr V293_tcb_type) Mskip (bo,0%Z)',
                     'cstepstar P', 'lpstep (pc,(po,pi,ip))',
                     '(ge,les,Mtarget,ir,au)', '(ge,les,Mf,ir,au)']:
            self.assertIn(text, body)

    def test_type_only_control_keeps_old_actual_prefix_and_SWPRE(self):
        self.assertIn('Definition RSge : env := set RHge OSTCBCur (1%positive,Tptr V293_tcb_type)', self.probe)
        for text in ['get RHge OSTCBCur', 'get RSge OSTCBCur', 'get RSge x=get RHge x']:
            self.assertIn(text, self.section('RSbinding_type_only', True))
        for text in ['cstepstar RCprogram', 'SWPRE V293_scheduler', 'RCjoint_call_handoff_and_omission', 'RSold_no_common_type']:
            self.assertIn(text, self.section('RSold_SWPRE_without_switch_type', True))

    def test_joint_ready_waiting_own_projection_records_and_omission(self):
        body = self.section('RSjoint_call_switch', True)
        for text in ['forall ks live', 'RHmemory (RIcurrent live)', 'V293_ready_call_then_switch',
                     'Different : ct<>OwnershipReady', 'RScurrent_load _ _ _ _ Bad',
                     'OldLoad', 'V293_ready_lenv_frame', 'V293_task_records Mf OwnershipTasks',
                     'projS', 'Some ((RSge,emp,Mf)', '(V293_byteval 99)',
                     'free Tint8 b Ms=Some Mskip', 'get Mskip (b,0%Z)=None',
                     'get Mf (c,i)=get Mtarget (c,i)']:
            self.assertIn(text, body)
        self.assertIn('Definition RStasks (ct : tid)', self.probe)
        self.assertIn('sig OwnershipReady (SKIP,(kenil,kstop))', self.probe)

    def test_stable_compiles_and_prospective_protocol(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('proof', SOURCE), ('probe', PROBE)]:
            row = json.loads((D / (stable[kind] + '.json')).read_text())
            data = (R / path).read_bytes()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256(data).hexdigest())
            self.assertEqual(data, (D / (stable[kind] + '.v.snapshot.txt')).read_bytes())
        self.assertEqual(len(json.loads((D / 'protocol.json').read_text())['prospective_checks']), 6)

    def test_chinese_claims_bounded_to_single_immediate_step(self):
        doc = (R / 'audit/STAGE138_READY_SWITCH_STEP.md').read_text()
        for text in ['单因素', '同一 Mtarget', '共同 pointee type', '完整连续控制轨迹',
                     '不把目标指针当作私有 frame 跨上下文切换保存', '无交错存在性执行',
                     '不是生产全局语义 Inv', 'WFIFun', 'GOOD_OS', 'K1–K4',
                     'uCOS3 未开始', '423', '失败 ID 集合', 'GoodInvAsrt',
                     '初始化可达性', '所有交错', '任意分配选择', '不是 C 修复']:
            self.assertIn(text, doc)
