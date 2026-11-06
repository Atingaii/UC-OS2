"""结构及证据身份检查；语义由独立 Coq 编译和 coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage140-ready-global-trace'
SOURCE = 'certiucos/v293/proofs/V293ReadyGlobalTrace.v'
PROBE = 'audit/probes/V293ReadyGlobalTraceProbe.v'


class ReadyGlobalTraceTests(unittest.TestCase):
    def setUp(self):
        self.source = (R / SOURCE).read_text()
        self.probe = (R / PROBE).read_text()

    def section(self, name, probe=False):
        return (self.probe if probe else self.source).split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_registered_hole_free_production(self):
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(SOURCE), 1)
        self.assertNotIn('CertiOS.audit.', self.source)
        for text in [self.source, self.probe]:
            self.assertNotRegex(text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')

    def test_closure_uses_original_global_transition(self):
        body = self.source.split('Definition V293_global_steps', 1)[1].split('Definition V293_enclose', 1)[0]
        for text in ['clos_refl_trans_1n', 'lpstep p', 'tasks * osstate * tid']:
            self.assertIn(text, body)
        self.assertNotIn('Inductive', self.source)

    def test_intermediate_classification_is_derived_not_an_oracle(self):
        body = self.section('V293_cstep_global')
        for text in ['step_prop.cstep_cont_locality', 'V293_enclosing_inos',
                     'inapi_step', 'ostc_step', 'pt_step', 'ltstep_goodks']:
            self.assertIn(text, body)
        hypotheses = self.section('V293_csteps_global').split('Proof.', 1)[0]
        self.assertIn('po f=Some (tau,d1,d2,s)', hypotheses)
        self.assertIn('goodks', hypotheses)
        self.assertNotIn('InOS', hypotheses)
        self.assertNotIn('clt_step', self.source)

    def test_joint_source_keeps_actual_call_counter_and_branches(self):
        body = self.section('GSsource_tail', True)
        for text in ['V293_ready_source_dispatch', 'Int.add Int.mone Int.one=Int.zero',
                     'destruct different', 'STentry ct different', 'GSprogram']:
            self.assertIn(text, body)
        self.assertIn('V293_csteps_global', self.section('GSglobal_source', True))

    def test_switch_is_in_same_closure_and_cache_gap_retained(self):
        body = self.section('GSglobal_switch', True)
        for text in ['GSglobal_source true', 'V293_ready_switch_step',
                     'clos_rt1n_rt', 'Relation_Operators.rt_step',
                     'Some (Vint32 Int.zero)', 'Some (V293_byteval 6)',
                     '~ V293_current_task OwnershipTasks OwnershipReady 6',
                     'other<>OwnershipWaiting']:
            self.assertIn(text, body)
        body = self.section('GSglobal_no_switch', True)
        self.assertIn('Some (Vint32 Int.mone)', body)
        self.assertIn('V293_current_task OwnershipTasks OwnershipReady 4', body)

    def test_binding_ablation_retains_source_trace_and_other_bindings(self):
        body = self.section('GSbinding_only_control', True)
        for text in ['f<>112%Z -> GSpo f=RCprogram f', 'RCprogram 112%Z=None',
                     '~ InOS', 'cstepstar RCprogram', 'STjoint_source_tail ct different GSouter']:
            self.assertIn(text, body)
        self.assertIn('not a stuckness claim', self.probe)

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

    def test_chinese_claims_bound_fixture_and_global_trace(self):
        doc = (R / 'audit/STAGE140_READY_GLOBAL_TRACE.md').read_text()
        for text in ['原 lpstep 的连续闭包', '推导每步 InOS', 'enclosing fragment fixture',
                     '不是完整 `OS_Sched`', '单因素', '不是 stuckness 定理',
                     'CurLINV', '生产全局语义 Inv', '存在性、无交错',
                     'GOOD_OS', 'K1–K4', 'uCOS3 未开始', '失败 ID 集合']:
            self.assertIn(text, doc)


if __name__ == '__main__':
    unittest.main()
