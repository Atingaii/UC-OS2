"""固定配置 OS_QInit：独立入口、完整调用、负控与有界结论。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage56-init-queue'
C='certiucos/v293/code/V293OSQInit.v';P='certiucos/v293/proofs/V293QInit.v';B='audit/probes/V293QInitProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class InitQueueTests(unittest.TestCase):
    def test_old_inputs_and_reusable_products_unchanged(self):
        b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
        for p,h in b['files'].items():
            if p not in allowed:self.assertEqual(sha(R/p),h,p)
        for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
        active=[p for p in (R/'_CoqProject').read_text().splitlines() if p.endswith('.v')];expected=b['sources']+[C,P]
        self.assertEqual(active[:len(expected)],expected);self.assertEqual(len(b['sources']),209);self.assertEqual(len(b['products']),1045)
    def test_exact_source_layout_and_order(self):
        x=read(L/'source/q.json');y=read(L/'source-connection.json');self.assertTrue(x['passed']);self.assertTrue(y['passed']);self.assertTrue(y['all94_identities_equal'])
        self.assertEqual(x['function']['name'],'OS_QInit');self.assertEqual(x['function']['preprocessed_body_sha256'],'1c7141f5cfdd50134cb33e3f4b1d4d3ddcd75d8c0effe2cfdbab933d513196e6')
        self.assertEqual(x['source_identity'],'74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da')
        self.assertEqual(x['layout'],dict(size=24,count=4,table=96,Ptr=0,Start=4,End=8,In=12,Out=16,Size=20,Entries=22))
        self.assertEqual(x['loop_iterations'],3);self.assertEqual(x['layout_exit'],0);self.assertEqual(y['actual_local_order'],['ix','ix_next','pq1','pq2']);self.assertEqual(y['OSInit_position_zero_based'],7)
        self.assertFalse(y['verified_frontend']);self.assertFalse(y['seventh_call_connected'])
    def test_real_clear_native_loop_and_four_local_call(self):
        s=(R/P).read_text();c=(R/C).read_text()
        for token in ['V293_OS_QInit_call_return','V293_MemClr_call_owned oldqueues','V293_zero4_comptr_null_owned','V293_tick_void_return','V293_raw_cells_return_many','salloclv_step','exact Return']:self.assertIn(token,s)
        self.assertIn('Tarray V293_q_type 4',c);self.assertIn('Tcom_ptr 414%Z',c);self.assertIn('swhile (V293_q_link_guard ix)',c);self.assertIn('(V293_q_ptr_field pq1) (evar pq2)',c)
        for i in range(3):self.assertIn('exact G'+str(i),s)
        self.assertIn('V293_rdy_while_false;exact G3',s)
        for token in ['Axiom','Admitted','Parameter','Conjecture']:self.assertNotIn(token,s)
        for src,key in [(C,'code'),(P,'proof')]:
            x=read(L/'proof-report.json');self.assertEqual(read(L/x[key+'_result'])['exit'],0);self.assertEqual(sha(R/src),sha(L/x[key+'_snapshot']))
    def test_independent88_same_memory_loads_and_caller(self):
        s=(R/B).read_text();self.assertNotIn('Require Import CertiOS.audit.probes.',s)
        for token in ['QueueLiteralEntry','QueueLiteralAST','QueueFinalValid','length QueueFinalCells=88%nat','repeat (Byte (Byte.repr 255)) 96','set emp 41%Z (110%positive,Tint32)']:self.assertIn(token,s)
        claim=s.split('Theorem QueueConcreteExecution :',1)[1].split('Proof.',1)[0]
        self.assertIn('load tp Mf a=Some v',claim);self.assertIn('get Mf (b,Z.of_nat k)=None',claim);self.assertNotIn('rule_type_val_match',claim)
        self.assertIn('load Tint16 Ms (90%positive,0)=Some (Vint32 (Int.repr 3))',claim)
        x=read(L/'proof-report.json');self.assertEqual(x['concrete_load_instances'],4+80+1+3);self.assertEqual(x['freed_local_bytes'],12)
        self.assertEqual(read(L/x['probe_result'])['exit'],0);self.assertEqual(sha(R/B),sha(L/x['probe_snapshot']))
    def test_prospective_whole_call_ablation_and_failed_predictions_retained(self):
        p=read(L/'ablation-plan02.json');x=read(L/'ablation-result.json');status=read(L/'ablation-plan-status.json')
        self.assertTrue(p['frozen_before_execution']);self.assertEqual(p['positive_probe_sha256'],sha(R/B));self.assertTrue(status['original_plan_retained'])
        self.assertEqual(status['original_plan_sha256'],sha(L/'ablation-plan.json'));self.assertIn('invalid',status['status'])
        for key in ['passed','single_factor','all_other_fixture_inputs_unchanged','zero_step_noop_deletion','failed_candidates_retained']:self.assertTrue(x[key])
        self.assertFalse(x['individual_internal_mechanisms_tested']);self.assertFalse(x['all_execution_safety'])
        for n in ['ablation-endpoints','ablation-endpoints02']:self.assertNotEqual(read(L/(n+'.json'))['exit'],0)
        self.assertEqual(read(L/'ablation-endpoints03.json')['exit'],0)
        self.assertEqual(x['measurements']['nonlink_byte_offset4'],dict(baseline=0,removed=255));self.assertEqual(x['measurements']['free_head'],dict(baseline='82:0',removed='121:0'))
        s=(L/'ablation-endpoints03.v.snapshot.txt').read_text();self.assertIn('QueuePointerByteIsNotAddressLowByte',s)
        self.assertIn('QueueMeasuredBaseline',s);self.assertIn('QueueMeasuredRemoved',s);self.assertIn('apply c_stepstar0',s)
    def test_four_distinct_final_interface_controls(self):
        p=read(L/'control-plan.json');rows=read(L/'control-results.json');positive=(L/'positive.v.snapshot.txt').read_text()
        self.assertTrue(p['frozen_before_execution']);self.assertEqual(p['positive_sha256'],sha(R/B));self.assertEqual(p['positive_harness_sha256'],sha(L/'positive.v.snapshot.txt'))
        self.assertEqual(len(rows),5);self.assertEqual({r['name'] for r in rows},{'positive','wrong-first-link','wrong-tail','wrong-free-head','corrupt-frame'})
        for row in rows:
            self.assertTrue(row['expected_result_observed']);self.assertTrue(row['proofs_unchanged']);self.assertTrue(row['single_factor']);self.assertFalse(row['all_execution_safety_credit'])
            s=(L/(row['name']+'.v.snapshot.txt')).read_text();self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',s,re.S),re.findall(r'Proof\.(.*?)Qed\.',positive,re.S))
            if row['name']!='positive':self.assertEqual(row['actual_error_lines'],[row['expected_error_line']])
        self.assertEqual(len({r['expected_error_line'] for r in rows if r['name']!='positive'}),4)
    def test_build_and_trust(self):
        x=read(L/'build.json');self.assertEqual(x['exit'],0);self.assertEqual(x['active_sources'],211);self.assertEqual(x['old_products_reused'],1045);self.assertFalse(x['source_only_cold_build'])
        x=read(L/'trust.json');self.assertTrue(x['passed']);self.assertEqual(x['roots_printed'],100);self.assertEqual(len(x['roots']),100);self.assertEqual([c['exit'] for c in x['commands']],[0,0]);self.assertTrue(x['assumptions_allowed'])
    def test_claim_boundaries_and_adversarial_review(self):
        x=read(L/'proof-report.json');review=read(L/'adversarial-review.json');self.assertGreaterEqual(len(review),20)
        for row in review:self.assertTrue(row['resolution']);self.assertIn(row['kind'],['test','bounded claim','limitation'])
        for key in ['native_while','real_MemClr_call','full_function_call','same_Mf_writable_ownership','nonzero_finite_entry','whole_call_neutralization','callee_freshness_entry_premises','return_resources_Away_premise']:self.assertTrue(x[key])
        for key in ['verified_frontend','source_only_cold_build','local_Hoare','all_execution_safety','OSInit_seventh_call_linked','OSInit_reachability','OSStart_reachability','full_94_function_program_instantiated','GOOD_OS','same_program_K1_K4','ucos3_started','six_gates_promoted','git_commit_or_push']:self.assertFalse(x[key])
        self.assertEqual(x['formal_six_gates'],[94,1,1,1,1,0]);self.assertEqual(x['goal_status'],'active')
