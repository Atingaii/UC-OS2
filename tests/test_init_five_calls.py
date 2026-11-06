"""Five adjacent real calls; bounded execution, provenance and adversarial controls."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage53-init-five-calls'
C='certiucos/v293/code/V293OSInitFlagChain.v';P='certiucos/v293/proofs/V293InitFlagChain.v';B='audit/probes/V293InitFiveCallsProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class InitFiveCallsTests(unittest.TestCase):
    def test_old_inputs_and_reusable_products_unchanged(self):
        b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
        for p,h in b['files'].items():
            if p not in allowed:self.assertEqual(sha(R/p),h,p)
        for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
        active=[p for p in (R/'_CoqProject').read_text().splitlines() if p.endswith('.v')]
        expected=b['sources']+[C,P];self.assertEqual(active[:len(expected)],expected)
        self.assertEqual(len(b['sources']),203);self.assertEqual(len(b['products']),1015)
    def test_exact_source_and_five_contiguous_statements(self):
        x=read(L/'source/result.json');y=read(L/'source-connection.json')
        self.assertTrue(x['passed']);self.assertTrue(x['all94_identities_equal']);self.assertTrue(y['passed'])
        self.assertEqual(x['source_identity'],'74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da')
        self.assertEqual(x['function']['name'],'OSInit');self.assertEqual(y['slice_positions_zero_based'],[1,2,3,4,5])
        self.assertEqual(x['call_order'][1:6],['OS_InitMisc','OS_InitRdyList','OS_InitTCBList','OS_InitEventList','OS_FlagInit'])
        self.assertEqual(len(y['subfunctions']),5);self.assertTrue(all(not p['defined'] for p in y['port_hooks']))
        for row in y['subfunctions']:self.assertEqual(sha(R/row['prior_evidence']),row['prior_sha256'])
        self.assertFalse(y['full_OSInit']);self.assertFalse(y['verified_frontend'])
        self.assertIn('sseq (V293_init_four_calls misc ready tcbs events) (scall flags nil)',(R/C).read_text())
    def test_actual_event_return_drives_flag_call_and_freshness(self):
        s=(R/P).read_text();stmt=s.split('Theorem V293_OSInit_five_calls :',1)[1].split('Proof.',1)[0]
        entry=stmt.split('  exists Mevent Mf bi bn b1 b2,')[0]
        for token in ['Mevent','fresh ','preallocated']:self.assertNotIn(token,entry)
        for token in ['V293_OSInit_four_calls slots oldtcbs oldprios oldevents (flold++frame)','V293_init_fresh_four Mevent (V293_flag_call_result','flags clear dest size ftable fhead fi fn fp1 fp2 fbt fbf bi bn b1 b2 fvf','exact Prefix','exact FlagExec','exact Returned']:
            self.assertIn(token,s)
        for token in ['Axiom','Admitted','Parameter','Conjecture']:self.assertNotIn(token,s)
        x=read(L/'proof-report.json')
        for src,key in [(C,'code'),(P,'proof')]:
            self.assertEqual(read(L/x[key+'_result'])['exit'],0);self.assertEqual(sha(R/src),sha(L/x[key+'_snapshot']))
    def test_independent_finite_entry_and_122_same_final_loads(self):
        s=(R/B).read_text();self.assertNotIn('Require Import CertiOS.audit.probes.',s)
        for token in ['FiveLiteralFullEntry','FiveLiteralOrder','FiveChecksValid','FiveChecksInFinal','FiveConcreteExecution','length FiveChecks=122%nat','repeat (Byte (Byte.repr 255)) 60','set emp 41%Z (110%positive,Tint32)']:
            self.assertIn(token,s)
        stmt=s.split('Theorem FiveConcreteExecution :',1)[1].split('Proof.',1)[0]
        self.assertIn('load tp Mf a=Some v',stmt);self.assertNotIn('rule_type_val_match',stmt)
        self.assertIn('fresh Mevent bi',stmt);self.assertIn('get Mf (c,Z.of_nat k)=None',stmt)
        x=read(L/'proof-report.json');self.assertEqual(x['concrete_load_instances'],76+46);self.assertEqual(x['flag_freed_local_bytes'],12)
        self.assertEqual(read(L/x['probe_result'])['exit'],0);self.assertEqual(sha(R/B),sha(L/x['probe_snapshot']))
    def test_prospective_whole_fifth_call_deletion_ablation(self):
        p=read(L/'ablation-plan.json');x=read(L/'ablation-result.json')
        self.assertTrue(p['frozen_before_execution']);self.assertEqual(p['baseline_probe_sha256'],sha(L/'probe03.v.snapshot.txt'))
        for key in ['passed','single_factor','all_other_fixture_inputs_unchanged']:self.assertTrue(x[key])
        self.assertFalse(x['individual_internal_mechanisms_tested']);self.assertFalse(x['all_execution_safety'])
        self.assertEqual(x['measurements']['flag_Type_byte_at_194_0'],dict(baseline=0,removed=255))
        self.assertEqual(x['measurements']['flag_free_head_at_195_0'],dict(baseline='194:0',removed='214:0'))
        self.assertEqual(x['measurements']['event_Type_byte_at_192_0'],dict(baseline=0,removed=0))
        self.assertEqual(x['measurements']['ready_group_at_161_0'],dict(baseline=0,removed=0))
        s=(R/B).read_text().split('Theorem FiveWithoutFlagCall :',1)[1]
        self.assertIn('V293_OSInit_four_calls FiveSlots',s);self.assertIn('FiveFlagBytes++FiveFlagHead++FiveFrame',s)
        self.assertNotIn('V293_OSInit_five_calls',s)
    def test_single_conclusion_controls_at_specific_readback_lines(self):
        p=read(L/'control-plan.json');rows=read(L/'control-results.json');positive=(L/'positive.v.snapshot.txt').read_text()
        self.assertTrue(p['frozen_before_execution']);self.assertEqual(p['positive_sha256'],sha(R/B));self.assertEqual(len(rows),5)
        self.assertEqual(p['positive_harness_sha256'],sha(L/'positive.v.snapshot.txt'))
        self.assertEqual({r['name'] for r in rows},{'positive','wrong-first-link','wrong-free-head','lost-ready-zero','corrupt-frame'})
        for row in rows:
            self.assertTrue(row['expected_result_observed']);self.assertTrue(row['proofs_unchanged']);self.assertTrue(row['single_factor']);self.assertFalse(row['all_execution_safety_credit'])
            snap=(L/(row['name']+'.v.snapshot.txt')).read_text()
            self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',snap,re.S),re.findall(r'Proof\.(.*?)Qed\.',positive,re.S))
            if row['name']!='positive':self.assertEqual(row['actual_error_lines'],[row['expected_error_line']])
        self.assertEqual(len({r['expected_error_line'] for r in rows if r['name']!='positive'}),4)
    def test_formal_build_and_kernel_trust(self):
        x=read(L/'build.json');self.assertEqual(x['exit'],0);self.assertEqual(x['active_sources'],205);self.assertEqual(x['old_products_reused'],1015);self.assertFalse(x['source_only_cold_build'])
        x=read(L/'trust.json');self.assertTrue(x['passed']);self.assertEqual(x['roots_printed'],85);self.assertEqual(len(x['roots']),85)
        self.assertEqual([c['exit'] for c in x['commands']],[0,0]);self.assertTrue(x['assumptions_allowed'])
    def test_bounded_review_no_formal_gate_promotion(self):
        x=read(L/'proof-report.json');review=read(L/'adversarial-review.json');self.assertGreaterEqual(len(review),15)
        for row in review:self.assertTrue(row['resolution']);self.assertIn(row['kind'],['test','bounded claim','limitation'])
        for key in ['real_five_calls','same_program_same_trajectory','fresh_constructed_from_actual_Event_return_memory','same_Mf_writable_ownership','nonzero_finite_entry','whole_flag_call_deletion_ablation']:self.assertTrue(x[key])
        for key in ['intermediate_memory_premise','intermediate_freshness_premise','preallocated_callee_locals','old_prefix_freed_bytes_final_claim','verified_frontend','local_Hoare','all_execution_safety','OSInit_reachability','OSStart_reachability','full_94_function_program_instantiated','GOOD_OS','same_program_K1_K4','ucos3_started','six_gates_promoted','git_commit_or_push']:self.assertFalse(x[key])
        self.assertEqual(x['formal_six_gates'],[94,1,1,1,1,0]);self.assertEqual(x['goal_status'],'active')
