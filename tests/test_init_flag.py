"""Exact configured FlagInit call: independent bytes, lifecycle and bounded controls."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage52-init-flag'
C='certiucos/v293/code/V293OSFlagInit.v';P='certiucos/v293/proofs/V293FlagInit.v';B='audit/probes/V293FlagInitProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class InitFlagTests(unittest.TestCase):
    def test_old_inputs_and_reusable_products_unchanged(self):
        b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
        for p,h in b['files'].items():
            if p not in allowed:self.assertEqual(sha(R/p),h,p)
        for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
        active=[p for p in (R/'_CoqProject').read_text().splitlines() if p.endswith('.v')]
        expected=b['sources']+[C,P];self.assertEqual(active[:len(expected)],expected)
        self.assertEqual(len(b['sources']),201);self.assertEqual(len(b['products']),1005)
    def test_source_identity_layout_and_native_loop(self):
        x=read(L/'source/result.json');y=read(L/'source/flag.json')
        self.assertTrue(x['passed']);self.assertTrue(x['all94_identities_equal']);self.assertTrue(y['passed'])
        self.assertEqual(y['source_identity'],'74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da')
        self.assertEqual(y['function']['name'],'OS_FlagInit');self.assertEqual(y['function']['preprocessed_body_sha256'],'5b8594c0edd6c5b4f91eb0e4c6225265da37f9b3c2034032c27102ce3479a62e')
        self.assertEqual(y['layout'],dict(size=12,count=5,table=60,Type=0,WaitList=4,Flags=8,Flags_width=2))
        self.assertEqual(y['layout_exit'],0);self.assertEqual(y['loop_iterations'],4);self.assertFalse(y['verified_frontend'])
        s=(R/C).read_text();self.assertIn('swhile (V293_flag_link_guard ix)',s);self.assertIn('Tarray V293_flag_type 5',s)
        self.assertIn('(econst32 (Int.repr 4))',s);self.assertIn('sseq (scall clear',s)
    def test_full_real_call_and_local_lifecycle(self):
        s=(R/P).read_text()
        for token in ['Theorem V293_OS_FlagInit_call_return','V293_OS_FlagInit_clear_call','V293_MemClr_call_owned oldflags','V293_zero4_null_owned','V293_tick_void_return','V293_raw_cells_return_many','salloclv_step','exact Return']:
            self.assertIn(token,s)
        for token in ['Axiom','Admitted','Parameter','Conjecture']:self.assertNotIn(token,s)
        for i in range(4):self.assertIn('exact G'+str(i),s)
        self.assertIn('V293_rdy_while_false;exact G4',s)
        x=read(L/'proof-report.json')
        for src,key in [(C,'code'),(P,'proof')]:
            self.assertEqual(read(L/x[key+'_result'])['exit'],0);self.assertEqual(sha(R/src),sha(L/x[key+'_snapshot']))
    def test_independent_finite_entry_all49_loads_and_caller(self):
        s=(R/B).read_text();self.assertNotIn('Require Import CertiOS.audit.probes.',s)
        for token in ['FlagLiteralEntry','FlagLiteralAST','FlagFinalValid','FlagConcreteExecution','length FlagFinalCells=49%nat','repeat (Byte (Byte.repr 255)) 60','set emp 41%Z (110%positive,Tint32)']:
            self.assertIn(token,s)
        stmt=s.split('Theorem FlagConcreteExecution :',1)[1].split('Proof.',1)[0]
        self.assertIn('load tp Mf a=Some v',stmt);self.assertNotIn('rule_type_val_match',stmt)
        self.assertIn('get Mf (b,Z.of_nat k)=None',stmt);self.assertIn('load Tint16 Ms (90%positive,0)=Some (Vint32 (Int.repr 4))',stmt)
        x=read(L/'proof-report.json');self.assertEqual(x['concrete_load_instances'],10+35+1+3);self.assertEqual(x['freed_local_bytes'],12)
        self.assertEqual(read(L/x['probe_result'])['exit'],0);self.assertEqual(sha(R/B),sha(L/x['probe_snapshot']))
    def test_prospective_whole_call_neutralization_only(self):
        p=read(L/'ablation-plan.json');x=read(L/'ablation-result.json')
        self.assertTrue(p['frozen_before_execution']);self.assertEqual(p['baseline_probe_sha256'],sha(L/'probe01.v.snapshot.txt'))
        for key in ['passed','single_factor','all_other_fixture_inputs_unchanged','zero_step_noop_deletion']:self.assertTrue(x[key])
        self.assertFalse(x['individual_internal_mechanisms_tested']);self.assertFalse(x['all_execution_safety'])
        self.assertEqual(x['measurements']['Type_byte'],dict(baseline=0,removed=255))
        self.assertEqual(x['measurements']['Flags_low_byte'],dict(baseline=0,removed=255))
        self.assertEqual(x['measurements']['free_head'],dict(baseline='82:0',removed='121:0'))
        s=(R/B).read_text().split('Theorem FlagWithoutCall :',1)[1]
        self.assertIn('apply c_stepstar0',s);self.assertIn('exact FlagLiteralEntry',s);self.assertNotIn('FlagConcreteExecution',s)
    def test_controls_reject_at_four_distinct_final_readback_lines(self):
        p=read(L/'control-plan.json');rows=read(L/'control-results.json');positive=(L/'positive.v.snapshot.txt').read_text()
        self.assertTrue(p['frozen_before_execution']);self.assertEqual(p['positive_sha256'],sha(R/B));self.assertEqual(len(rows),5)
        self.assertEqual(p['positive_harness_sha256'],sha(L/'positive.v.snapshot.txt'))
        self.assertEqual({r['name'] for r in rows},{'positive','wrong-first-link','wrong-tail','wrong-free-head','corrupt-frame'})
        for row in rows:
            self.assertTrue(row['expected_result_observed']);self.assertTrue(row['proofs_unchanged']);self.assertTrue(row['single_factor']);self.assertFalse(row['all_execution_safety_credit'])
            snap=(L/(row['name']+'.v.snapshot.txt')).read_text()
            self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',snap,re.S),re.findall(r'Proof\.(.*?)Qed\.',positive,re.S))
            if row['name']!='positive':self.assertEqual(row['actual_error_lines'],[row['expected_error_line']])
        self.assertEqual(len({r['expected_error_line'] for r in rows if r['name']!='positive'}),4)
    def test_formal_build_and_kernel_trust(self):
        x=read(L/'build.json');self.assertEqual(x['exit'],0);self.assertEqual(x['active_sources'],203);self.assertEqual(x['old_products_reused'],1005);self.assertFalse(x['source_only_cold_build'])
        x=read(L/'trust.json');self.assertTrue(x['passed']);self.assertEqual(x['roots_printed'],76);self.assertEqual(len(x['roots']),76)
        self.assertEqual([c['exit'] for c in x['commands']],[0,0]);self.assertTrue(x['assumptions_allowed'])
    def test_claim_boundaries_and_review(self):
        x=read(L/'proof-report.json');review=read(L/'adversarial-review.json');self.assertGreaterEqual(len(review),20)
        for row in review:self.assertTrue(row['resolution']);self.assertIn(row['kind'],['test','bounded claim','limitation'])
        for key in ['native_while','real_MemClr_call','full_function_call','same_Mf_writable_ownership','nonzero_finite_entry','whole_call_neutralization','callee_freshness_entry_premises','return_resources_Away_premise']:self.assertTrue(x[key])
        for key in ['verified_frontend','source_only_cold_build','local_Hoare','all_execution_safety','OSInit_fifth_call_linked','OSInit_reachability','OSStart_reachability','full_94_function_program_instantiated','GOOD_OS','same_program_K1_K4','ucos3_started','six_gates_promoted','git_commit_or_push']:self.assertFalse(x[key])
        self.assertEqual(x['formal_six_gates'],[94,1,1,1,1,0]);self.assertEqual(x['goal_status'],'active')
