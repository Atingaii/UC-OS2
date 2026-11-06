"""Three real configured initialization calls on a single memory trajectory."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage49-init-chain'
C='certiucos/v293/code/V293OSInitChain.v';P='certiucos/v293/proofs/V293InitChain.v';B='audit/probes/V293InitChainProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class InitChainTests(unittest.TestCase):
    def test_previous_inputs_and_products_preserved(self):
        b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
        for p,h in b['files'].items():
            if p not in allowed:self.assertEqual(sha(R/p),h,p)
        for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
        active=[p for p in (R/'_CoqProject').read_text().splitlines() if p.endswith('.v')]
        expected=b['sources']+[C,P];self.assertEqual(active[:len(expected)],expected)
        self.assertEqual(len(b['sources']),195);self.assertEqual(len(b['products']),975)
    def test_exact_OSInit_order_and_unresolved_hook_boundary(self):
        x=read(L/'source/result.json');y=read(L/'source-connection.json')
        self.assertTrue(x['passed']);self.assertTrue(x['all94_identities_equal']);self.assertTrue(y['passed'])
        self.assertEqual(x['source_identity'],'74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da')
        self.assertEqual(y['input_sha256'],sha(L/'source/result.json'))
        self.assertEqual(y['call_order'],['OSInitHookBegin','OS_InitMisc','OS_InitRdyList','OS_InitTCBList','OS_InitEventList','OS_FlagInit','OS_MemInit','OS_QInit','OS_InitTaskIdle','OS_InitTaskStat','OSInitHookEnd'])
        self.assertEqual(y['slice_positions_zero_based'],[1,2,3]);self.assertTrue(y['starts_after_unresolved_hook'])
        for row in y['port_hooks']:self.assertFalse(row['defined']);self.assertGreater(row['declarations'],0)
        for row in y['subfunctions']:self.assertEqual(row['prior_sha256'],sha(R/row['prior_evidence']))
        self.assertFalse(y['verified_frontend']);self.assertFalse(y['full_OSInit'])
    def test_no_intermediate_storage_or_freshness_oracle_premise(self):
        s=(R/P).read_text();stmt=s.split('Theorem V293_OSInit_three_calls :',1)[1].split('Proof.',1)[0];pre=stmt.split('  exists Mmisc Mrdy Mf')[0]
        self.assertNotIn('fresh ',pre);self.assertNotIn('Mmisc',pre);self.assertNotIn('Mrdy',pre);self.assertNotIn('Mf',pre)
        for token in ['P misc=Some','P ready=Some','P tcbs=Some','P clear=Some','(ge,emp,M,ir,aux,O,op)','V293_init_resources slots false']:self.assertIn(token,pre)
        for token in ['Axiom','Admitted','Parameter','Conjecture']:self.assertNotIn(token,s)
        self.assertEqual(stmt.count('cstepstar P'),4)
    def test_real_call_composition_and_freshness_from_actual_memory(self):
        s=(R/P).read_text();body=s.split('Theorem V293_OSInit_three_calls :',1)[1].split('Proof.',1)[1]
        for token in ['V293_init_slots_call slots P','V293_OS_InitRdyList_call_return P','V293_OS_InitTCBList_call_return oldtcbs','V293_init_fresh_four Mmisc','V293_init_fresh_four Mrdy','exact MiscExec','exact ReadyExec','exact TCBExec','V293_raw_cells_return_many','exact Returned']:self.assertIn(token,body)
        helper=s.split('Lemma V293_init_fresh_four :',1)[1].split('Qed.',1)[0]
        for token in ['HalfPermMap.bounded M','V293_cells_upper cells','Pos.lt_irrefl']:self.assertIn(token,helper)
        self.assertIn('sallocend_step',s);self.assertIn('sfreeend_step',s)
        report=read(L/'proof-report.json');self.assertEqual(read(L/report['proof_result'])['exit'],0)
        self.assertEqual(sha(R/P),sha(L/report['proof_snapshot']))
    def test_literal_finite_entry_and_same_Mf_49_reads(self):
        s=(R/B).read_text();self.assertNotIn('Require Import CertiOS.audit.probes.',s)
        for token in ['ChainLiteralFullEntry','ChainSlotEntry','ChainLiteralOrder','ChainConcreteExecution','ChainExtrasValid','ChainExtraCount','ChainEntryMemory','repeat Vundef 728','set emp 41%Z (110%positive,Tint32)']:self.assertIn(token,s)
        self.assertIn('get Mrdy (bri,0)=None',s);self.assertIn('get Mf (c,Z.of_nat k)=None',s)
        self.assertNotIn('get Mf (bri,0)=None',s)
        x=read(L/'proof-report.json');self.assertEqual(x['concrete_load_instances'],12+1+2+13+7+10+4)
        self.assertEqual(read(L/x['probe_result'])['exit'],0);self.assertEqual(sha(R/B),sha(L/x['probe_snapshot']))
    def test_frozen_single_conclusion_controls(self):
        plan=read(L/'control-plan.json');rows=read(L/'control-results.json');s=(R/B).read_text();positive=(L/'positive.v.snapshot.txt').read_text()
        self.assertEqual(sha(L/'positive.v.snapshot.txt'),plan['positive_harness_sha256'])
        self.assertTrue(plan['frozen_before_execution']);self.assertEqual(plan['positive_sha256'],sha(R/B));self.assertEqual(len(rows),5)
        for row in rows:
            self.assertTrue(row['expected_result_observed']);self.assertTrue(row['proofs_unchanged']);self.assertTrue(row['single_factor'])
            self.assertFalse(row['all_execution_safety_credit']);snap=(L/(row['name']+'.v.snapshot.txt')).read_text()
            self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',snap,re.S),re.findall(r'Proof\.(.*?)Qed\.',positive,re.S))
            self.assertEqual(sha(L/(row['name']+'.v.snapshot.txt')),row['source_sha256'])
            if row['name']!='positive':self.assertEqual(row['actual_error_lines'],[row['expected_error_line']])
        self.assertIn('not mechanism ablations',plan['scope'])
    def test_formal_build_and_kernel_trust(self):
        x=read(L/'build.json');self.assertEqual(x['exit'],0);self.assertEqual(x['active_sources'],197)
        self.assertEqual(x['old_products_reused'],975);self.assertFalse(x['source_only_cold_build'])
        x=read(L/'trust.json');self.assertTrue(x['passed']);self.assertEqual(x['roots_printed'],64);self.assertEqual(len(x['roots']),64)
        self.assertEqual([c['exit'] for c in x['commands']],[0,0]);self.assertTrue(x['assumptions_allowed'])
        self.assertNotIn('MemoryNotFull',str(x['assumptions']))
    def test_bounded_claims_and_review(self):
        x=read(L/'proof-report.json');review=read(L/'adversarial-review.json');self.assertGreaterEqual(len(review),10)
        for row in review:self.assertTrue(row['resolution']);self.assertIn(row['kind'],['test','bounded claim','limitation'])
        for key in ['same_program_same_trajectory','fresh_choices_constructed_after_calls','same_Mf_writable_ownership','nonempty_shadowed_caller','real_three_calls']:self.assertTrue(x[key])
        for key in ['OSInit_reachability','OSStart_reachability','all_execution_safety','GOOD_OS','same_program_K1_K4','ucos3_started','six_gates_promoted','git_commit_or_push']:self.assertFalse(x[key])
        self.assertEqual(x['formal_six_gates'],[94,1,1,1,1,0]);self.assertEqual(x['goal_status'],'active')
