"""OSInit seven-call composition: actual return memory, independent fixture and bounded claims."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage57-init-seven-calls'
C='certiucos/v293/code/V293OSInitQChain.v';P='certiucos/v293/proofs/V293InitQChain.v';B='audit/probes/V293InitSevenCallsProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class InitSevenCallsTests(unittest.TestCase):
 def test_previous_inputs_and_products_preserved(self):
  b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
  for p,h in b['files'].items():
   if p not in allowed:self.assertEqual(sha(R/p),h,p)
  for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
  active=[p for p in (R/'_CoqProject').read_text().splitlines() if p.endswith('.v')];expected=b['sources']+[C,P]
  self.assertEqual(active[:len(expected)],expected);self.assertEqual(len(b['sources']),211);self.assertEqual(len(b['products']),1055)
 def test_fixed_source_and_literal_order(self):
  s=read(L/'source/result.json');x=read(L/'source-connection.json');self.assertTrue(x['passed']);self.assertTrue(s['all94_identities_equal']);self.assertEqual(x['slice_positions_zero_based'],[1,2,3,4,5,6,7]);self.assertEqual(len(x['subfunctions']),7)
  self.assertEqual(s['call_order'][1:8],['OS_InitMisc','OS_InitRdyList','OS_InitTCBList','OS_InitEventList','OS_FlagInit','OS_MemInit','OS_QInit'])
  for row in x['subfunctions']:self.assertEqual(sha(R/row['prior_evidence']),row['prior_sha256'])
  self.assertEqual(s['source_identity'],'74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da');self.assertTrue(x['starts_after_unresolved_hook']);self.assertFalse(x['verified_frontend']);self.assertEqual(len(x['port_hooks']),2)
  c=(R/C).read_text();self.assertIn('sseq (V293_init_six_calls misc ready tcbs events flags mems) (scall queues nil)',c)
  b=(R/B).read_text();self.assertIn('Lemma SevenLiteralOrder',b);self.assertIn('(scall 208%Z nil).',b)
 def test_actual_six_return_constructs_four_fresh_blocks(self):
  s=(R/P).read_text();stmt=s.split('Theorem V293_OSInit_seven_calls :',1)[1].split('Proof.',1)[0];entry=stmt.split('  exists Msix Mf bi bn b1 b2,')[0]
  self.assertNotIn('Msix',entry);self.assertNotIn('fresh ',entry)
  for token in ['V293_OSInit_six_calls slots oldtcbs oldprios oldevents oldflags oldmems (qold++frame)','V293_init_fresh_four Msix (V293_q_call_result','V293_OS_QInit_call_return oldqueues rest P ks ge caller Msix','NoDup (V293_q_call_blocks','exact Prefix','exact QueueExec','exact Returned']:self.assertIn(token,s)
  for token in ['Axiom','Admitted','Parameter','Conjecture']:self.assertNotIn(token,s)
  x=read(L/'proof-report.json')
  for src,key in [(C,'code'),(P,'proof')]:self.assertEqual(sha(R/src),sha(L/x[key+'_snapshot']));self.assertEqual(read(L/x[key+'_result'])['exit'],0)
 def test_independent293_same_memory_readbacks_and_caller(self):
  s=(R/B).read_text();self.assertNotIn('Require Import CertiOS.audit.probes.',s)
  for token in ['SevenLiteralFullEntry','SevenLiteralOrder','length SevenChecks=293%nat','repeat (Byte (Byte.repr 255)) 96','set emp 41%Z (110%positive,Tint32)','SevenQEnvironment']:self.assertIn(token,s)
  claim=s.split('Theorem SevenConcreteExecution :',1)[1].split('Proof.',1)[0];self.assertIn('load tp Mf a=Some v',claim);self.assertIn('get Mf (c,Z.of_nat k)=None',claim);self.assertNotIn('rule_type_val_match',claim)
  x=read(L/'proof-report.json');self.assertEqual(x['concrete_load_instances'],208+85);self.assertEqual(x['queue_freed_local_bytes'],12);self.assertEqual(x['fixture_function_count'],8);self.assertEqual(sha(R/B),sha(L/x['probe_snapshot']));self.assertEqual(read(L/x['probe_result'])['exit'],0)
 def test_prospective_seventh_only_noop_ablation(self):
  plan=read(L/'ablation-plan.json');x=read(L/'ablation-result.json');self.assertTrue(plan['frozen_before_execution']);self.assertTrue(x['passed']);self.assertTrue(x['single_factor']);self.assertFalse(x['individual_internal_mechanisms_tested']);self.assertEqual(plan['measurements']['queue_nonlink4'],[0,255]);self.assertEqual(plan['measurements']['previous_mem_link'],['196:20','196:20'])
  self.assertEqual(read(L/'ablation01.json')['exit'],1);self.assertEqual(read(L/'ablation02.json')['exit'],-2);self.assertEqual(read(L/'ablation03.json')['exit'],0);s=(L/'ablation02.v.snapshot.txt').read_text();old=(L/'ablation01.v.snapshot.txt').read_text();self.assertTrue(s.endswith(old));self.assertEqual(len(s)-len(old),len('Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.\n'))
  latest=(L/'ablation03.v.snapshot.txt').read_text();self.assertEqual(re.findall(r'Theorem (.*?)Proof\.',s,re.S),re.findall(r'Theorem (.*?)Proof\.',latest,re.S));self.assertTrue(read(L/'ablation-search-diagnosis.json')['statements_unchanged']);removed=latest.split('Theorem SevenWithoutQueue :',1)[1];self.assertIn('sseq (V293_init_six_calls',removed);self.assertIn('(sskip None)),(kenil,ks))',removed);self.assertIn('V293_OSInit_six_calls SevenSlots',removed);self.assertNotIn('V293_OSInit_seven_calls',removed);self.assertIn('SevenBaselineMeasurements',s);self.assertEqual(x['explicit_baseline_measurements'],6);self.assertEqual(x['explicit_removed_measurements'],6)
 def test_four_distinct_final_interface_negative_controls(self):
  p=read(L/'control-plan.json');rows=read(L/'control-results.json');self.assertTrue(p['frozen_before_execution']);self.assertEqual(p['positive_sha256'],sha(R/B));self.assertEqual(len(rows),5);self.assertEqual(p['positive_harness_sha256'],sha(L/'positive.v.snapshot.txt'))
  positive=(L/'positive.v.snapshot.txt').read_text()
  for row in rows:
   self.assertTrue(row['expected_result_observed']);self.assertTrue(row['proofs_unchanged']);self.assertTrue(row['single_factor']);s=(L/(row['name']+'.v.snapshot.txt')).read_text();self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',s,re.S),re.findall(r'Proof\.(.*?)Qed\.',positive,re.S))
   if row['name']!='positive':self.assertEqual(row['actual_error_lines'],[row['expected_error_line']])
  self.assertEqual(len({r['expected_error_line'] for r in rows if r['name']!='positive'}),4)
 def test_build_and_trust(self):
  b=read(L/'build.json');self.assertEqual(b['exit'],0);self.assertEqual(b['active_sources'],213);self.assertEqual(b['old_products_reused'],1055);self.assertFalse(b['source_only_cold_build']);x=read(L/'trust.json');self.assertTrue(x['passed']);self.assertEqual(x['roots_printed'],100);self.assertEqual(len(x['roots']),100);self.assertEqual([c['exit'] for c in x['commands']],[0,0]);self.assertTrue(x['assumptions_allowed']);self.assertTrue(read(L/'proof-report.json')['ablation_assumptions_allowed'])
 def test_honest_bounded_claims_and_adversarial_review(self):
  x=read(L/'proof-report.json');rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),20)
  for row in rows:self.assertTrue(row['resolution']);self.assertIn(row['kind'],['test','bounded claim','limitation'])
  for k in ['real_seven_calls','same_program_same_trajectory','fresh_constructed_from_actual_six_return_memory','same_Mf_writable_ownership','whole_queue_call_noop_ablation']:self.assertTrue(x[k])
  for k in ['intermediate_memory_premise','intermediate_freshness_premise','preallocated_callee_locals','old_prefix_freed_bytes_final_claim','verified_frontend','local_Hoare','all_execution_safety','OSInit_reachability','OSStart_reachability','full_94_function_program_instantiated','GOOD_OS','same_program_K1_K4','ucos3_started','six_gates_promoted','git_commit_or_push']:self.assertFalse(x[k])
  self.assertEqual(x['formal_six_gates'],[94,1,1,1,1,0]);self.assertEqual(x['goal_status'],'active');self.assertEqual(read(L/'function-progress.json')['formal_states'],dict(located=True,modeled=False,specified=False,local_hoare=False,component_linked=False,full_target_linked=False))
