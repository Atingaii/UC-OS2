"""真实psp写入与七参数入口；不把条件Hook返回当实现。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage68-task-create-tcb-entry'
C='certiucos/v293/code/V293OSTaskCreateExtCalls.v';P='certiucos/v293/proofs/V293TaskCreateTCBEntry.v';B='audit/probes/V293TaskCreateTCBEntryProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TaskCreateTCBEntryTests(unittest.TestCase):
 def test_baseline_preserved(self):
  b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
  self.assertEqual((len(b['files']),len(b['sources']),len(b['products'])),(15309,228,1140))
  for p,h in b['files'].items():
   if p not in allowed:self.assertEqual(sha(R/p),h,p)
  for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
  self.assertEqual([p for p in (R/'_CoqProject').read_text().splitlines() if p.endswith('.v')][:230],b['sources']+[C,P])
 def test_source_mapping_and_stable_interface(self):
  for p,n in [(C,'code02'),(P,'proof05'),(B,'probe01')]:
   self.assertEqual(sha(R/p),sha(L/(n+'.v.snapshot.txt')));self.assertEqual(read(L/(n+'.json'))['exit'],0)
   self.assertNotRegex((R/p).read_text(),r'\b(Axiom|Admitted|admit|Parameter|Conjecture)\b')
   self.assertNotIn('Require Import CertiOS.audit.probes.',(R/p).read_text())
  s=read(L/'source-connection.json');self.assertTrue(s['passed']);self.assertTrue(s['all94_identities_equal'])
  self.assertEqual(s['source_identity'],read(R/'audit/repaired-source-inventory.json')['source_identity_sha256'])
  self.assertEqual(s['AST_seven_argument_names'],['prio','psp','pbos','id','stk_size','pext','opt'])
  self.assertEqual(s['AST_seven_argument_types'],['INT8U','OS_STK *','OS_STK *','INT16U','INT32U','void *','INT16U'])
  self.assertTrue(s['function_pointer_argument_evaluated']);self.assertTrue(s['AST_psp_assignment_precedes_TCB_call']);self.assertTrue(s['AST_arguments_are_pure_variable_reads'])
  self.assertEqual(len(s['hook_declarations']),5)
  for h in s['hook_declarations']:self.assertFalse(h['defined'])
  src=(R/P).read_text();premises=src.split('Theorem V293_OSTaskCreateExt_to_TCB_under_stack_return :')[1].split(' exists Mf,')[0]
  for forbidden in ['evalval','evaltype','cstepstar']:self.assertNotIn(forbidden,premises)
  self.assertIn('V293_create_stack_return',premises)
  for n in ['V293_return_value_assign','V293_create_seven_arguments','V293_missing_stack_hook_cannot_return','HookReturn Mh AtHook','Mr&Returned&AfterHook','inversion Run']:self.assertIn(n,src)
 def test_independent_anchors_and_claim_bounds(self):
  src=(R/B).read_text()
  for n in ['BridgeLiteralReturnEntry','BridgeLiteralBodyEntry','BridgeActualAfterReturn','BridgeActualMissingStack','p=0%nat \/ p=12%nat','BridgeExpected p nonnull','load tp Mf a=Some v']:self.assertIn(n,src)
  p=read(L/'proof-report.json');self.assertEqual((p['independent_literal_body_entries'],p['independent_literal_return_anchors'],p['typed_reads_per_return_anchor']),(2,4,17))
  for k in ['return_anchor_unconditional','body_entry_conditional_on_real_stack_return','real_psp_store','actual_seven_argument_evaluation','TCB_sfexec','same_Mf_psp_and_second_TCB_argument','IE_universally_quantified','si_ci_preserved','actual_reached_missing_stack_hook','missing_hook_cannot_return_including_zero_steps']:self.assertTrue(p[k],k)
  for k in ['stack_return_requires_whole_M_identity','real_Hook_implementation','Hook_assumed_noop','fixed_program_stack_return','caller_function_allocation','creation_suffix','err_result_assignment','TCB_body_executed','stage65_full_TCB_call_linked','seven_OSInit_actual_memories_linked','local_Hoare','all_execution_safety','GOOD_OS','same_program_K1_K4','ucos3_started']:self.assertFalse(p[k],k)
  self.assertEqual(p['formal_six_gates'],[94,1,1,1,1,0])
 def test_endpoint_controls_and_single_factor_ablation(self):
  p=read(L/'control-plan.json');s=(L/'positive01.v.snapshot.txt').read_text();proofs=lambda x:re.findall(r'Proof\.(.*?)Qed\.',x,re.S)
  self.assertTrue(p['frozen_before_compilation']);self.assertEqual(sha(L/'positive01.v.snapshot.txt'),p['positive_sha256']);self.assertEqual(read(L/'positive01.json')['exit'],0)
  for n,v in p['variants'].items():
   t=(L/(n+'01.v.snapshot.txt')).read_text();a=s.index('Theorem '+v['theorem']);b=s.index('Proof.',a)
   self.assertEqual(t,s[:a]+s[a:b].replace(v['old'],v['new'],1)+s[b:]);self.assertEqual(proofs(s),proofs(t));self.assertEqual(sha(L/(n+'01.v.snapshot.txt')),v['sha256']);self.assertEqual(read(L/(n+'01.json'))['exit'],1)
  self.assertEqual(len(read(L/'control-results.json')['rows']),3)
  self.assertEqual(read(L/'ablation01.json')['exit'],1);self.assertEqual(read(L/'ablation02.json')['exit'],0)
  self.assertEqual(sha(L/'ablation02.v.snapshot.txt'),read(L/'ablation-plan02.json')['sha256'])
  a=read(L/'ablation-result.json')
  for k in ['passed','single_factor_remove_kassignr','same_returned_value','same_old_psp','same_entry_memory','same_remaining_continuation','real_semantics_both_cases','psp_returned_vs_old_decision_differs','frame77_preserved_both','assignment_anchor_credit']:self.assertTrue(a[k],k)
  for k in ['seven_argument_ablation_credit','prefix_credit','Hook_credit','TCB_body_credit']:self.assertFalse(a[k],k)
 def test_build_trust_and_adversarial_review(self):
  b=read(L/'build.json');self.assertEqual((b['exit'],b['active_sources'],b['old_products_reused']),(0,230,1140));self.assertFalse(b['source_only_cold_build'])
  t=read(L/'trust.json');self.assertTrue(t['passed']);self.assertTrue(t['assumptions_allowed']);self.assertEqual(t['roots_printed'],len(t['roots']));self.assertEqual(t['roots_printed'],60);self.assertEqual([c['exit'] for c in t['commands']],[0,0]);self.assertIn('V293TaskCreateTCBEntry.V293_OSTaskCreateExt_to_TCB_under_stack_return',t['roots'])
  rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),15)
  for r in rows:self.assertTrue(r['resolution']);self.assertIn(r['kind'],['test','bounded claim','limitation'])
