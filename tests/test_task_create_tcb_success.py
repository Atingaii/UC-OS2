"""任务创建到TCB成功返回的条件连接，不把三项真实Hook义务当实现。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage69-task-create-tcb-return'
P='certiucos/v293/proofs/V293TaskCreateTCBSuccess.v';B='audit/probes/V293TaskCreateTCBSuccessProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TaskCreateTCBSuccessTests(unittest.TestCase):
 def test_baseline_preserved(self):
  b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
  self.assertEqual((len(b['files']),len(b['sources']),len(b['products'])),(15436,230,1150))
  for p,h in b['files'].items():
   if p not in allowed:self.assertEqual(sha(R/p),h,p)
  for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
  self.assertEqual([p for p in (R/'_CoqProject').read_text().splitlines() if p.endswith('.v')][:231],b['sources']+[P])
 def test_source_and_stable_composition(self):
  for p,n in [(P,'proof06'),(B,'probe02')]:
   self.assertEqual(sha(R/p),sha(L/(n+'.v.snapshot.txt')));self.assertEqual(read(L/(n+'.json'))['exit'],0)
   self.assertNotRegex((R/p).read_text(),r'\b(Axiom|Admitted|admit|Parameter|Conjecture)\b')
   self.assertNotIn('Require Import CertiOS.audit.probes.',(R/p).read_text())
  s=read(L/'source-connection.json');self.assertTrue(s['passed']);self.assertTrue(s['all94_identities_equal']);self.assertEqual(s['source_identity'],read(R/'audit/repaired-source-inventory.json')['source_identity_sha256'])
  self.assertEqual(s['AST_seven_argument_names'],['prio','psp','pbos','id','stk_size','pext','opt']);self.assertTrue(s['TCB_body_executed_under_real_hooks'])
  for h in s['hook_declarations']:self.assertFalse(h['defined'])
  src=(R/P).read_text();sig=src.split('Theorem V293_OSTaskCreateExt_to_TCB_success_under_hooks :')[1].split(' exists Mbridge,')[0]
  self.assertEqual(sig.count('V293_tcb_creation_hook_return'),2);self.assertEqual(sig.count('V293_create_stack_return'),1)
  for forbidden in ['evalval','evaltype','cstepstar','V293_local_steps']:self.assertNotIn(forbidden,sig)
  for n in ['Mbridge&Prefix&AtTCB','V293_OS_TCBInit_success_call_under_hooks','fresh Mbridge b','get Mf (b,Z.of_nat k)=None','split;[exact Prefix | ]','V293_create_caller_cells']:self.assertIn(n,src)
 def test_inhabitation_readback_and_claim_bounds(self):
  src=(R/B).read_text()
  for n in ['CreateLiteralBodyEntry','CreateLiteralReturnEntry','CreateConditionalExecution','CreateActualMissingStack','CreateResultValid','CreateResultReads','load tp Mf a=Some v']:self.assertIn(n,src)
  self.assertIn('= 42', (L/'probe02.log').read_text())
  x=read(L/'proof-report.json');self.assertEqual((x['conditional_full_path_instances'],x['typed_reads_per_conditional_output'],x['TCB_locals_freed_objects'],x['TCB_locals_freed_bytes']),(1,42,9,29))
  for k in ['body_entry_to_TCB_return0_conditional','three_real_Hook_obligations','same_Mbridge_actually_reached','fresh_nine_relative_to_Mbridge','priority_slot_owned_once','actual_reached_missing_stack_hook','err_unchanged9_until_pending_assignment']:self.assertTrue(x[k],k)
  for k in ['err_assignment_in_main','real_Hook_implementations','whole_memory_identity_required','caller_allocation','creation_suffix','seven_OSInit_actual_memories_linked','verified_frontend','local_Hoare','all_execution_safety','GOOD_OS','same_program_K1_K4','ucos3_started']:self.assertFalse(x[k],k)
  self.assertEqual(x['formal_six_gates'],[94,1,1,1,1,0])
 def test_controls_and_prospective_single_factor_ablation(self):
  p=read(L/'control-plan.json');s=(L/'positive01.v.snapshot.txt').read_text();proofs=lambda t:re.findall(r'Proof\.(.*?)Qed\.',t,re.S)
  self.assertTrue(p['frozen_before_compilation']);self.assertEqual(sha(L/'positive01.v.snapshot.txt'),p['positive_sha256']);self.assertEqual(read(L/'positive01.json')['exit'],0)
  for n,v in p['variants'].items():
   t=(L/(n+'01.v.snapshot.txt')).read_text();a=s.index('Theorem '+v['theorem']);b=s.index('Proof.',a)
   self.assertEqual(t,s[:a]+s[a:b].replace(v['old'],v['new'],1)+s[b:]);self.assertEqual(proofs(t),proofs(s));self.assertEqual(sha(L/(n+'01.v.snapshot.txt')),v['sha256']);self.assertEqual(read(L/(n+'01.json'))['exit'],1)
  self.assertTrue(read(L/'control-results.json')['passed']);a=read(L/'ablation-result.json');self.assertTrue(a['passed']);self.assertTrue(a['return_anchor_only']);self.assertFalse(a['full_path_or_Hook_credit'])
  self.assertEqual(sha(L/'ablation01.v.snapshot.txt'),read(L/'ablation-plan.json')['sha256']);self.assertEqual(read(L/'ablation01.json')['exit'],0)
 def test_build_trust_and_adversarial_review(self):
  x=read(L/'build.json');self.assertEqual((x['exit'],x['active_sources'],x['old_products_reused']),(0,231,1150));self.assertFalse(x['source_only_cold_build'])
  x=read(L/'trust.json');self.assertTrue(x['passed']);self.assertTrue(x['assumptions_allowed']);self.assertEqual(x['roots_printed'],len(x['roots']));self.assertEqual(x['roots_printed'],58);self.assertEqual([c['exit'] for c in x['commands']],[0,0])
  self.assertIn('V293TaskCreateTCBSuccess.V293_OSTaskCreateExt_to_TCB_success_under_hooks',x['roots'])
  rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),18)
  for row in rows:self.assertTrue(row['resolution']);self.assertIn(row['kind'],['test','bounded claim','limitation'])
