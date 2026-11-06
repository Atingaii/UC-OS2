"""精确成功后缀接入口；保持真实调度边界和未兑现Hook，不虚报整核完成。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage71-task-create-suffix'
C='certiucos/v293/code/V293OSTaskCreateExtSuffix.v';P='certiucos/v293/proofs/V293TaskCreateSuffix.v';B='audit/probes/V293TaskCreateSuffixProbe.v';D='audit/probes/V293TaskCreateDispatchProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TaskCreateSuffixTests(unittest.TestCase):
 def test_preserves_existing_baseline(self):
  b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
  self.assertEqual((len(b['files']),len(b['sources']),len(b['products'])),(15701,232,1160))
  for p,h in b['files'].items():
   if p not in allowed:self.assertEqual(sha(R/p),h,p)
  for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
  self.assertEqual([s for s in (R/'_CoqProject').read_text().splitlines() if s.endswith('.v')][:234],b['sources']+[C,P])
 def test_source_identity_and_actual_composition(self):
  for p,n in [(C,'code02'),(P,'proof03'),(B,'probe01'),(D,'dispatch02')]:
   self.assertEqual(sha(R/p),sha(L/(n+'.v.snapshot.txt')));self.assertEqual(read(L/(n+'.json'))['exit'],0)
   self.assertNotRegex((R/p).read_text(),r'\b(Axiom|Admitted|admit|Parameter|Conjecture)\b')
   self.assertNotIn('Require Import CertiOS.audit.probes.',(R/p).read_text())
  x=read(L/'source-connection.json');self.assertTrue(x['passed']);self.assertTrue(x['all94_identities_equal']);self.assertEqual(x['source_identity'],read(R/'audit/repaired-source-inventory.json')['source_identity_sha256'])
  self.assertEqual(x['rollback_order'],['enter','priority_slot=NULL','exit']);self.assertEqual(x['return_expression'],'err');self.assertFalse(x['verified_frontend']);self.assertTrue(x['error_branch_syntax_only'])
  for h in x['hook_declarations']:self.assertFalse(h['defined'])
  s=(R/P).read_text();sig=s.split('Theorem V293_OSTaskCreateExt_success_dispatch_under_hooks :')[1].split(' exists Mbridge,')[0]
  self.assertEqual(sig.count('V293_tcb_creation_hook_return'),2);self.assertEqual(sig.count('V293_create_stack_return'),1)
  for n in ['V293_OSTaskCreateExt_result_assigned_under_hooks','V293_OSTaskCreateExt_success_suffix','exact Final','split;assumption','fresh Mbridge b','get Mf (b,Z.of_nat k)=None']:self.assertIn(n,s)
 def test_literal_inhabitation_and_bounded_claims(self):
  s=(R/B).read_text()
  for n in ['CreateLiteralBodyEntry','CreateLiteralReturnEntry','CreateActualMissingStack','CreateConditionalExecution','CreateResultReads','load tp Mf a=Some v']:self.assertIn(n,s)
  self.assertIn('= 43',(L/'probe01.log').read_text());x=read(L/'proof-report.json')
  for k in ['body_entry_to_exact_success_suffix','running0_return_value_evaluated','running1_actual_sfexec','same_Mf_unchanged_by_success_suffix','three_real_Hook_obligations','release9_preserved','caller_frame_preserved','readback_shares_production_result_formula']:self.assertTrue(x[k],k)
  for k in ['real_Hook_implementations','scheduler_body_executed','creation_local_free','creation_call_allocation','error_cleanup_execution','local_Hoare','all_execution_safety','GOOD_OS','same_program_K1_K4','ucos3_started']:self.assertFalse(x[k],k)
  self.assertEqual(x['typed_reads_per_conditional_output'],43);self.assertEqual(x['formal_six_gates'],[94,1,1,1,1,0])
 def test_prospective_controls_and_single_factor_dispatch(self):
  p=read(L/'control-plan.json');s=(L/'positive01.v.snapshot.txt').read_text();proofs=lambda t:re.findall(r'Proof\.(.*?)Qed\.',t,re.S)
  self.assertTrue(p['frozen_before_compilation']);self.assertEqual(read(L/'positive01.json')['exit'],0);self.assertEqual(sha(L/'positive01.v.snapshot.txt'),p['positive_sha256'])
  for n,v in p['variants'].items():
   t=(L/(n+'01.v.snapshot.txt')).read_text();a=s.index('Theorem '+v['theorem']);b=s.index('Proof.',a)
   self.assertEqual(t,s[:a]+s[a:b].replace(v['old'],v['new'],1)+s[b:]);self.assertEqual(proofs(s),proofs(t));self.assertEqual(sha(L/(n+'01.v.snapshot.txt')),v['sha256']);self.assertEqual(read(L/(n+'01.json'))['exit'],1)
  self.assertTrue(read(L/'control-results.json')['passed']);a=read(L/'dispatch-ablation-result.json');self.assertTrue(a['passed']);self.assertTrue(a['same_all_other_addresses']);self.assertFalse(a['full_path_or_Hook_credit'])
  self.assertEqual(sha(L/'dispatch02.v.snapshot.txt'),read(L/'dispatch-ablation-plan02.json')['sha256'])
 def test_build_trust_and_adversarial_review(self):
  x=read(L/'build.json');self.assertEqual((x['exit'],x['active_sources'],x['old_products_reused']),(0,234,1160));self.assertFalse(x['source_only_cold_build'])
  x=read(L/'trust.json');self.assertTrue(x['passed']);self.assertTrue(x['assumptions_allowed']);self.assertEqual(x['roots_printed'],len(x['roots']));self.assertEqual(x['roots_printed'],60);self.assertEqual([c['exit'] for c in x['commands']],[0,0])
  rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),15)
  for row in rows:self.assertTrue(row['resolution']);self.assertIn(row['kind'],['test','bounded claim','limitation'])
