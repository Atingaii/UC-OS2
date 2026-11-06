"""真实创建返回/free/caller恢复；未兑现端口和分配义务不升级为整核成果。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage72-task-create-return'
P='certiucos/v293/proofs/V293TaskCreateReturn.v';B='audit/probes/V293TaskCreateReturnProbe.v';A='audit/probes/V293TaskCreateReturnAnchor.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TaskCreateReturnTests(unittest.TestCase):
 def test_preserves_existing_baseline(self):
  b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
  self.assertEqual((len(b['files']),len(b['sources']),len(b['products'])),(15824,234,1170))
  for p,h in b['files'].items():
   if p not in allowed:self.assertEqual(sha(R/p),h,p)
  for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
  self.assertEqual([s for s in (R/'_CoqProject').read_text().splitlines() if s.endswith('.v')][:235],b['sources']+[P])
 def test_actual_composition_and_source_layout(self):
  versions=read(L/'accepted-versions.json')
  for p in [P,B,A]:
   n=versions[p];self.assertEqual(sha(R/p),sha(L/(n+'.v.snapshot.txt')));self.assertEqual(read(L/(n+'.json'))['exit'],0)
   self.assertNotRegex((R/p).read_text(),r'\b(Axiom|Admitted|admit|Parameter|Conjecture)\b');self.assertNotIn('Require Import CertiOS.audit.probes.',(R/p).read_text())
  x=read(L/'source-connection.json');self.assertTrue(x['passed']);self.assertTrue(x['all94_identities_equal']);self.assertEqual(x['source_identity'],read(R/'audit/repaired-source-inventory.json')['source_identity_sha256']);self.assertEqual(x['return_expression'],'err');self.assertFalse(x['verified_frontend'])
  y=read(L/'source-layout.json');self.assertTrue(y['passed']);self.assertEqual((len(y['parameters']),len(y['locals']),y['objects'],y['bytes']),(9,3,12,38));self.assertFalse(y['allocation_proved']);self.assertFalse(y['ABI_proved'])
  for h in x['hook_declarations']:self.assertFalse(h['defined'])
  s=(R/P).read_text();sig=s.split('Theorem V293_OSTaskCreateExt_success_return_under_hooks :')[1].split(' exists Mbridge,')[0]
  self.assertEqual(sig.count('V293_tcb_creation_hook_return'),2);self.assertEqual(sig.count('V293_create_stack_return'),1)
  for n in ['V293_OSTaskCreateExt_success_dispatch_under_hooks','V293_sfree_construct_execution','sretv_step','sfreeend_step','V293_raw_cells_return_many','Writable','TCBRemoved','getaddr le=addresses']:self.assertIn(n,s)
 def test_literal_inhabitation_and_bounded_claims(self):
  s=(R/B).read_text()
  for n in ['CreateLiteralBodyEntry','CreateLiteralReturnEntry','CreateActualMissingStack','CreateConditionalExecution','CreateResultReads','CreateCallerBinding','CreateReleasedSize','load tp Mf a=Some v']:self.assertIn(n,s)
  versions=read(L/'accepted-versions.json');self.assertIn('= 31',(L/(versions[B]+'.log')).read_text())
  x=read(L/'proof-report.json')
  for k in ['body_entry_to_actual_return','creation_local_free','real_caller_restored','local_writable_derived_from_reached_ownership','same_returned_memory_preserves_live_cells','three_real_Hook_obligations','release9_preserved','caller_frame_preserved']:self.assertTrue(x[k],k)
  for k in ['real_Hook_implementations','scheduler_body_executed','creation_call_allocation','error_cleanup_execution','local_Hoare','all_execution_safety','GOOD_OS','same_program_K1_K4','ucos3_started']:self.assertFalse(x[k],k)
  self.assertEqual((x['creation_locals_freed_objects'],x['creation_locals_freed_bytes'],x['typed_reads_per_conditional_output']),(12,38,31));self.assertEqual(x['formal_six_gates'],[94,1,1,1,1,0])
 def test_prospective_controls_and_single_factor_return(self):
  p=read(L/'control-plan.json');s=(L/'positive01.v.snapshot.txt').read_text();proofs=lambda t:re.findall(r'Proof\.(.*?)Qed\.',t,re.S)
  self.assertTrue(p['frozen_before_compilation']);self.assertEqual(read(L/'positive01.json')['exit'],0);self.assertEqual(sha(L/'positive01.v.snapshot.txt'),p['positive_sha256'])
  for n,v in p['variants'].items():
   t=(L/(n+'01.v.snapshot.txt')).read_text();a=s.index('Theorem '+v['theorem']);b=s.index('Proof.',a)
   self.assertEqual(t,s[:a]+s[a:b].replace(v['old'],v['new'],1)+s[b:]);self.assertEqual(proofs(s),proofs(t));self.assertEqual(sha(L/(n+'01.v.snapshot.txt')),v['sha256']);self.assertEqual(read(L/(n+'01.json'))['exit'],1)
  self.assertTrue(read(L/'control-results.json')['passed']);a=read(L/'return-ablation-result.json');self.assertTrue(a['passed']);self.assertTrue(a['same_input_memory_env_value']);self.assertFalse(a['full_path_or_Hook_credit']);self.assertTrue(read(L/'return-ablation-plan.json')['frozen_before_compilation'])
 def test_build_trust_and_adversarial_review(self):
  x=read(L/'build.json');self.assertEqual((x['exit'],x['active_sources'],x['old_products_reused']),(0,235,1170));self.assertFalse(x['source_only_cold_build'])
  x=read(L/'trust.json');self.assertTrue(x['passed']);self.assertTrue(x['assumptions_allowed']);self.assertEqual(x['roots_printed'],len(x['roots']));self.assertEqual(x['roots_printed'],60);self.assertEqual([c['exit'] for c in x['commands']],[0,0])
  rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),15)
  for row in rows:self.assertTrue(row['resolution']);self.assertIn(row['kind'],['test','bounded claim','limitation'])
