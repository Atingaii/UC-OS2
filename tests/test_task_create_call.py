"""调用真实分配接入既有返回证明；不升级开放的Hook/整核义务。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage73-task-create-call'
C='certiucos/v293/code/V293OSTaskCreateExtFunction.v';P='certiucos/v293/proofs/V293TaskCreateCall.v';B='audit/probes/V293TaskCreateCallProbe.v';A='audit/probes/V293TaskCreateCallAnchor.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TaskCreateCallTests(unittest.TestCase):
 def test_preserves_baseline_and_exact_function_connection(self):
  b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
  self.assertEqual((len(b['files']),len(b['sources']),len(b['products'])),(15987,235,1175))
  for p,h in b['files'].items():
   if p not in allowed:self.assertEqual(sha(R/p),h,p)
  for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
  self.assertEqual([s for s in (R/'_CoqProject').read_text().splitlines() if s.endswith('.v')],b['sources']+[C,P])
  x=read(L/'function-connection.json');self.assertTrue(x['passed']);self.assertTrue(x['actual_semantic_allocation']);self.assertFalse(x['ABI_proved']);self.assertTrue(x['three_Hook_contracts_open'])
  self.assertEqual([p['name'] for p in x['source_parameters']],['task','p_arg','ptos','prio','id','pbos','stk_size','pext','opt'])
  self.assertEqual([p['name'] for p in x['source_locals']],['psp','err','cpu_sr'])
  d=read(L/'declaration-connection.json');self.assertTrue(d['passed']);self.assertTrue(d['reversed_argument_types_checked']);self.assertEqual(len(d['rows']),12);self.assertEqual(d['code_sha256'],sha(R/C))
  x=read(L/'source-connection.json');self.assertTrue(x['passed']);self.assertTrue(x['all94_identities_equal'])
  self.assertEqual(x['source_identity'],read(R/'audit/repaired-source-inventory.json')['source_identity_sha256'])
  self.assertTrue(all(not h['defined'] for h in x['hook_declarations']))
 def test_actual_allocation_composition_and_literal_freshness(self):
  versions=read(L/'accepted-versions.json')
  for p in [C,P,B,A]:
   n=versions[p];self.assertEqual(sha(R/p),sha(L/(n+'.v.snapshot.txt')));self.assertEqual(read(L/(n+'.json'))['exit'],0)
   self.assertNotRegex((R/p).read_text(),r'\b(Axiom|Admitted|admit|Parameter|Conjecture)\b');self.assertNotIn('Require Import CertiOS.audit.probes.',(R/p).read_text())
  s=(R/P).read_text();self.assertEqual(s.count('eapply sallocp_step;'),9);self.assertEqual(s.count('eapply salloclv_step;'),3)
  for n in ['V293_create_function_layout','V293_create_call_prologue','V293_OSTaskCreateExt_success_return_under_hooks','V293_OSTaskCreateExt_success_call_under_hooks','V293_local_trans','sallocend_step']:self.assertIn(n,s)
  for n in ['CallLiteralEntry','CallBlocksDistinct','CallBlocksFresh','CallMemoryOutside','CallConditionalExecution','CreateResultReads']:self.assertIn(n,(R/B).read_text())
  self.assertIn('= 31',(L/(versions[B]+'.log')).read_text())
  x=read(L/'proof-report.json')
  for k in ['creation_call_allocation','same_actual_memory_composed','creation_local_free','caller_restored','three_real_Hook_obligations','fresh_block_choices_explicit','survivor_separation_explicit']:self.assertTrue(x[k],k)
  for k in ['caller_argument_expressions_evaluated','real_Hook_implementations','all_execution_safety','local_Hoare','GOOD_OS','same_program_K1_K4','ucos3_started']:self.assertFalse(x[k],k)
  self.assertEqual((x['creation_objects'],x['creation_bytes'],x['typed_reads_per_conditional_output']),(12,38,31))
 def test_prospective_endpoint_controls_and_call_type_ablation(self):
  p=read(L/'control-plan02.json');s=(L/'positive02.v.snapshot.txt').read_text();proofs=lambda t:re.findall(r'Proof\.(.*?)Qed\.',t,re.S)
  self.assertTrue(p['frozen_before_compilation']);self.assertEqual(read(L/'positive02.json')['exit'],0);self.assertEqual(sha(L/'positive02.v.snapshot.txt'),p['positive_sha256'])
  for n,v in p['variants'].items():
   t=(L/(n+'02.v.snapshot.txt')).read_text();a=s.index('Theorem '+v['theorem']);b=s.index('Proof.',a)
   self.assertEqual(t,s[:a]+s[a:b].replace(v['old'],v['new'],1)+s[b:]);self.assertEqual(proofs(s),proofs(t));self.assertEqual(sha(L/(n+'02.v.snapshot.txt')),v['sha256']);self.assertEqual(read(L/(n+'02.json'))['exit'],1)
  x=read(L/'control-results.json');self.assertTrue(x['passed']);self.assertEqual(len(x['rows']),3)
  x=read(L/'call-ablation-result.json');self.assertTrue(x['passed']);self.assertTrue(x['same_input_memory_env_types_other_eight_arguments']);self.assertFalse(x['downstream_allocation_body_or_Hook_credit'])
  self.assertIn('Only argument opt value',read(L/'protocol.json')['ablation']['factor'])
 def test_build_trust_and_bounded_adversarial_review(self):
  x=read(L/'build.json');self.assertEqual((x['exit'],x['active_sources'],x['old_products_reused']),(0,237,1175));self.assertFalse(x['source_only_cold_build'])
  x=read(L/'trust.json');self.assertTrue(x['passed']);self.assertTrue(x['assumptions_allowed']);self.assertEqual(x['roots_printed'],len(x['roots']));self.assertEqual(x['roots_printed'],58);self.assertEqual([c['exit'] for c in x['commands']],[0,0])
  rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),15)
  for row in rows:self.assertTrue(row['resolution']);self.assertIn(row['kind'],['test','bounded claim','limitation'])
  self.assertEqual(read(L/'proof-report.json')['formal_six_gates'],[94,1,1,1,1,0])
