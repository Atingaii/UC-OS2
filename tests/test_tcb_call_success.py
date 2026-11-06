"""Conditional full-call connection; explicitly not fixed-program success."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage65-tcb-call-success'
P='certiucos/v293/proofs/V293TCBCallSuccess.v';B='audit/probes/V293TCBCallSuccessProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TCBCallSuccessTests(unittest.TestCase):
 def test_preserved_baseline(self):
  b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
  self.assertEqual((len(b['files']),len(b['sources']),len(b['products'])),(14873,224,1120))
  for p,h in b['files'].items():
   if p not in allowed:self.assertEqual(sha(R/p),h,p)
  for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
  self.assertEqual([p for p in (R/'_CoqProject').read_text().splitlines() if p.endswith('.v')][:225],b['sources']+[P])
 def test_contiguous_call_and_real_obligations(self):
  s=(R/P).read_text();statement=s.split('Theorem V293_OS_TCBInit_success_call_under_hooks :')[1].split('Proof.')[0]
  self.assertEqual(statement.count('V293_tcb_creation_hook_return'),2)
  self.assertNotIn('V293_local_steps',statement.split(' exists b1 b2 b3 b4 b5 b6 b7 b8 b9 Mf,')[0])
  for token in ['HalfPermMap.bounded M','V293_cells_upper cells','V293_tcb_fresh_nine_avoiding M result','Hook1 b1','Hook2 b1','exact Prefix','exact FirstExec','exact PriorityExec','exact SecondExec','exact Suffix','V293_tcb_creation_fields','V293_raw_cells_append']:
   self.assertIn(token,s)
  self.assertNotRegex(s,r'\b(Axiom|Admitted|admit|Parameter|Conjecture)\b')
  self.assertEqual(sha(R/P),sha(L/'proof07.v.snapshot.txt'))
  source=read(L/'source-connection.json');self.assertTrue(source['passed']);self.assertTrue(source['all94_identities_equal'])
  self.assertEqual(source['source_identity'],read(R/'audit/repaired-source-inventory.json')['source_identity_sha256'])
  self.assertEqual(len(source['hook_declarations']),5)
  for h in source['hook_declarations']:self.assertEqual(h['declarations'],1);self.assertFalse(h['defined'])
 def test_literal_inputs_conditional_outputs_and_stuck(self):
  s=(R/B).read_text();self.assertNotIn('Require Import CertiOS.audit.probes.',s)
  for token in ['SuccessLiteralEntry','SuccessConditionalExecution','SuccessActualFirstHookStuck','SuccessHook P p present enabled si ci false','SuccessHook P p present enabled si ci true','SuccessFixedMissing','SuccessFields','SuccessExpected','get Mf(b,Z.of_nat k)=None']:
   self.assertIn(token,s)
  self.assertNotRegex(s,r'\b(Axiom|Admitted|admit|Parameter|Conjecture)\b')
  p=read(L/'proof-report.json')
  self.assertEqual((p['unconditional_literal_entries'],p['conditional_output_cases'],p['actual_successful_fixture_runs']),(4,4,0))
  self.assertEqual(p['conditional_typed_reads_by_head_present'],{'false':31,'true':32})
  for k in ['automatic_callee_freshness','automatic_survivor_block_avoidance','unconditional_first_Hook_stuck_witness','publication_and_return_memories_contiguous','same_Mf_ownership','conditional_full_call']:self.assertTrue(p[k],k)
  for k in ['contracts_discharged','real_Hook_implementation','Hook_assumed_noop','unconditional_success','local_Hoare','all_execution_safety','GOOD_OS','same_program_K1_K4','ucos3_started']:self.assertFalse(p[k],k)
  self.assertEqual(p['formal_six_gates'],[94,1,1,1,1,0])
 def test_controls_and_lookup_only_ablation(self):
  p=read(L/'control-plan03.json');s=(L/'positive02.v.snapshot.txt').read_text();proofs=lambda x:re.findall(r'Proof\.(.*?)Qed\.',x,re.S)
  self.assertTrue(p['frozen_before_execution']);self.assertTrue(p['conditional']);self.assertFalse(p['Hook_hypotheses_discharged'])
  self.assertEqual(sha(L/'positive02.v.snapshot.txt'),p['positive_sha256']);self.assertEqual(sha(R/B),p['probe_sha256'])
  self.assertEqual(read(L/'positive.json')['exit'],1);self.assertFalse(read(L/'original-control-result.json')['negative_control_credit'])
  rows=read(L/'control-results.json');self.assertEqual(len(rows),5)
  for r in rows:self.assertTrue(r['expected_result_observed']);self.assertTrue(r['proofs_unchanged'])
  for n,v in p['variants'].items():
   t=(L/(n+'02.v.snapshot.txt')).read_text();a=s.index('Theorem '+v['section']);b=s.index('Proof.',a)
   self.assertEqual(t,s[:a]+s[a:b].replace(v['old'],v['new'],1)+s[b:]);self.assertEqual(proofs(s),proofs(t));self.assertEqual(sha(L/(n+'02.v.snapshot.txt')),v['sha256'])
  plan=read(L/'ablation-plan02.json');self.assertTrue(plan['frozen_before_execution']);self.assertEqual(sha(L/'ablation01.v.snapshot.txt'),plan['sha256'])
  a=read(L/'ablation-result.json');self.assertTrue(a['passed']);self.assertTrue(a['only_P502_lookup_changed'])
  for k in ['sentinel_body_executed','anchor_reachability_proved','downstream_credit','source_Hook_implementation']:self.assertFalse(a[k],k)
 def test_build_trust_and_review(self):
  b=read(L/'build.json');self.assertEqual((b['exit'],b['active_sources'],b['old_products_reused']),(0,225,1120));self.assertFalse(b['source_only_cold_build'])
  t=read(L/'trust.json');self.assertTrue(t['passed']);self.assertTrue(t['assumptions_allowed']);self.assertEqual(t['roots_printed'],len(t['roots']));self.assertEqual(t['roots_printed'],52)
  self.assertEqual([c['exit'] for c in t['commands']],[0,0]);self.assertIn('V293TCBCallSuccess.V293_OS_TCBInit_success_call_under_hooks',t['roots'])
  rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),15)
  for r in rows:self.assertTrue(r['resolution']);self.assertIn(r['kind'],['test','bounded claim','limitation'])
