"""Actual post-Hook publication/return/free, not a reachable whole-function claim."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage64-tcb-success-return'
P='certiucos/v293/proofs/V293TCBSuccessReturn.v';B='audit/probes/V293TCBSuccessReturnProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TCBSuccessReturnTests(unittest.TestCase):
 def test_preserved_inputs_and_products(self):
  b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
  self.assertEqual((len(b['files']),len(b['sources']),len(b['products'])),(14696,223,1115))
  for p,h in b['files'].items():
   if p not in allowed:self.assertEqual(sha(R/p),h,p)
  for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
  self.assertEqual([s for s in (R/'_CoqProject').read_text().splitlines() if s.endswith('.v')][:224],b['sources']+[P])
 def test_actual_suffix_and_explicit_boundary(self):
  source=read(L/'source-connection.json');self.assertTrue(source['passed']);self.assertTrue(source['all94_identities_equal'])
  self.assertEqual(source['source_identity'],read(R/'audit/repaired-source-inventory.json')['source_identity_sha256'])
  for h in source['hook_declarations']:self.assertEqual(h['declarations'],1);self.assertFalse(h['defined'])
  s=(R/P).read_text();statement=s.split('Theorem V293_OS_TCBInit_success_suffix_return :')[1].split('Proof.')[0]
  self.assertNotIn('V293_local_steps',statement.split(' exists Ms Mf,')[0])
  for t in ['NoDup blocks','~In (fst a) blocks','V293_tcb_second_hook_cont','V293_OS_TCBInit_publication_execution','V293_error_return_execution','V293_raw_cells_return_many','V293_tcb_function_layout','V293_tick_raw_owned_writable']:self.assertIn(t,s)
  self.assertNotRegex(s,r'\b(Axiom|Admitted|admit|Parameter|Conjecture)\b')
  self.assertEqual(sha(R/P),sha(L/'proof11.v.snapshot.txt'));self.assertEqual(sha(R/B),sha(L/'probe05.v.snapshot.txt'))
 def test_independent_fixture_and_bounded_claims(self):
  s=(R/B).read_text();self.assertNotIn('Require Import CertiOS.audit.probes.',s)
  for t in ['SuccessLiteralEntry','SuccessConcreteExecution','SuccessExpected','SuccessFrame','get Mf(b,Z.of_nat k)=None','(310%positive,4*Z.of_nat p)','(601%positive,0)','(602%positive,0)']:self.assertIn(t,s)
  p=read(L/'proof-report.json');self.assertEqual((p['independent_memory_cases'],p['IE_instantiated_cases'],p['typed_read_instances'],p['freed_byte_instances']),(4,8,108,232))
  self.assertEqual((p['callee_objects_freed'],p['callee_bytes_freed']),(9,29))
  for k in ['publication_executed','success_return_executed','caller_restored','same_Mf_ownership','initial_IE_universal','interrupt_and_critical_stacks_preserved','explicit_NoDup_and_block_Away_required','Hook_return_anchor_assumed']:self.assertTrue(p[k],k)
  for k in ['Hook_return_anchor_reachability','real_Hook_execution','Hook_assumed_noop','automatic_callee_freshness','whole_allocation_reachability','full_OS_TCBInit','seven_call_Mf_connected','full_OSInit','local_Hoare','all_execution_safety','GOOD_OS','same_program_K1_K4','ucos3_started']:self.assertFalse(p[k],k)
  self.assertEqual(p['formal_six_gates'],[94,1,1,1,1,0])
 def test_controls_and_separate_permission_ablation(self):
  p=read(L/'control-plan02.json');s=(L/'positive02.v.snapshot.txt').read_text();proofs=lambda t:re.findall(r'Proof\.(.*?)Qed\.',t,re.S)
  self.assertTrue(p['frozen_before_execution']);self.assertEqual(sha(L/'positive02.v.snapshot.txt'),p['positive_sha256'])
  rows=read(L/'control-results02.json');self.assertEqual(len(rows),5)
  for row in rows:self.assertTrue(row['expected_result_observed']);self.assertTrue(row['proofs_unchanged'])
  for n,v in p['variants'].items():
   t=(L/(n+'02.v.snapshot.txt')).read_text();a=s.index('Theorem '+v['section']);b=s.index('Proof.',a)
   self.assertEqual(t,s[:a]+s[a:b].replace(v['old'],v['new'],1)+s[b:]);self.assertEqual(proofs(t),proofs(s));self.assertEqual(sha(L/(n+'02.v.snapshot.txt')),v['sha256'])
  original=read(L/'control-results.json');self.assertEqual(original[0]['exit'],1)
  for i in range(1,8):
   plan=read(L/('permission-plan'+('' if i==1 else f'0{i}')+'.json'));self.assertTrue(plan['frozen_before_execution']);self.assertFalse(plan['downstream_credit']);self.assertEqual(sha(L/f'permission0{i}.v.snapshot.txt'),plan['sha256'])
  self.assertEqual([read(L/f'permission0{i}.json')['exit'] for i in range(1,8)],[1,1,1,1,1,1,0])
  a=read(L/'permission-result.json');self.assertTrue(a['passed']);self.assertFalse(a['publication_ablation_executed']);self.assertFalse(a['full_return_ablation_executed']);self.assertFalse(a['original_protocol_proposal_executed'])
 def test_build_trust_and_review(self):
  b=read(L/'build.json');self.assertEqual((b['exit'],b['active_sources'],b['old_products_reused']),(0,224,1115));self.assertFalse(b['source_only_cold_build'])
  t=read(L/'trust.json');self.assertTrue(t['passed']);self.assertTrue(t['assumptions_allowed']);self.assertEqual(t['roots_printed'],len(t['roots']));self.assertEqual(t['roots_printed'],48);self.assertEqual([c['exit'] for c in t['commands']],[0,0])
  self.assertIn('V293TCBSuccessReturn.V293_OS_TCBInit_success_suffix_return',t['roots'])
  rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),15)
  for r in rows:self.assertTrue(r['resolution']);self.assertIn(r['kind'],['test','bounded claim','limitation'])
