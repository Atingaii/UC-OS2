"""Between-Hooks table write, explicit open HookReturn contract, no kernel credit."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage63-tcb-priority-hook'
P='certiucos/v293/proofs/V293TCBPriorityHook.v';B='audit/probes/V293TCBPriorityHookProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TCBPriorityHookTests(unittest.TestCase):
 def test_preserved_inputs_products_and_append(self):
  b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
  self.assertEqual((len(b['files']),len(b['sources']),len(b['products'])),(14559,222,1110))
  for p,h in b['files'].items():
   if p not in allowed:self.assertEqual(sha(R/p),h,p)
  for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
  active=[s for s in (R/'_CoqProject').read_text().splitlines() if s.endswith('.v')]
  self.assertEqual(active[:223],b['sources']+[P])
 def test_actual_body_and_explicit_open_contract(self):
  x=read(L/'source-connection.json');self.assertTrue(x['passed']);self.assertTrue(x['all94_identities_equal'])
  self.assertEqual(x['source_identity'],read(R/'audit/repaired-source-inventory.json')['source_identity_sha256'])
  self.assertIn('OSTCBPrioTbl[prio] = ptcb;',x['between_hooks_source'])
  for h in x['hook_declarations']:self.assertEqual(h['declarations'],1);self.assertFalse(h['defined'])
  s=(R/P).read_text();seam=s.split('Theorem V293_OS_TCBInit_priority_to_second_hook :')[1].split('Proof.')[0].split(' exists Mf')[0]
  self.assertNotIn('V293_local_steps',seam);self.assertNotIn('loststep',seam)
  conditional=s.split('Theorem V293_OS_TCBInit_call_to_second_hook_under_contract :')[1].split('Proof.')[0]
  for t in ['forall b1 b2 b3 b4 b5 b6 b7 b8 b9 Mh','exists Mr','V293_local_steps P','((ge,V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9,Mr)','V293_tcb_hook_cells']:self.assertIn(t,conditional)
  self.assertNotRegex(conditional,r'Mh\s*=\s*Mr|Mr\s*=\s*Mh')
  for t in ['HookReturn b1 b2 b3 b4 b5 b6 b7 b8 b9 Mi ND Initialized','V293_OS_TCBInit_call_to_first_hook','V293_rdy_assign','spcall_step','svfevalnil_step','V293_missing_hook_cannot_return']:self.assertIn(t,s)
  self.assertNotRegex(s,r'\b(Axiom|Admitted|admit|Parameter|Conjecture)\b')
  self.assertEqual(sha(R/P),sha(L/'proof11.v.snapshot.txt'));self.assertEqual(sha(R/B),sha(L/'probe04.v.snapshot.txt'))
 def test_independent_fixture_and_bounded_claims(self):
  s=(R/B).read_text();self.assertNotIn('Require Import CertiOS.audit.probes.',s)
  for t in ['PriorityLiteralEntry','PriorityConcreteExecution','PriorityOld','PriorityFrame','310%positive,0','310%positive,4','V293_tcb_init_read Owned 9%nat']:self.assertIn(t,s)
  p=read(L/'proof-report.json');self.assertEqual((p['independent_memory_cases'],p['IE_instantiated_cases'],p['typed_reads_per_case'],p['typed_read_instances']),(4,8,10,80))
  for k in ['priority_table_write_executed','second_Hook_argument_evaluated','entry_to_second_hook_conditional_only','first_hook_return_anchor_assumed','HookReturn_requires_real_local_steps','HookReturn_protects_exact_cells','neighbor_slots_preserved','ready_group_row_task_count_preserved','caller_frame_preserved','initial_IE_universal','interrupt_and_critical_stacks_preserved']:self.assertTrue(p[k],k)
  for k in ['anchor_reachability_in_fixture','HookReturn_obligation_discharged','HookReturn_requires_memory_equality','first_Hook_real_execution','second_Hook_real_execution','Hook_assumed_noop','success_return_executed','callee_objects_freed','caller_restored','publication_executed','seven_call_Mf_connected','full_OS_TCBInit','full_OSInit','local_Hoare','all_execution_safety','GOOD_OS','same_program_K1_K4','ucos3_started']:self.assertFalse(p[k],k)
  self.assertEqual(p['formal_six_gates'],[94,1,1,1,1,0])
 def test_separate_endpoint_controls_and_assignment_ablation(self):
  p=read(L/'control-plan.json');s=(L/'positive.v.snapshot.txt').read_text();proofs=lambda t:re.findall(r'Proof\.(.*?)Qed\.',t,re.S)
  self.assertTrue(p['frozen_before_execution']);self.assertEqual(sha(L/'positive.v.snapshot.txt'),p['positive_sha256']);self.assertEqual(sha(R/B),p['probe_sha256'])
  rows=read(L/'control-results.json');self.assertEqual(len(rows),4)
  for row in rows:self.assertTrue(row['expected_result_observed']);self.assertTrue(row['proofs_unchanged'])
  for n,v in p['variants'].items():
   t=(L/(n+'.v.snapshot.txt')).read_text();a=s.index('Theorem '+v['section']);b=s.index('Proof.',a)
   self.assertEqual(t,s[:a]+s[a:b].replace(v['old'],v['new'],1)+s[b:]);self.assertEqual(proofs(t),proofs(s));self.assertEqual(sha(L/(n+'.v.snapshot.txt')),v['sha256'])
  a=read(L/'ablation-result.json');self.assertTrue(a['passed']);self.assertFalse(a['downstream_credit']);self.assertFalse(a['source_Hook_execution'])
  for k in ['same_input_program_env_memory_parameters','same_endpoint_code_argument','other_seven_frame_loads_unchanged','IE_si_ci_unchanged','same_measurement_statements_all_versions','helper_result_strengthened_not_weakened']:self.assertTrue(a[k])
  for i in [1,2,3]:
   plan=read(L/('ablation-plan'+('' if i==1 else f'0{i}')+'.json'));self.assertTrue(plan['frozen_before_execution']);self.assertEqual(sha(L/f'ablation0{i}.v.snapshot.txt'),plan['sha256'])
  self.assertEqual([read(L/f'ablation0{i}.json')['exit'] for i in [1,2,3]],[1,1,0])
 def test_build_trust_and_review(self):
  b=read(L/'build.json');self.assertEqual((b['exit'],b['active_sources'],b['old_products_reused']),(0,223,1110));self.assertFalse(b['source_only_cold_build'])
  t=read(L/'trust.json');self.assertTrue(t['passed']);self.assertTrue(t['assumptions_allowed']);self.assertEqual(t['roots_printed'],len(t['roots']));self.assertEqual(t['roots_printed'],50);self.assertEqual([c['exit'] for c in t['commands']],[0,0])
  self.assertIn('V293TCBPriorityHook.V293_OS_TCBInit_call_to_second_hook_under_contract',t['roots'])
  rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),15)
  for r in rows:self.assertTrue(r['resolution']);self.assertIn(r['kind'],['test','bounded claim','limitation'])
