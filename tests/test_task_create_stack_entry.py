"""Body-entry to real argument evaluation; deliberately no Hook-body credit."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage67-task-create-stack-entry'
P='certiucos/v293/proofs/V293TaskCreateStackEntry.v';B='audit/probes/V293TaskCreateStackEntryProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TaskCreateStackEntryTests(unittest.TestCase):
 def test_preserved_baseline(self):
  b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
  self.assertEqual((len(b['files']),len(b['sources']),len(b['products'])),(15190,227,1135))
  for p,h in b['files'].items():
   if p not in allowed:self.assertEqual(sha(R/p),h,p)
  for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
  self.assertEqual([p for p in (R/'_CoqProject').read_text().splitlines() if p.endswith('.v')][:228],b['sources']+[P])
 def test_source_and_public_interface(self):
  for p,n in [(P,'proof01'),(B,'probe02')]:
   self.assertEqual(sha(R/p),sha(L/(n+'.v.snapshot.txt')));self.assertEqual(read(L/(n+'.json'))['exit'],0)
   self.assertNotRegex((R/p).read_text(),r'\b(Axiom|Admitted|admit|Parameter|Conjecture)\b')
   self.assertNotIn('Require Import CertiOS.audit.probes.',(R/p).read_text())
  s=read(L/'source-connection.json');self.assertTrue(s['passed']);self.assertTrue(s['all94_identities_equal'])
  self.assertEqual(s['source_identity'],read(R/'audit/repaired-source-inventory.json')['source_identity_sha256'])
  self.assertEqual(s['AST_four_argument_names'],['task','p_arg','ptos','opt'])
  self.assertEqual(s['AST_four_argument_types'],['void (*)(void *)','void *','OS_STK *','INT16U'])
  self.assertTrue(s['AST_arguments_are_pure_variable_reads']);self.assertFalse(s['task_to_pc_identity_map_proved']);self.assertFalse(s['function_pointer_ABI_equivalence'])
  self.assertEqual(len(s['hook_declarations']),5)
  for h in s['hook_declarations']:self.assertFalse(h['defined'])
  src=(R/P).read_text();premises=src.split('Theorem V293_OSTaskCreateExt_to_stack_hook :')[1].split(' exists Mf,')[0]
  for forbidden in ['evalval','evaltype','V293_local_steps','cstepstar','hook_return']:self.assertNotIn(forbidden,premises)
  for t in ['0<=target<=Int.max_unsigned','V293_stack_argument_env','V293_stack_argument_valid']:self.assertIn(t,premises)
  for t in ['V293_tcb_init_read Final 4%nat','V293_tcb_init_read Final 7%nat','V293_stack_four_argument_execution','apply V293_missing_port_has_no_step']:self.assertIn(t,src)
 def test_literal_entries_and_boundaries(self):
  src=(R/B).read_text()
  for t in ['StackLiteralEntry','StackActualHookEntry','StackActualMissingPort','p=0%nat \/ p=12%nat','target=700 \/ target=701','StackExpected p target','load tp Mf a=Some v']:self.assertIn(t,src)
  p=read(L/'proof-report.json');self.assertEqual((p['unconditional_literal_entries'],p['typed_reads_per_entry']),(4,12))
  for k in ['body_entry','unconditional_normalized_prefix','argument_evaluation','actual_four_variable_reads','Hook_sfexec','IE_universally_quantified','si_ci_preserved','same_Mf_ownership','actual_reached_missing_port_no_step','selector_range_required','selector_exact_recovery','selector_injective_in_range']:self.assertTrue(p[k],k)
  for k in ['function_call_allocation','Hook_lookup','Hook_body_executed','task_to_pc_identity_map_proved','function_pointer_ABI_equivalence','real_Hook_implementation','Hook_assumed_noop','whole_OSTaskCreateExt','stage65_TCB_call_linked','seven_call_actual_memories_linked','local_Hoare','all_execution_safety','GOOD_OS','same_program_K1_K4','ucos3_started']:self.assertFalse(p[k],k)
  self.assertEqual(p['formal_six_gates'],[94,1,1,1,1,0])
  self.assertTrue((R/'docs/adr/0007-任务入口复用框架函数标识符.md').is_file())
 def test_controls_and_representation_decision(self):
  p=read(L/'control-plan.json');s=(L/'positive01.v.snapshot.txt').read_text();proofs=lambda x:re.findall(r'Proof\.(.*?)Qed\.',x,re.S)
  self.assertTrue(p['frozen_before_compilation']);self.assertEqual(sha(L/'positive01.v.snapshot.txt'),p['positive_sha256']);self.assertEqual(read(L/'positive01.json')['exit'],0)
  for n,v in p['variants'].items():
   t=(L/(n+'01.v.snapshot.txt')).read_text();a=s.index('Theorem '+v['theorem']);b=s.index('Proof.',a)
   self.assertEqual(t,s[:a]+s[a:b].replace(v['old'],v['new'],1)+s[b:]);self.assertEqual(proofs(s),proofs(t));self.assertEqual(sha(L/(n+'01.v.snapshot.txt')),v['sha256']);self.assertEqual(read(L/(n+'01.json'))['exit'],1)
  c=read(L/'control-results.json');self.assertTrue(c['negative_credit']);self.assertEqual(len(c['rows']),3)
  for r in c['rows']:self.assertTrue(r['failure_at_changed_output']);self.assertTrue(r['proofs_unchanged'])
  for i in range(1,6):self.assertEqual(read(L/(f'selector-spike{i:02d}.json'))['exit'],1)
  self.assertEqual(read(L/'selector-spike06.json')['exit'],0)
  a=read(L/'selector-decision-result.json')
  for k in ['passed','decoder_input_representation_single_factor','same_vtoZ','range_limited_exact_recovery','range_limited_injectivity','object_pointer_rejected']:self.assertTrue(a[k],k)
  self.assertEqual(a['without_range_counterexample'],[0,4294967296])
  for k in ['full_prefix_ablation_credit','Hook_execution_credit','downstream_credit','ABI_equivalence']:self.assertFalse(a[k],k)
 def test_build_trust_and_review(self):
  b=read(L/'build.json');self.assertEqual((b['exit'],b['active_sources'],b['old_products_reused']),(0,228,1135));self.assertFalse(b['source_only_cold_build'])
  t=read(L/'trust.json');self.assertTrue(t['passed']);self.assertTrue(t['assumptions_allowed']);self.assertEqual(t['roots_printed'],len(t['roots']));self.assertEqual(t['roots_printed'],59);self.assertEqual([c['exit'] for c in t['commands']],[0,0]);self.assertIn('V293TaskCreateStackEntry.V293_OSTaskCreateExt_to_stack_hook',t['roots'])
  rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),15)
  for r in rows:self.assertTrue(r['resolution']);self.assertIn(r['kind'],['test','bounded claim','limitation'])
