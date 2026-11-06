"""Task-creation prefix only: no argument evaluation or Hook execution credit."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage66-task-create-reservation'
C='certiucos/v293/code/V293OSTaskCreateExtPrefix.v';P='certiucos/v293/proofs/V293TaskCreateExtPrefix.v';B='audit/probes/V293TaskCreateExtPrefixProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TaskCreateExtPrefixTests(unittest.TestCase):
 def test_preserved_baseline(self):
  b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
  self.assertEqual((len(b['files']),len(b['sources']),len(b['products'])),(15029,225,1125))
  for p,h in b['files'].items():
   if p not in allowed:self.assertEqual(sha(R/p),h,p)
  for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
  self.assertEqual([p for p in (R/'_CoqProject').read_text().splitlines() if p.endswith('.v')][:227],b['sources']+[C,P])
 def test_source_and_unconditional_prefix_interface(self):
  for p,n in [(C,'code01'),(P,'proof15'),(B,'probe02')]:
   self.assertEqual(sha(R/p),sha(L/(n+'.v.snapshot.txt')));self.assertEqual(read(L/(n+'.json'))['exit'],0)
   self.assertNotRegex((R/p).read_text(),r'\b(Axiom|Admitted|admit|Parameter|Conjecture)\b')
  source=read(L/'source-connection.json');self.assertTrue(source['passed']);self.assertTrue(source['all94_identities_equal'])
  self.assertEqual(source['source_identity'],read(R/'audit/repaired-source-inventory.json')['source_identity_sha256'])
  self.assertTrue(source['AST_guard_order_verified']);self.assertTrue(source['AST_success_statement_order_verified'])
  self.assertEqual(len(source['hook_declarations']),5)
  for h in source['hook_declarations']:self.assertFalse(h['defined'])
  s=(R/P).read_text();statement=s.split('Theorem V293_OSTaskCreateExt_to_stack_call_setup :')[1].split('Proof.')[0]
  self.assertNotIn('V293_local_steps',statement.split(' exists Mf,')[0]);self.assertNotIn('hook_return',statement)
  for t in ['kassignr (evar psp)','V293_OSTaskCreateExt_prefix_reserved','apply scalle_step','V293_create_prefix_cells','V293_local_trans']:self.assertIn(t,s)
  code=(R/C).read_text();self.assertIn('V293_task_prio_reserved_expr reserved',code);self.assertIn('sprim excrit',code)
 def test_literal_entries_and_explicit_boundaries(self):
  s=(R/B).read_text();self.assertNotIn('Require Import CertiOS.audit.probes.',s)
  for t in ['CreateLiteralEntry','CreateActualSetup','CreateTaskArgumentUnbound','p=0%nat \/ p=12%nat','CreateExpected p','load tp Mf a=Some v']:self.assertIn(t,s)
  p=read(L/'proof-report.json');self.assertEqual((p['unconditional_literal_entries'],p['typed_reads_per_entry']),(2,8))
  for k in ['body_entry','unconditional_normalized_prefix','real_CPU_zero_store','real_reservation_store','same_reserved_symbol_ADR0004','actual_scalle_setup','IE_universally_quantified','si_ci_preserved','same_Mf_ownership']:self.assertTrue(p[k],k)
  for k in ['function_call_allocation','argument_evaluation','function_pointer_representation','Hook_lookup','Hook_sfexec','real_Hook_implementation','Hook_assumed_noop','whole_OSTaskCreateExt','stage65_TCB_call_linked','seven_call_actual_memories_linked','local_Hoare','all_execution_safety','GOOD_OS','same_program_K1_K4','ucos3_started']:self.assertFalse(p[k],k)
  self.assertEqual(p['formal_six_gates'],[94,1,1,1,1,0])
 def test_controls_and_single_factor_ablation(self):
  p=read(L/'control-plan02.json');s=(L/'positive01.v.snapshot.txt').read_text();proofs=lambda x:re.findall(r'Proof\.(.*?)Qed\.',x,re.S)
  self.assertTrue(p['frozen_before_execution']);self.assertEqual(sha(L/'positive01.v.snapshot.txt'),p['positive_sha256']);self.assertEqual(read(L/'positive01.json')['exit'],0)
  for n,v in p['variants'].items():
   t=(L/(n+'01.v.snapshot.txt')).read_text();a=s.index('Theorem '+v['theorem']);b=s.index('Proof.',a)
   self.assertEqual(t,s[:a]+s[a:b].replace(v['old'],v['new'],1)+s[b:]);self.assertEqual(proofs(s),proofs(t));self.assertEqual(sha(L/(n+'01.v.snapshot.txt')),v['sha256']);self.assertEqual(read(L/(n+'01.json'))['exit'],1)
  c=read(L/'control-results.json');self.assertTrue(c['negative_credit']);self.assertEqual(len(c['rows']),3)
  for r in c['rows']:self.assertTrue(r['failure_at_changed_output']);self.assertTrue(r['proofs_unchanged'])
  self.assertEqual(read(L/'ablation01.json')['exit'],1);self.assertEqual(read(L/'ablation02.json')['exit'],0)
  plan=read(L/'ablation-plan02.json');self.assertTrue(plan['frozen_before_execution']);self.assertEqual(sha(L/'ablation02.v.snapshot.txt'),plan['sha256'])
  a=read(L/'ablation-result.json');self.assertTrue(a['passed']);self.assertTrue(a['single_factor_RHS']);self.assertTrue(a['real_assignment_execution_both_cases']);self.assertTrue(a['cpu23_and_frame77_preserved']);self.assertFalse(a['prefix_credit']);self.assertFalse(a['downstream_credit'])
 def test_build_trust_and_review(self):
  b=read(L/'build.json');self.assertEqual((b['exit'],b['active_sources'],b['old_products_reused']),(0,227,1125));self.assertFalse(b['source_only_cold_build'])
  t=read(L/'trust.json');self.assertTrue(t['passed']);self.assertTrue(t['assumptions_allowed']);self.assertEqual(t['roots_printed'],len(t['roots']));self.assertEqual(t['roots_printed'],56);self.assertEqual([c['exit'] for c in t['commands']],[0,0]);self.assertIn('V293TaskCreateExtPrefix.V293_OSTaskCreateExt_to_stack_call_setup',t['roots'])
  rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),15)
  for r in rows:self.assertTrue(r['resolution']);self.assertIn(r['kind'],['test','bounded claim','limitation'])
