"""Normalized OS_TCBInit prefix: not raw-port or whole-function verification."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage59-tcb-init-prefix'
C='certiucos/v293/code/V293OSTCBInitPrefix.v';P='certiucos/v293/proofs/V293TCBInitPrefix.v';B='audit/probes/V293TCBInitPrefixProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TCBInitPrefixTests(unittest.TestCase):
 def test_previous_inputs_and_products(self):
  b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
  for p,h in b['files'].items():
   if p not in allowed:self.assertEqual(sha(R/p),h,p)
  for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
  active=[p for p in (R/'_CoqProject').read_text().splitlines() if p.endswith('.v')]
  expected=b['sources']+[C,P];self.assertEqual(active[:len(expected)],expected)
  self.assertEqual((len(b['sources']),len(b['products'])),(215,1075))
 def test_fresh_source_and_manual_boundary(self):
  x=read(L/'source-connection.json');self.assertTrue(x['passed']);self.assertTrue(read(L/'source/result.json')['all94_identities_equal'])
  self.assertEqual(x['source_identity'],read(L/'protocol.json')['source_identity']);self.assertEqual(x['positions'],sorted(x['positions']));self.assertEqual(len(x['fields']),18)
  for k in ['manual_frontend','cpu_sr_byte_effects_erased','cpu_sr_declaration_init_outside_execution','actual_suffix_required_from_caller','success_suffix_untouched','failure_return_boundary_only']:self.assertTrue(x[k])
  for k in ['verified_frontend','raw_port_execution','hook_assumed_noop']:self.assertFalse(x[k])
  s=(R/C).read_text();self.assertIn('sifthen',s);self.assertIn('V293_TCBInit_empty)).',s);self.assertIn('V293_TCBInit_fields ptcb prio ptos pbos id stk_size pext opt) suffix',s)
 def test_stable_execution_not_assumed_results(self):
  s=(R/P).read_text()
  for name in ['V293_OS_TCBInit_prefix_execution','V293_OS_TCBInit_empty_prefix_execution']:
   stmt=s.split('Theorem '+name+' :',1)[1].split('Proof.',1)[0];entry=stmt.split('  exists Mf,')[0]
   for token in ['cstepstar','V293_local_steps','evalval','evaladdr','Mf']:self.assertNotIn(token,entry)
   self.assertIn('(enabled,si,ci)',stmt);self.assertIn('exists Mf',stmt)
  self.assertIn('apply PopStep',s);self.assertIn('exact Fields',s);self.assertIn('flag:=true',s);self.assertIn('flag:=false',s)
  empty=s.split('Theorem V293_OS_TCBInit_empty_prefix_execution :')[1].split('Proof.')[0]
  self.assertNotIn('V293_tcb_prefix_links',empty);self.assertNotIn('V293_tcb_init_old_fields',empty)
  for t in ['Axiom','Admitted','Parameter','Conjecture']:self.assertNotIn(t,s)
  x=read(L/'proof-report.json')
  for src,k in [(C,'code'),(P,'proof'),(B,'probe')]:self.assertEqual(sha(R/src),sha(L/x[k+'_snapshot']));self.assertEqual(read(L/x[k+'_result'])['exit'],0)
 def test_independent_physical_entry_and_same32loads(self):
  s=(R/B).read_text();self.assertNotIn('Require Import CertiOS.audit.probes.',s)
  checks=s.split('Definition PrefixChecks')[1].split('Lemma PrefixChecksCount')[0];self.assertEqual(len(re.findall(r'\(\(\d+%positive,',checks)),32)
  self.assertEqual(s.split('Definition PrefixOld')[1].split('Definition PrefixInputs')[0].count('(Vundef)'),18)
  for t in ['PrefixLiteralEntry','PrefixFreeBindings','PrefixEmptyLiteral','PrefixEmptyConcrete','forall p tail P ks enabled si ci suffix','p=12%nat \/ p=11%nat','load tp Mf a=Some v','Int.repr 8','Int.repr 77']:self.assertIn(t,s)
  x=read(L/'proof-report.json');self.assertEqual((x['success_checks_per_case'],x['independent_memory_cases'],x['success_instantiated_case_count']),(32,4,8));self.assertTrue(x['independent_cases_not_task_coexistence'])
 def test_single_pop_ablation(self):
  p=read(L/'ablation-plan02.json');x=read(L/'ablation-result.json');self.assertTrue(p['frozen_before_execution']);self.assertTrue(x['passed']);self.assertEqual((x['changed_cells'],x['unchanged_cells']),(1,31));self.assertTrue(x['only_pop_assignment_removed']);self.assertFalse(x['individual_18stores_tested'])
  orig=(L/'ablation01.v.snapshot.txt').read_text();final=(L/'ablation03.v.snapshot.txt').read_text();self.assertEqual(final,orig.replace('change (8+55<=4294967295)','change ((8+55<=4294967295)%Z)'))
  code=(R/C).read_text().split('Definition V293_TCBInit_prefix')[1].strip();removed=final.split('Definition NoPopPrefix')[1].split('Theorem NoPopExecution')[0].strip();self.assertEqual(removed,code.replace('(V293_TCBInit_pop free ptcb)','(sskip None)'))
  self.assertEqual([read(L/(n+'.json'))['exit'] for n in ['positive','positive02','ablation01','ablation02','ablation03']],[1,0,1,1,0])
 def test_four_distinct_negative_controls(self):
  p=read(L/'control-plan02.json');rows=read(L/'control-results.json');s=(L/'positive02.v.snapshot.txt').read_text();self.assertEqual(p['probe_sha256'],sha(R/B));self.assertEqual(p['positive_sha256'],sha(L/'positive02.v.snapshot.txt'))
  proofs=lambda t:re.findall(r'Proof\.(.*?)Qed\.',t,re.S)
  self.assertEqual(len(rows),5)
  for row in rows:
   for k in ['expected_result_observed','proofs_unchanged','single_factor']:self.assertTrue(row[k])
   if row['name']=='positive02':continue
   v=p['variants'][row['name']];t=(L/(row['name']+'.v.snapshot.txt')).read_text();self.assertEqual(t,s.replace(v['old'],v['new'],1));self.assertEqual(proofs(t),proofs(s));self.assertEqual(sha(L/(row['name']+'.v.snapshot.txt')),v['sha256']);self.assertEqual(row['actual_error_lines'],[v['expected_error_line']])
  self.assertEqual(len({r['expected_error_line'] for r in rows[1:]}),4)
 def test_build_and_trust(self):
  b=read(L/'build.json');self.assertEqual((b['exit'],b['active_sources'],b['old_products_reused']),(0,217,1075));self.assertFalse(b['source_only_cold_build'])
  t=read(L/'trust.json');self.assertTrue(t['passed']);self.assertTrue(t['assumptions_allowed']);self.assertEqual(t['roots_printed'],55);self.assertEqual(len(t['roots']),55);self.assertEqual([x['exit'] for x in t['commands']],[0,0]);self.assertTrue(read(L/'ablation-result.json')['assumptions_allowed'])
 def test_bounded_claims(self):
  x=read(L/'proof-report.json')
  for k in ['success_free_list_pop_executed','arbitrary_old_ptcb_and_18fields','typed_next_can_be_null','initial_IE_universal','interrupt_and_critical_stacks_preserved','empty_no_TCB_resource','empty_return_boundary_only','same_Mf_writable_ownership']:self.assertTrue(x[k])
  for k in ['raw_port_execution','verified_frontend','empty_return_and_free_executed','free_list_acyclicity_proved','whole_function_allocation','hooks_skipped','priority_publication_executed','ready_bitmap_insert_executed','task_counter_increment_executed','seven_call_output_connected','full_OS_TCBInit','full_OSInit','local_Hoare','all_execution_safety','full_94_function_program_instantiated','GOOD_OS','same_program_K1_K4','ucos3_started','six_gates_promoted','git_commit_or_push']:self.assertFalse(x[k])
  self.assertEqual(x['formal_six_gates'],[94,1,1,1,1,0]);self.assertEqual(x['goal_status'],'active');rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),30)
  for r in rows:self.assertTrue(r['resolution']);self.assertIn(r['kind'],['test','bounded claim','limitation'])
