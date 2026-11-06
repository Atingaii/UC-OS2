"""Continuous task-publication fragment, not whole-function verification."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage60-tcb-publish'
C='certiucos/v293/code/V293OSTCBPublish.v';P='certiucos/v293/proofs/V293TCBPublish.v';B='audit/probes/V293TCBPublishProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TCBPublishTests(unittest.TestCase):
 def test_previous_inputs_and_products(self):
  b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
  for p,h in b['files'].items():
   if p not in allowed:self.assertEqual(sha(R/p),h,p)
  for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
  active=[p for p in (R/'_CoqProject').read_text().splitlines() if p.endswith('.v')];expected=b['sources']+[C,P]
  self.assertEqual(active[:len(expected)],expected);self.assertEqual((len(b['sources']),len(b['products'])),(217,1085))
 def test_fresh_source_and_manual_boundary(self):
  x=read(L/'source-connection.json');s=read(L/'source/result.json');self.assertTrue(x['passed']);self.assertTrue(s['all94_identities_equal']);self.assertEqual(x['source_identity'],s['source_identity'])
  for k in ['hooks_before_fragment','priority_table_write_before_fragment','manual_frontend','cpu_sr_bytes_erased']:self.assertTrue(x[k])
  for k in ['hook_execution_proved','priority_table_write_in_fragment','verified_frontend','raw_port_execution']:self.assertFalse(x[k])
  self.assertIn('OSTaskCtr++; ; V293_ExitCritical',x['exact_publication_fragment'])
  c=(R/C).read_text();self.assertEqual(c.count('(sassign'),7);self.assertEqual(c.count('(sifthen'),1);self.assertIn('sprim encrit',c);self.assertIn('sprim excrit',c);self.assertIn('(sskip None)',c);self.assertIn('ecast (ebinop oplus',c)
 def test_stable_execution_not_assumed_results(self):
  s=(R/P).read_text();stmt=s.split('Theorem V293_OS_TCBInit_publication_execution :')[1].split('Proof.')[0];entry=stmt.split(' exists Mf,')[0]
  for token in ['cstepstar','V293_local_steps','evalval','evaladdr','Mf']:self.assertNotIn(token,entry)
  for token in ['oldnext oldprev oldback','n<255','y<2','x<8']:self.assertIn(token,entry)
  self.assertIn('(enabled,si,ci)',stmt);self.assertIn('(Nat.setbit g y) (Nat.setbit r x) (S n)',stmt)
  for token in ['flag:=true','flag:=false','V293_pub_write P','S1','S2','S3','S4','S5','S6','S7']:self.assertIn(token,s)
  for token in ['Axiom','Admitted','Parameter','Conjecture']:self.assertNotIn(token,s)
  x=read(L/'proof-report.json')
  for src,k in [(C,'code'),(P,'proof'),(B,'probe')]:self.assertEqual(sha(R/src),sha(L/x[k+'_snapshot']));self.assertEqual(read(L/x[k+'_result'])['exit'],0)
 def test_independent_physical_cases_same_loads(self):
  s=(R/B).read_text();self.assertNotIn('Require Import CertiOS.audit.probes.',s)
  for token in ['PubLiteralEntry','PubBindings','PubChecksCount','forall p present P ks enabled si ci','p=12%nat \\/ p=11%nat','load tp Mf a=Some v','Int.repr 8','Int.repr 16','V293_byteval 85','V293_byteval 77','PubMemory (PubOld p present ++ PubFrame)']:self.assertIn(token,s)
  x=read(L/'proof-report.json');self.assertEqual((x['checks_per_null_case'],x['checks_per_nonnull_case'],x['independent_memory_cases'],x['instantiated_case_count'],x['typed_load_instances']),(12,13,4,8,100));self.assertTrue(x['null_case_has_no_old_TCB_storage']);self.assertTrue(x['independent_cases_not_task_coexistence'])
  c=(R/P).read_text().split('Definition V293_pub_cells')[1].split('Definition V293_pub_env')[0];self.assertIn('if present then [',c);self.assertIn('else nil',c)
 def test_single_row_ablation_and_frozen_corrections(self):
  p=read(L/'ablation-plan.json');x=read(L/'ablation-result.json');self.assertTrue(p['frozen_before_execution']);self.assertTrue(x['passed']);self.assertTrue(x['only_selected_ready_row_assignment_removed']);self.assertEqual((x['changed_cells'],x['unchanged_cells_null'],x['unchanged_cells_nonnull']),(1,11,12));self.assertFalse(x['all_other_store_ablations']);self.assertFalse(x['failed_harness_credit'])
  a,b,c,d=[(L/(n+'.v.snapshot.txt')).read_text() for n in ['ablation01','ablation02','ablation03','ablation04']]
  self.assertEqual(b,a.replace('Definition NoRowBody ptcb head group rows counter :=','Definition NoRowBody ptcb head group (rows : var) counter :='))
  self.assertEqual(c,b.replace('pose (M6 := M5). pose proof H5 as H6.','pose proof H5 as H6.').replace('M6','M5'))
  self.assertEqual(d,c.replace('change (8+54<=4294967295)','change ((8+54<=4294967295)%Z)').replace('change (16+24<=4294967295)','change ((16+24<=4294967295)%Z)'))
  stmts=lambda s:re.findall(r'Theorem \w+ :(.*?)Proof\.',s,re.S)
  self.assertEqual(stmts(a),stmts(b));self.assertEqual(stmts(b),stmts(c));self.assertEqual(stmts(c),stmts(d))
  orig=(R/C).read_text().split('Definition V293_TCB_publish_body',1)[1];orig='Definition V293_TCB_publish_body'+orig
  self.assertEqual(orig.count(p['removed_statement']),1)
  expected=orig.replace(p['removed_statement'],'       (sseq (sskip None)',1).replace('V293_TCB_publish_body','NoRowBody').replace('V293_TCB_publish','NoRowProgram').replace('NoRowBody ptcb head group rows counter :=','NoRowBody ptcb head group (rows : var) counter :=')
  self.assertEqual(d[d.index('Definition NoRowBody'):d.index('Theorem NoRowExecution')].strip(),expected.strip())
  for label,plan,key in [('ablation01','ablation-plan','removed_sha256'),('ablation02','ablation-plan02','candidate_sha256'),('ablation03','ablation-plan03','candidate_sha256'),('ablation04','ablation-plan04','candidate_sha256')]:self.assertEqual(sha(L/(label+'.v.snapshot.txt')),read(L/(plan+'.json'))[key])
  self.assertEqual([read(L/(n+'.json'))['exit'] for n in ['positive','ablation01','ablation02','ablation03','ablation04']],[0,1,1,1,0])
 def test_four_distinct_negative_controls(self):
  p=read(L/'control-plan.json');rows=read(L/'control-results.json');s=(L/'positive.v.snapshot.txt').read_text();self.assertEqual(p['probe_sha256'],sha(R/B));self.assertEqual(p['positive_sha256'],sha(L/'positive.v.snapshot.txt'))
  proofs=lambda t:re.findall(r'Proof\.(.*?)Qed\.',t,re.S)
  self.assertEqual(len(rows),5)
  for row in rows:
   for k in ['expected_result_observed','proofs_unchanged','single_factor']:self.assertTrue(row[k])
   if row['name']=='positive':continue
   v=p['variants'][row['name']];t=(L/(row['name']+'.v.snapshot.txt')).read_text();self.assertEqual(t,s.replace(v['old'],v['new'],1));self.assertEqual(proofs(t),proofs(s));self.assertEqual(sha(L/(row['name']+'.v.snapshot.txt')),v['sha256']);self.assertEqual(row['actual_error_lines'],[v['expected_error_line']]);self.assertEqual(read(L/(row['name']+'.json'))['exit'],1)
  self.assertEqual(len({r['expected_error_line'] for r in rows[1:]}),4)
 def test_build_and_trust(self):
  b=read(L/'build.json');self.assertEqual((b['exit'],b['active_sources'],b['old_products_reused']),(0,219,1085));self.assertFalse(b['source_only_cold_build'])
  t=read(L/'trust.json');self.assertTrue(t['passed']);self.assertTrue(t['assumptions_allowed']);self.assertEqual(t['roots_printed'],52);self.assertEqual(len(t['roots']),52);self.assertEqual([x['exit'] for x in t['commands']],[0,0]);self.assertTrue(read(L/'ablation-result.json')['assumptions_allowed'])
 def test_bounded_claims(self):
  x=read(L/'proof-report.json')
  for k in ['actual_null_guard','new_next_and_prev_stores','conditional_old_head_prev_store','list_head_store','group_OR_store','selected_ready_row_OR_store','task_counter_increment_store','initial_IE_universal','interrupt_and_critical_stacks_preserved','same_Mf_writable_ownership','arbitrary_old_links','entry_owns_selected_fields_only','protocol_allocation_wording_narrowed']:self.assertTrue(x[k])
  for k in ['raw_port_execution','verified_frontend','whole_TCB_allocation_proved','full_list_invariant','priority_field_mask_relation_proved','counter_wrap_proved','hook_execution','hooks_assumed_noop','priority_table_write_executed','prefix_output_connected','seven_call_output_connected','return_executed','full_OS_TCBInit','full_OSInit','local_Hoare','all_execution_safety','full_94_function_program_instantiated','GOOD_OS','same_program_K1_K4','ucos3_started','six_gates_promoted','git_commit_or_push']:self.assertFalse(x[k])
  self.assertEqual(x['formal_six_gates'],[94,1,1,1,1,0]);self.assertEqual(x['goal_status'],'active');rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),30)
  for r in rows:self.assertTrue(r['resolution']);self.assertIn(r['kind'],['test','bounded claim','limitation'])
