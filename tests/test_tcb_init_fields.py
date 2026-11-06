"""Configured OS_TCBInit contiguous-store slice; deliberately not a whole-call claim."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage58-tcb-init-fields'
C='certiucos/v293/code/V293OSTCBInit.v';P='certiucos/v293/proofs/V293TCBInitFields.v';B='audit/probes/V293TCBInitFieldsProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TCBInitFieldsTests(unittest.TestCase):
 def test_previous_inputs_and_products_preserved(self):
  b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
  for p,h in b['files'].items():
   if p not in allowed:self.assertEqual(sha(R/p),h,p)
  for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
  active=[p for p in (R/'_CoqProject').read_text().splitlines() if p.endswith('.v')];expected=b['sources']+[C,P]
  self.assertEqual(active[:len(expected)],expected);self.assertEqual(len(b['sources']),213);self.assertEqual(len(b['products']),1065)
 def test_fixed_source_order_and_independent_layout(self):
  s=read(L/'source/result.json');x=read(L/'source-connection.json');plan=read(L/'protocol.json');self.assertTrue(s['all94_identities_equal']);self.assertTrue(x['passed']);self.assertEqual(s['source_identity'],plan['source_identity']);self.assertEqual(x['ordered_fields'],plan['ordered_fields'])
  self.assertEqual(len(x['ordered_fields']),18);self.assertEqual((x['size'],x['written_bytes'],x['untouched_bytes']),(56,44,12))
  body=(L/'source/OS_TCBInit.body.c.snapshot.txt').read_text();start=body.index('ptcb->OSTCBStkPtr = ptos;');stop=body.index('OSTCBInitHook(ptcb);');fragment=body[start:stop]
  self.assertEqual(re.findall(r'ptcb->(\w+)\s*=',fragment),[r['name'] for r in plan['ordered_fields']])
  code=(R/C).read_text();self.assertEqual([int(t) for t in re.findall(r'sassign \(efield \(ederef \(evar ptcb\)\) (\d+)%Z\)',code)],[r['tag'] for r in plan['ordered_fields']])
  for row in x['ordered_fields']:self.assertEqual(row['offset'],x['clang_offsets'][row['name']])
  self.assertTrue(x['manual_frontend']);self.assertFalse(x['verified_frontend']);self.assertFalse(x['configured_stack_clear']);self.assertTrue(x['hooks_not_skipped'])
 def test_actual_stores_not_result_premises(self):
  s=(R/P).read_text();stmt=s.split('Theorem V293_OS_TCBInit_fields_execution :',1)[1].split('Proof.',1)[0];entry=stmt.split('  exists Mf,')[0]
  for token in ['cstepstar','evalval','evaladdr','Mf','V293_task_record']:self.assertNotIn(token,entry)
  for token in ['p<13','0<=base','base+55','V293_tcb_init_old_fields','V293_tcb_init_input_cells']:self.assertIn(token,entry)
  self.assertEqual(len(re.findall(r'^  V293_tcb_init_write P ',s,re.M)),18)
  for token in ['V293_tcb_init_read H13 11 Coord13','V293_tcb_init_read H14 12 Coord14','V293_tcb_init_mask_eval','V293_rekey_sequence_execution','V293_tcb_init_record_connection']:self.assertIn(token,s)
  for token in ['Axiom','Admitted','Parameter','Conjecture']:self.assertNotIn(token,s)
  x=read(L/'proof-report.json')
  for src,key in [(C,'code'),(P,'proof')]:self.assertEqual(sha(R/src),sha(L/x[key+'_snapshot']));self.assertEqual(read(L/x[key+'_result'])['exit'],0)
 def test_independent31_same_memory_readbacks_in_two_runs(self):
  s=(R/B).read_text();self.assertNotIn('Require Import CertiOS.audit.probes.',s)
  old=s.split('Definition InitOld :',1)[1].split('Definition InitInputs',1)[0];self.assertEqual(old.count('(Vundef)'),18)
  checks=s.split('Definition InitChecks ',1)[1].split('Lemma InitChecksCount',1)[0];self.assertEqual(len(re.findall(r'\(\(\d+%positive,',checks)),31)
  for token in ['InitLiteralEntry','InitEnvironment','InitChecksCount','length (InitChecks 12)=31%nat','InitConcreteExecution','InitIdleAndStat','Int.repr 4660','Int.repr 22136','Int.repr 8']:self.assertIn(token,s)
  stmt=s.split('Theorem InitConcreteExecution :',1)[1].split('Proof.',1)[0];self.assertIn('load tp Mf a=Some v',stmt);self.assertIn('InitState Mf |=',stmt);self.assertIn('V293_task_record Mf',stmt)
  x=read(L/'proof-report.json');self.assertEqual((x['checks_per_run'],x['concrete_load_instances'],x['independent_runs']),(31,62,2));self.assertFalse(x['Idle_Stat_coexistence']);self.assertEqual(sha(R/B),sha(L/x['probe_snapshot']));self.assertEqual(read(L/x['probe_result'])['exit'],0)
 def test_prospective_whole_fragment_noop_ablation(self):
  plan=read(L/'ablation-plan.json');x=read(L/'ablation-result.json');self.assertTrue(plan['frozen_before_execution']);self.assertTrue(x['passed']);self.assertTrue(x['single_factor']);self.assertFalse(x['individual_internal_mechanisms_tested']);self.assertEqual(x['measurements'],plan['measurements']);self.assertEqual(x['explicit_baseline_measurements'],6);self.assertEqual(x['explicit_removed_measurements'],6)
  extract=lambda s:re.search(r'Theorem InitWithoutWrites :(.*?)Proof\.',s,re.S).group(1)
  first=(L/'ablation01.v.snapshot.txt').read_text();self.assertEqual(sha(L/'ablation01.v.snapshot.txt'),plan['removed_sha256']);self.assertEqual(sha(L/'positive.v.snapshot.txt'),plan['baseline_sha256'])
  for i in range(1,9):self.assertEqual(extract((L/f'ablation{i:02}.v.snapshot.txt').read_text()),extract(first))
  self.assertEqual(read(L/'ablation01.json')['exit'],1);self.assertEqual(read(L/'ablation02.json')['exit'],-2);self.assertEqual(read(L/'ablation08.json')['exit'],0)
  s=(L/'ablation08.v.snapshot.txt').read_text();self.assertIn('ptomvallist_loadbytes',s);self.assertIn('V293_star_load_l',s);self.assertIn('Print Assumptions InitUndefLoad.',s);self.assertIn('apply c_stepstar0',s);self.assertNotIn('vm_compute',s)
 def test_four_distinct_final_interface_negative_controls(self):
  plan=read(L/'control-plan.json');rows=read(L/'control-results.json');self.assertTrue(plan['frozen_before_execution']);self.assertEqual(plan['probe_sha256'],sha(R/B));self.assertEqual(plan['positive_sha256'],sha(L/'positive.v.snapshot.txt'));self.assertEqual(len(rows),5)
  positive=(L/'positive.v.snapshot.txt').read_text();proofs=lambda s:re.findall(r'Proof\.(.*?)Qed\.',s,re.S)
  for row in rows:
   self.assertTrue(row['expected_result_observed']);self.assertTrue(row['proofs_unchanged']);self.assertTrue(row['single_factor']);s=(L/(row['name']+'.v.snapshot.txt')).read_text();self.assertEqual(proofs(s),proofs(positive))
   if row['name']!='positive':
    self.assertEqual(row['actual_error_lines'],[row['expected_error_line']]);p=plan['variants'][row['name']];self.assertEqual(sha(L/(row['name']+'.v.snapshot.txt')),p['sha256']);self.assertEqual(s,positive.replace(p['old'],p['new'],1))
  self.assertEqual(len({r['expected_error_line'] for r in rows if r['name']!='positive'}),4)
 def test_build_and_trust(self):
  b=read(L/'build.json');self.assertEqual(b['exit'],0);self.assertEqual(b['active_sources'],215);self.assertEqual(b['old_products_reused'],1065);self.assertFalse(b['source_only_cold_build']);x=read(L/'trust.json');self.assertTrue(x['passed']);self.assertEqual(x['roots_printed'],57);self.assertEqual(len(x['roots']),57);self.assertEqual([r['exit'] for r in x['commands']],[0,0]);self.assertTrue(x['assumptions_allowed']);self.assertTrue(read(L/'ablation-result.json')['assumptions_allowed'])
 def test_honest_limits_and_adversarial_review(self):
  x=read(L/'proof-report.json');rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),25)
  for r in rows:self.assertTrue(r['resolution']);self.assertIn(r['kind'],['test','bounded claim','limitation'])
  for k in ['arbitrary_old_values_including_Vundef','generic_nonzero_base','source_computed_masks_from_fields','same_Mf_writable_ownership','existing_task_record_connected','whole_fragment_noop_ablation']:self.assertTrue(x[k])
  for k in ['input_result_or_execution_premise','record_rdy_means_bitmap_membership','allocated_stack_validity','hooks_skipped','stack_initializer_contract_assumed','free_list_pop_executed','priority_publication_executed','ready_bitmap_insert_executed','task_counter_increment_executed','seven_call_output_connected','full_OS_TCBInit','verified_frontend','local_Hoare','all_execution_safety','OSInit_reachability','OSStart_reachability','full_94_function_program_instantiated','GOOD_OS','same_program_K1_K4','ucos3_started','six_gates_promoted','git_commit_or_push']:self.assertFalse(x[k])
  self.assertEqual(x['formal_six_gates'],[94,1,1,1,1,0]);self.assertEqual(x['goal_status'],'active');self.assertEqual(read(L/'function-progress.json')['formal_states'],dict(located=True,modeled=False,specified=False,local_hoare=False,component_linked=False,full_target_linked=False))
