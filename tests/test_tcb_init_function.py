"""Whole empty-free-list call lifecycle, not full success or whole-kernel credit."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage61-tcb-empty-call'
C='certiucos/v293/code/V293OSTCBInitFunction.v';P='certiucos/v293/proofs/V293TCBInitFunction.v';B='audit/probes/V293TCBInitFunctionProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TCBInitFunctionTests(unittest.TestCase):
 def test_previous_inputs_and_products(self):
  b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
  for p,h in b['files'].items():
   if p not in allowed:self.assertEqual(sha(R/p),h,p)
  for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
  active=[p for p in (R/'_CoqProject').read_text().splitlines() if p.endswith('.v')];expected=b['sources']+[C,P]
  self.assertEqual(active[:len(expected)],expected);self.assertEqual((len(b['sources']),len(b['products'])),(219,1095))
 def test_fresh_source_full_syntax_and_boundary(self):
  x=read(L/'source-connection.json');s=read(L/'source/result.json');self.assertTrue(x['passed']);self.assertTrue(s['all94_identities_equal']);self.assertEqual(x['source_identity'],s['source_identity'])
  self.assertEqual(sum(r['bytes'] for r in x['parameters']+x['locals']),29);self.assertEqual(x['parameter_allocation_order'],[107,106,105,104,103,102,101]);self.assertEqual(x['local_allocation_order'],[108,109])
  self.assertTrue(x['hooks_retained_as_calls']);self.assertTrue(x['cpu_sr_explicit_zero_store']);self.assertTrue(x['cpu_sr_token_effects_erased']);self.assertFalse(x['verified_frontend']);self.assertFalse(x['success_executed'])
  for row in x['hook_definitions']:self.assertEqual(row['declarations'],1);self.assertFalse(row['defined'])
  c=(R/C).read_text()
  for t in ['scall hook_init (evar 108%Z::nil)','scall hook_create (evar 108%Z::nil)','V293_TCB_publish 108%Z 93%Z 94%Z 95%Z 96%Z','sassign (evar 109%Z) (econst32 Int.zero)']:self.assertIn(t,c)
 def test_real_entry_alloc_store_return(self):
  s=(R/P).read_text();stmt=s.split('Theorem V293_OS_TCBInit_empty_call_return :')[1].split('Proof.')[0];entry=stmt.split(' exists Ms Mf,')[0]
  for t in ['V293_local_steps','cstepstar','evalval','evaladdr','Mf']:self.assertNotIn(t,entry)
  for t in ['NoDup','fresh M','V293_tcb_function_values_valid','Vnull']:self.assertIn(t,entry)
  self.assertEqual(s.count('eapply sallocp_step;'),7);self.assertEqual(s.count('eapply salloclv_step;'),2)
  for t in ['V293_error_return_execution','V293_raw_cells_return_many','sfexec_step','sallocend_step','V293_OS_TCBInit_empty_prefix_execution']:self.assertIn(t,s)
  for t in ['Axiom','Admitted','Parameter','Conjecture']:self.assertNotIn(t,s)
  x=read(L/'proof-report.json')
  for src,k in [(C,'code'),(P,'proof'),(B,'probe')]:self.assertEqual(sha(R/src),sha(L/x[k+'_snapshot']));self.assertEqual(read(L/x[k+'_result'])['exit'],0)
 def test_independent_literal_caller_and_released_bytes(self):
  s=(R/B).read_text();self.assertNotIn('Require Import CertiOS.audit.probes.',s)
  for t in ['CallLiteralEntry','CallAbsentLocals','CallFreedByteCount','CallHooksAbsent','CallConcreteExecution','29%nat','p=12%nat \\/ p=11%nat','set emp 108%Z (602%positive,Tint8)','load Tint8 Mf (602%positive,0)=Some(Vint32(Int.repr 88))','get Mf (b,Z.of_nat k)=None']:self.assertIn(t,s)
  x=read(L/'proof-report.json');self.assertEqual((x['freed_objects'],x['freed_bytes'],x['independent_memory_cases'],x['instantiated_case_count'],x['typed_load_instances'],x['freed_byte_instances']),(9,29,2,4,12,116));self.assertTrue(x['independent_cases_not_task_coexistence']);self.assertTrue(x['no_TCB_storage_required']);self.assertTrue(x['chosen_fresh_blocks_required'])
 def test_callee_availability_ablation_only(self):
  p=read(L/'ablation-plan.json');x=read(L/'ablation-result.json');self.assertTrue(p['frozen_before_execution']);self.assertEqual(sha(L/'ablation01.v.snapshot.txt'),p['sha256']);self.assertEqual(read(L/'ablation01.json')['exit'],0)
  for k in ['passed','single_factor','only_callee_definition_removed','same_entry_same_arguments_same_memory','has_no_loststep','whole_call_availability_only','assumptions_allowed']:self.assertTrue(x[k])
  self.assertFalse(x['downstream_mechanisms_individually_ablated'])
  s=(L/'ablation01.v.snapshot.txt').read_text();self.assertIn('Definition MissingProgram f := if Z.eq_dec f 500%Z then None else CallProgram f.',s);self.assertIn('forall f, f<>500%Z -> MissingProgram f=CallProgram f',s)
 def test_four_frozen_endpoint_controls(self):
  p=read(L/'control-plan.json');rows=read(L/'control-results.json');s=(L/'positive.v.snapshot.txt').read_text();proofs=lambda t:re.findall(r'Proof\.(.*?)Qed\.',t,re.S)
  self.assertTrue(p['frozen_before_execution']);self.assertEqual(sha(R/B),p['probe_sha256']);self.assertEqual(sha(L/'positive.v.snapshot.txt'),p['positive_sha256']);self.assertEqual(len(rows),5)
  for row in rows:
   for k in ['expected_result_observed','proofs_unchanged','single_factor']:self.assertTrue(row[k])
   if row['name']=='positive':continue
   v=p['variants'][row['name']];t=(L/(row['name']+'.v.snapshot.txt')).read_text();a=s.index('Theorem '+v['section']);b=s.index('Qed.',a)
   self.assertEqual(t,s[:a]+s[a:b].replace(v['old'],v['new'],1)+s[b:]);self.assertEqual(proofs(t),proofs(s));self.assertEqual(sha(L/(row['name']+'.v.snapshot.txt')),v['sha256']);self.assertEqual(row['actual_error_lines'],[v['expected_error_line']])
  self.assertEqual(len({r['expected_error_line'] for r in rows[1:]}),4)
 def test_build_and_trust(self):
  b=read(L/'build.json');self.assertEqual((b['exit'],b['active_sources'],b['old_products_reused']),(0,221,1095));self.assertFalse(b['source_only_cold_build'])
  t=read(L/'trust.json');self.assertTrue(t['passed']);self.assertTrue(t['assumptions_allowed']);self.assertEqual(t['roots_printed'],53);self.assertEqual(len(t['roots']),53);self.assertEqual([c['exit'] for c in t['commands']],[0,0])
 def test_bounded_claims_and_open_success(self):
  x=read(L/'proof-report.json')
  for k in ['actual_parameter_stores','actual_null_guard','return_executed','caller_restored','initial_IE_universal','interrupt_and_critical_stacks_preserved','same_Mf_owned_head_and_frame','hook_calls_retained','manual_frontend','cpu_sr_token_effects_erased']:self.assertTrue(x[k])
  for k in ['verified_frontend','raw_port_execution','argument_expression_evaluation','hook_definitions_available','hooks_assumed_noop','success_hook_execution','priority_table_write_executed','full_success_execution','seven_call_output_connected','reachable_empty_list_from_seven_calls_proved','automatic_freshness_from_M','local_Hoare','all_execution_safety','full_OS_TCBInit','full_OSInit','full_94_function_program_instantiated','GOOD_OS','same_program_K1_K4','ucos3_started','six_gates_promoted','git_commit_or_push']:self.assertFalse(x[k])
  self.assertEqual(x['formal_six_gates'],[94,1,1,1,1,0]);self.assertEqual(x['goal_status'],'active');rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),30)
  for r in rows:self.assertTrue(r['resolution']);self.assertIn(r['kind'],['test','bounded claim','limitation'])
