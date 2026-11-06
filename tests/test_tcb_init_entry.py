"""Success path from function entry to real missing Hook, not whole-function credit."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage62-tcb-success-entry'
P='certiucos/v293/proofs/V293TCBInitEntry.v';B='audit/probes/V293TCBInitEntryProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TCBInitEntryTests(unittest.TestCase):
 def test_preserved_inputs_and_products(self):
  b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
  for p,h in b['files'].items():
   if p not in allowed:self.assertEqual(sha(R/p),h,p)
  for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
  active=[s for s in (R/'_CoqProject').read_text().splitlines() if s.endswith('.v')]
  self.assertEqual(active[:222],b['sources']+[P]);self.assertEqual((len(b['sources']),len(b['products'])),(221,1105))
 def test_source_and_real_entry(self):
  x=read(L/'source-connection.json');self.assertTrue(x['passed']);self.assertTrue(x['all94_identities_equal']);self.assertTrue(x['no_source_Hook_body_invented'])
  self.assertEqual(x['source_identity'],read(R/'audit/repaired-source-inventory.json')['source_identity_sha256'])
  for h in x['hook_declarations']:self.assertEqual(h['declarations'],1);self.assertFalse(h['defined'])
  s=(R/P).read_text();stmt=s.split('Theorem V293_OS_TCBInit_call_to_first_hook :')[1].split('Proof.')[0];pre=stmt.split(' exists b1')[0]
  for t in ['fresh M','NoDup','V293_local_steps','loststep','evalval','Mf']:self.assertNotIn(t,pre)
  for t in ['V293_tcb_fresh_nine M','V293_tcb_call_prologue','V293_OS_TCBInit_prefix_execution','spcall_step','svfevalnil_step','V293_missing_port_has_no_step']:self.assertIn(t,s)
  self.assertEqual(s.count('eapply sallocp_step;'),7);self.assertEqual(s.count('eapply salloclv_step;'),2)
  self.assertNotRegex(s,r'\b(Axiom|Admitted|admit|Parameter|Conjecture)\b')
  self.assertEqual(sha(R/P),sha(L/'production-final.v.snapshot.txt'));self.assertEqual(sha(R/B),sha(L/'probe04.v.snapshot.txt'))
 def test_literal_entry_reads_and_bound(self):
  s=(R/B).read_text();self.assertNotIn('Require Import CertiOS.audit.probes.',s)
  for t in ['SuccessLiteralEntry','SuccessExpected','SuccessConcreteExecution','602%positive,0%Z','SuccessStop','V293_tcb_init_read Owned 33%nat']:self.assertIn(t,s)
  p=read(L/'proof-report.json');self.assertEqual((p['allocated_objects'],p['allocated_bytes'],p['typed_reads_per_case'],p['typed_read_instances']),(9,29,25,200))
  for k in ['automatic_freshness_from_M','actual_hook_argument_evaluation','caller_frame_preserved','initial_IE_universal','interrupt_and_critical_stacks_preserved']:self.assertTrue(p[k])
  for k in ['first_hook_lookup_executed','success_return_executed','callee_objects_freed','caller_restored','priority_table_write_executed','publication_executed','seven_call_Mf_connected','Hook_assumed_noop','local_Hoare','all_execution_safety','GOOD_OS','same_program_K1_K4','ucos3_started']:self.assertFalse(p[k])
  self.assertEqual(p['formal_six_gates'],[94,1,1,1,1,0]);self.assertEqual(read(L/'probe04.json')['exit'],0)
 def test_prospective_controls_and_lookup_only(self):
  p=read(L/'control-plan.json');s=(L/'positive.v.snapshot.txt').read_text();proofs=lambda t:re.findall(r'Proof\.(.*?)Qed\.',t,re.S)
  self.assertTrue(p['frozen_before_execution']);self.assertEqual(sha(L/'positive.v.snapshot.txt'),p['positive_sha256']);self.assertEqual(sha(R/B),p['probe_sha256'])
  rows=read(L/'control-results.json');self.assertEqual(len(rows),5)
  for row in rows:self.assertTrue(row['expected_result_observed'])
  for n,v in p['variants'].items():
   t=(L/(n+'.v.snapshot.txt')).read_text();a=s.index('Theorem '+v['section']);b=s.index('Proof.',a)
   self.assertEqual(t,s[:a]+s[a:b].replace(v['old'],v['new'],1)+s[b:]);self.assertEqual(proofs(t),proofs(s));self.assertEqual(sha(L/(n+'.v.snapshot.txt')),v['sha256'])
  a=read(L/'ablation-result.json');self.assertTrue(a['passed']);self.assertTrue(a['same_endpoint_code_state_memory']);self.assertFalse(a['downstream_credit']);self.assertTrue(a['statements_unchanged_after_harness_fix'])
 def test_build_trust_and_honest_scope(self):
  b=read(L/'build.json');self.assertEqual((b['exit'],b['active_sources'],b['old_products_reused']),(0,222,1105));self.assertFalse(b['source_only_cold_build'])
  t=read(L/'trust.json');self.assertTrue(t['passed']);self.assertTrue(t['assumptions_allowed']);self.assertEqual(t['roots_printed'],len(t['roots']));self.assertEqual([c['exit'] for c in t['commands']],[0,0])
  rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),12)
  for r in rows:self.assertTrue(r['resolution']);self.assertIn(r['kind'],['test','bounded claim','limitation'])
