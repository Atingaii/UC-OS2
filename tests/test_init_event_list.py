"""Configured EventList full-call ownership, provenance and bounded evidence."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage50-init-event-list'
C='certiucos/v293/code/V293OSInitEventList.v';P='certiucos/v293/proofs/V293InitEventList.v';B='audit/probes/V293InitEventListProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class InitEventListTests(unittest.TestCase):
    def test_previous_inputs_and_products_preserved(self):
        b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
        for p,h in b['files'].items():
            if p not in allowed:self.assertEqual(sha(R/p),h,p)
        for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
        active=[p for p in (R/'_CoqProject').read_text().splitlines() if p.endswith('.v')]
        expected=b['sources']+[C,P];self.assertEqual(active[:len(expected)],expected)
        self.assertEqual(len(b['sources']),197);self.assertEqual(len(b['products']),985)
    def test_exact_configured_source_identity_and_layout(self):
        x=read(L/'source/result.json');y=read(L/'source-connection.json')
        self.assertTrue(x['passed']);self.assertTrue(x['all94_identities_equal']);self.assertTrue(y['passed'])
        self.assertEqual(x['source_identity'],'74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da')
        self.assertEqual(x['function']['name'],'OS_InitEventList')
        self.assertEqual(x['function']['preprocessed_body_sha256'],'230bd821cc790a82385212f2bde26fb379626776971cc295ee8d39a3e2ebc796')
        self.assertEqual(x['layout'],dict(event=16,event_count=2,event_array=32,type_offset=0,pointer_offset=4,counter_offset=8,group_offset=10,rows_offset=11,local_counter=2))
        self.assertEqual(y['local_widths'],[2,2,4,4]);self.assertEqual(y['event_field_pointer_type'],'void *')
        self.assertFalse(y['verified_frontend'])
    def test_actual_clear_loop_type_writes_and_call_lifecycle(self):
        c=(R/C).read_text();s=(R/P).read_text()
        self.assertIn('swhile (V293_event_link_guard ix)',c)
        self.assertEqual(c.count('sassign (V293_event_type_field pevent1)'),2)
        self.assertIn('ecast (evar pevent2) (Tptr Tvoid)',c)
        for token in ['V293_MemClr_call_owned oldevents','V293_fresh_parameters_away M','V293_rdy_while_true','V293_rdy_while_false','V293_OS_InitEventList_body_execution oldevents','V293_tick_void_return','sallocend_step','V293_raw_cells_return_many']:
            self.assertIn(token,s)
        for token in ['Axiom','Admitted','Parameter','Conjecture']:self.assertNotIn(token,s)
        x=read(L/'proof-report.json')
        for src,key in [(C,'code'),(P,'proof')]:
            self.assertEqual(read(L/x[key+'_result'])['exit'],0);self.assertEqual(sha(R/src),sha(L/x[key+'_snapshot']))
    def test_stable_interface_premises_not_result_oracle(self):
        s=(R/P).read_text().split('Theorem V293_OS_InitEventList_call_return :',1)[1].split('Proof.',1)[0]
        before=s.split('  exists Ms Mf,')[0]
        self.assertNotIn('Ms',before);self.assertNotIn('Mf',before)
        for p in ['fresh M bi','fresh M bn','fresh M b1','fresh M b2','P f=Some','P clear=Some','length oldevents=32%nat','V293_clr_bytes bt 0 oldevents']:
            self.assertIn(p,before)
        self.assertIn('get Mf (c,Z.of_nat k)=None',s)
    def test_nonzero_finite_entry_same_Mf_30_reads(self):
        s=(R/B).read_text();self.assertNotIn('Require Import CertiOS.audit.probes.',s)
        for token in ['EventLiteralEntry','EventLiteralAST','EventFinalCount','EventFinalValid','EventConcreteExecution','EventReturnConnections','repeat (Byte (Byte.repr 255)) 32','set emp 41%Z (110%positive,Tint32)','length EventFinalCells=30%nat']:
            self.assertIn(token,s)
        stmt=s.split('Theorem EventConcreteExecution :',1)[1].split('Proof.',1)[0]
        self.assertIn('load tp Mf a=Some v',stmt);self.assertNotIn('rule_type_val_match',stmt)
        x=read(L/'proof-report.json');self.assertEqual(x['concrete_load_instances'],5+22+3);self.assertEqual(x['freed_local_bytes'],12)
        self.assertEqual(read(L/x['probe_result'])['exit'],0);self.assertEqual(sha(R/B),sha(L/x['probe_snapshot']))
    def test_frozen_single_conclusion_controls(self):
        plan=read(L/'control-plan.json');rows=read(L/'control-results.json');positive=(L/'positive.v.snapshot.txt').read_text()
        self.assertTrue(plan['frozen_before_execution']);self.assertEqual(plan['positive_sha256'],sha(R/B));self.assertEqual(len(rows),5)
        self.assertEqual(plan['positive_harness_sha256'],sha(L/'positive.v.snapshot.txt'))
        for row in rows:
            self.assertTrue(row['expected_result_observed']);self.assertTrue(row['proofs_unchanged']);self.assertTrue(row['single_factor']);self.assertFalse(row['all_execution_safety_credit'])
            snap=(L/(row['name']+'.v.snapshot.txt')).read_text()
            self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',snap,re.S),re.findall(r'Proof\.(.*?)Qed\.',positive,re.S))
            if row['name']!='positive':self.assertEqual(row['actual_error_lines'],[row['expected_error_line']])
        self.assertIn('not mechanism ablations',plan['scope'])
    def test_formal_build_and_kernel_trust(self):
        x=read(L/'build.json');self.assertEqual(x['exit'],0);self.assertEqual(x['active_sources'],199)
        self.assertEqual(x['old_products_reused'],985);self.assertFalse(x['source_only_cold_build'])
        x=read(L/'trust.json');self.assertTrue(x['passed']);self.assertEqual(x['roots_printed'],75);self.assertEqual(len(x['roots']),75)
        self.assertEqual([c['exit'] for c in x['commands']],[0,0]);self.assertTrue(x['assumptions_allowed'])
    def test_review_and_bounded_claims(self):
        x=read(L/'proof-report.json');review=read(L/'adversarial-review.json');self.assertGreaterEqual(len(review),15)
        for row in review:self.assertTrue(row['resolution']);self.assertIn(row['kind'],['test','bounded claim','limitation'])
        for key in ['same_program_full_function_call','same_Mf_writable_ownership','real_clear_call','nonzero_finite_entry','nonempty_shadowed_caller','fresh_locals_explicit_premise']:self.assertTrue(x[key])
        for key in ['verified_frontend','linked_with_stage49_three_calls','local_Hoare','OSInit_reachability','OSStart_reachability','all_execution_safety','GOOD_OS','same_program_K1_K4','ucos3_started','six_gates_promoted','git_commit_or_push']:self.assertFalse(x[key])
        self.assertEqual(x['formal_six_gates'],[94,1,1,1,1,0]);self.assertEqual(x['goal_status'],'active')
