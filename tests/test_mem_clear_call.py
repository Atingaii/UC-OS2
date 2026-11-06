"""Real two-argument OS_MemClr call, allocation, loop and return evidence."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage45-mem-clear-call'
P='certiucos/v293/proofs/V293MemClrCall.v';B='audit/probes/V293MemClrCallProbe.v'
read=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class MemClearCallTests(unittest.TestCase):
    def test_all_old_sources_tests_c_and_evidence_retained(self):
        baseline=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md'}
        for p,h in baseline['files'].items():
            if p not in allowed:self.assertEqual(sha(R/p),h,p)
        self.assertEqual(len(baseline['sources']),188)
        sources=[s for s in (R/'_CoqProject').read_text().splitlines() if s.endswith('.v')]
        self.assertEqual(sources,baseline['sources']+[P]);self.assertEqual(len(sources),189)
    def test_fixed_c_identity_is_recomputed(self):
        x=read(L/'source/result.json');self.assertTrue(x['passed']);self.assertTrue(x['all94_identities_equal'])
        self.assertEqual(x['function']['name'],'OS_MemClr')
        self.assertEqual(x['source_identity'],'74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da')
        self.assertIn('*pdest++',x['body']);self.assertFalse(x['verified_frontend']);self.assertFalse(x['full_OSInit'])
    def test_stable_interface_has_no_store_or_free_oracle(self):
        s=(R/P).read_text();stmt=s.split('Theorem V293_OS_MemClr_call_return :',1)[1].split('Proof.',1)[0]
        for item in ['evalval ed (ge,caller,M)','evalval es (ge,caller,M)','fresh M bs','fresh M bp','exists Ms Mf','scall f [ed;es]','(ge,caller,Mf)','(forall k, (k<4)%nat','(forall k, (k<2)%nat']:
            self.assertIn(item,stmt)
        for forbidden in ['store ', 'free ', 'MemoryNotFull','Axiom','Admitted','Parameter','Conjecture']:self.assertNotIn(forbidden,stmt)
        for lemma in ['spcall_step','svfeval_step','svfevalnil_step','sfexec_step','sallocp_step','V293_tick_allocate_frame','V293_tick_raw_slot_update','V293_OS_MemClr_loop_execution','V293_tick_void_return']:self.assertIn(lemma,s)
    def test_independent_finite_entry_and_same_final_memory(self):
        s=(R/B).read_text();stmt=s.split('Theorem CallConcreteExecution :',1)[1].split('Proof.',1)[0]
        self.assertEqual(stmt.count('load '),6)
        for token in ['CallLiteralEntry','CallLiteralAST','CallFreshParameters','CallProgramLookup','CallConcreteInstance','Vundef;Vint32 (Int.repr 7)','71%positive','73%positive','CallByte 82%positive']:
            self.assertIn(token,s)
        self.assertNotIn('Require Import CertiOS.audit.probes.',s)
        self.assertEqual(read(L/'probe-final02.json')['exit'],0)
        self.assertEqual((L/'probe-final02.log').read_text().count('Axioms:')+(L/'probe-final02.log').read_text().count('Closed under the global context'),6)
    def test_actual_build_and_kernel_check(self):
        x=read(L/'build.json');self.assertEqual(x['exit'],0);self.assertEqual(x['active_sources'],189)
        self.assertEqual(x['old_products_reused'],940);self.assertFalse(x['source_only_cold_build'])
        x=read(L/'trust02.json');self.assertTrue(x['passed']);self.assertTrue(x['assumptions_allowed'])
        self.assertEqual([c['exit'] for c in x['commands']],[0,0]);self.assertEqual(len(x['roots']),x['roots_printed'])
        self.assertFalse(x['kernel_GOOD_OS']);self.assertNotIn('MemoryNotFull',str(x['assumptions']))
        for module in ['toptheorem','V293MemClrCall','V293MemClrCallProbe']:self.assertIn(module,str(x['commands'][-1]['command']))
    def test_prospective_single_factor_postcondition_controls(self):
        plan=read(L/'control-plan.json');rows=read(L/'control-results.json');s=(R/B).read_text()
        self.assertEqual(plan['positive_sha256'],sha(R/B));self.assertTrue(plan['frozen_before_execution'])
        self.assertEqual([x['name'] for x in rows],['positive','target-not-cleared','caller-pointer-advanced','freed-parameter-readable'])
        for row in rows:
            self.assertTrue(row['expected_result_observed']);self.assertTrue(row['proofs_unchanged']);self.assertTrue(row['single_factor'])
            self.assertFalse(row['all_execution_safety_credit'])
            snap=(L/(row['name']+'.v.snapshot.txt')).read_text()
            self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',snap,re.S),re.findall(r'Proof\.(.*?)Qed\.',s,re.S))
            self.assertEqual(hashlib.sha256(snap.encode()).hexdigest(),row['source_sha256'])
            if row['name']!='positive':
                control=next(x for x in plan['controls'] if x['name']==row['name'])
                self.assertEqual(snap,s.replace(control['old'],control['new'],1))
                self.assertEqual(row['actual_error_lines'],[row['expected_error_line']])
                log=(L/(row['name']+'.log')).read_text()
                for forbidden in ['Syntax error','Cannot find library','inconsistent assumptions','was not found']:self.assertNotIn(forbidden,log)
    def test_unchanged_boundaries_and_explicit_adversarial_review(self):
        x=read(L/'adversarial-review.json');self.assertGreaterEqual(len(x),8)
        for row in x:self.assertTrue(row['resolution']);self.assertIn(row['kind'],['test','bounded claim','limitation'])
        x=read(L/'proof-report.json')
        for key in ['old_sources_unchanged','old_tests_unchanged','old_evidence_unchanged','real_argument_evaluation','actual_parameter_allocation','actual_parameter_free','caller_restored']:self.assertTrue(x[key],key)
        for key in ['full_pointer_table','full_TCB_list','OSInit_reachability','OSStart_reachability','all_execution_safety','GOOD_OS','same_program_K1_K4','ucos3_started','six_gates_promoted','git_commit_or_push']:self.assertFalse(x[key],key)
        self.assertEqual(x['goal_status'],'active')
