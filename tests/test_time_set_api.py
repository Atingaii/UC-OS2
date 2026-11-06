"""Actual shared-time API builders and a nonempty independent invocation fixture."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage39-time-set-api';G=L/'gate01'
P='certiucos/v293/proofs/V293TimeSetAPI.v';B='audit/probes/V293TimeSetAPIProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TimeSetAPITests(unittest.TestCase):
    def test_checked_identities_and_registration(self):
        inputs=json.loads((G/'inputs.json').read_text())
        for p in [P,B,'audit/logs/stage39-time-set-api/protocol.json','audit/logs/stage39-time-set-api/run-checks.py']:
            self.assertEqual(sha(R/p),inputs[p],p)
        self.assertEqual((R/'_CoqProject').read_text().splitlines().count(P),1)
    def test_old_sources_and_evidence_not_rewritten(self):
        old=json.loads((L/'baseline.json').read_text())['files']
        sources=[p for p in old if p.endswith('.v') and p.startswith(('framework/','tactics/','certiucos/v293/'))]
        self.assertEqual(len(sources),179)
        for p in sources:self.assertEqual(sha(R/p),old[p],p)
        for stage in ['stage36-time-shared','stage37-time-shared-good','stage38-time-shared-set']:
            manifest=json.loads((R/'audit/logs'/stage/'final-evidence-manifest.json').read_text())
            for p,h in manifest.items():self.assertEqual(sha(R/p),h,p)
    def test_real_builders_universal_contract(self):
        text=(R/P).read_text()
        for term in ['Theorem V293_TimeSet_api_contract','Some pre=BuildPreA\'','Some post=BuildRetA\'','V293_time_api_args','rev vl','V293_time_api_entry','V293_time_api_return','apply V293_OSTimeSet_shared_body','APIRule','apply api_rule','EqDomAPI','| (Vint32 n)::nil => V293_time_set_action n']:
            self.assertIn(term,text)
        stmt=text.split('Theorem V293_TimeSet_api_contract :',1)[1].split('Proof.',1)[0]
        self.assertIn('vl pre post',stmt)
        for extra in ['store ','evalval ','V293_time_shared_core','PV ']:self.assertNotIn(extra,stmt)
        self.assertNotRegex(text,r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture)\b')
    def test_names_from_local_invariant_not_caller_clock(self):
        text=(R/P).read_text()
        for term in ['p_local li t args ==> Agvarenv','V293_time_api_bind','astar_l_adomlenv_elim','NotLocal','V293_time_api_release_cell']:
            self.assertIn(term,text)
        text=(R/B).read_text()
        for term in ['Definition TimeAPILi : LocalInv','Agvarenv 1001%Z Tint32','TimeAPILiGood','TimeAPINoAbs','TimeAPIGlobal','TimeAPICallerEntry','TimeAPICallerLacksClock']:
            self.assertIn(term,text)
    def test_actual_literal_joint_entry_and_builder_inputs(self):
        text=(R/B).read_text()
        for term in ['TimeAPIActualBuilders','Some TimeAPIPre=BuildPreA\'','Some TimeAPIPost=BuildRetA\'','TimeAPIRejectsInvalidInputs','[Vnull]','[Vint32 (Int.repr 42);Vint32 Int.zero]','TimeAPIInstantiated','TimeAPIBodyFromBuilders','TimeAPIJointEntry','GV_separate_rw','V293_time_shared_core 80%positive ** TimeAPIPre']:
            self.assertIn(term,text)
        self.assertNotIn('Require Import CertiOS.audit.probes.',text)
        self.assertNotRegex(text,r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture)\b')
    def test_real_compilers_and_printed_assumptions(self):
        commands=json.loads((G/'commands.json').read_text())
        self.assertEqual([c['exit'] for c in commands],[0,0,0,1,1,0]);self.assertTrue(all(c['passed'] for c in commands))
        allowed={'FunctionalExtensionality.functional_extensionality_dep','Classical_Prop.classic'}
        for name,n in [('production',3),('probe',10)]:
            log=(G/(name+'.log')).read_text()
            self.assertEqual(log.count('Axioms:')+log.count('Closed under the global context'),n)
            self.assertTrue(set(re.findall(r'^([A-Za-z][\w.]*)\s+:',log,re.M))<=allowed)
    def test_single_factor_prospective_negative_controls(self):
        text=(R/P).read_text();controls=json.loads((G/'ablations.json').read_text())
        self.assertEqual([c['name'] for c in controls],['wrong-api-argument','wrong-local-type'])
        for c in controls:
            self.assertTrue(c['single_factor']);self.assertTrue(c['proofs_unchanged']);self.assertTrue(c['expected_rejection_observed']);self.assertFalse(c['downstream_credit'])
            mutant=(G/(c['name']+'.v.snapshot.txt')).read_text();log=(G/(c['name']+'.log')).read_text()
            self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',text,re.S),re.findall(r'Proof\.(.*?)Qed\.',mutant,re.S))
            if c['name']=='wrong-api-argument':self.assertEqual(mutant.replace('| (Vint32 n)::nil => V293_time_set_action Int.zero','| (Vint32 n)::nil => V293_time_set_action n'),text)
            else:self.assertEqual(mutant.replace('dcons saved Tint8 dnil','dcons saved Tint32 dnil',1),text)
            self.assertEqual(int(re.search(r'line (\d+),',log).group(1)),c['exact_connection_line'])
            for bad in ['Syntax error','Cannot find library','Cannot find a physical path','inconsistent assumptions']:self.assertNotIn(bad,log)
    def test_fixed_source_and_bounded_claims(self):
        source=json.loads((G/'source/result.json').read_text());old=json.loads((R/'audit/logs/stage35-time-access/protocol.json').read_text())
        self.assertTrue(source['passed']);self.assertEqual([f['identity'] for f in source['functions']],old['functions'])
        self.assertFalse(source['verified_frontend']);self.assertFalse(source['port_simulation'])
        result=json.loads((G/'result.json').read_text())
        for k in ['actual_pre_ret_builders','all_builder_inputs_quantified','actual_api_rule','global_binding_from_local_invariant','caller_no_clock_bytes','concrete_nonempty_NoAbs','literal_joint_nonvacuity','same_shared_invariant','framework_call_return_soundness_reused']:self.assertTrue(result[k],k)
        for k in ['independent_concrete_call_return_trace','verified_frontend','original_port_simulation','full_function_linked','initialized_reachability','all_ISR_safety','good_os_proved','formal_six_gates_promoted','whole_source_clean_build']:self.assertFalse(result[k],k)
