"""Same name-local invariant for actual shared-time GoodI and setter API."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage40-time-names-good';G=L/'gate01'
P='certiucos/v293/proofs/V293TimeNamesGood.v';B='audit/probes/V293TimeNamesGoodProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TimeNamesGoodTests(unittest.TestCase):
    def test_checked_identities_and_registration(self):
        inputs=json.loads((G/'inputs.json').read_text())
        for p in [P,B,'audit/logs/stage40-time-names-good/protocol.json','audit/logs/stage40-time-names-good/run-checks.py']:
            self.assertEqual(sha(R/p),inputs[p],p)
        self.assertEqual((R/'_CoqProject').read_text().splitlines().count(P),1)
    def test_old_sources_and_evidence_not_rewritten(self):
        old=json.loads((L/'baseline.json').read_text())['files']
        sources=[p for p in old if p.endswith('.v') and p.startswith(('framework/','tactics/','certiucos/v293/'))]
        self.assertEqual(len(sources),180)
        for p in sources:self.assertEqual(sha(R/p),old[p],p)
        for stage in ['stage36-time-shared','stage37-time-shared-good','stage38-time-shared-set','stage39-time-set-api']:
            manifest=json.loads((R/'audit/logs'/stage/'final-evidence-manifest.json').read_text())
            for p,h in manifest.items():self.assertEqual(sha(R/p),h,p)
    def test_canonical_names_and_actual_resource_properties(self):
        text=(R/P).read_text()
        for term in ['Definition V293_time_names_li','fun _ _ => Agvarenv now Tint32 (bn,0%Z)','V293_time_names_footprint','V293_time_names_local_good','V293_time_names_noabs','V293_time_names_global','==> Aemp','GoodLInvAsrt (V293_time_names_li','NoAbs (V293_time_names_li']:
            self.assertIn(term,text)
        self.assertNotRegex(text,r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture)\b')
    def test_changed_goodi_obligation_discharged(self):
        text=(R/P).read_text()
        for term in ['Theorem V293_time_names_good','[Frame [Current [Switch Sched]]]','[Live | Dead]','assert (Empty : Mx=emp /\\ Ox=emp)','apply V293_time_names_footprint in Local','subst Mx Ox','apply Return with (Mx:=emp) (Ox:=emp)','exact JM','exact JO']:
            self.assertIn(term,text)
        stmt=text.split('Theorem V293_time_names_good :',1)[1].split('Proof.',1)[0]
        self.assertIn('GoodI (V293_time_shared_inv bn) V293_scheduler (V293_time_names_li now bn)',stmt)
        self.assertNotIn('->',stmt)
    def test_compatible_api_and_nonempty_joint_fixture(self):
        text=(R/P).read_text();stmt=text.split('Theorem V293_time_names_compatible :',1)[1].split('Proof.',1)[0]
        self.assertEqual(stmt.count('(V293_time_shared_inv bn)'),2)
        self.assertEqual(stmt.count('(V293_time_names_li now bn)'),2)
        self.assertIn('apply V293_TimeSet_api_rule',text)
        text=(R/B).read_text()
        for term in ['Definition NamesLi : LocalInv := V293_time_names_li','NamesActualBuilders','NamesRejectsInvalidInputs','NamesJointEntry','NamesCallerEntry','NamesCallerLacksClock','GV_separate_rw','NamesSameGood','NamesSameAPI','NamesCombinedNonempty']:
            self.assertIn(term,text)
        self.assertNotIn('Require Import CertiOS.audit.probes.',text)
        self.assertNotRegex(text,r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture)\b')
    def test_real_coqc_coqchk_and_assumptions(self):
        commands=json.loads((G/'commands.json').read_text())
        self.assertEqual([c['exit'] for c in commands],[0,0,0,1,1,0]);self.assertTrue(all(c['passed'] for c in commands))
        allowed={'FunctionalExtensionality.functional_extensionality_dep','Classical_Prop.classic'}
        for name,n in [('production',3),('probe',8)]:
            log=(G/(name+'.log')).read_text()
            self.assertEqual(log.count('Axioms:')+log.count('Closed under the global context'),n)
            self.assertTrue(set(re.findall(r'^([A-Za-z][\w.]*)\s+:',log,re.M))<=allowed)
    def test_prospective_interface_ablation_boundaries(self):
        text=(R/B).read_text();controls=json.loads((G/'ablations.json').read_text())
        self.assertEqual([c['name'] for c in controls],['old-empty-good-direct','wrong-api-clock-block'])
        for c in controls:
            self.assertTrue(c['single_factor']);self.assertTrue(c['production_unchanged']);self.assertTrue(c['expected_rejection_observed']);self.assertTrue(c['interface_rejection_only']);self.assertFalse(c['semantic_execution_credit']);self.assertFalse(c['downstream_credit'])
            mutant=(G/(c['name']+'.v.snapshot.txt')).read_text();log=(G/(c['name']+'.log')).read_text()
            if c['name']=='old-empty-good-direct':self.assertEqual(mutant.replace('exact (V293_time_shared_good 80%positive).','exact (V293_time_names_good 1001%Z 80%positive).'),text)
            else:self.assertEqual(mutant.replace('V293_time_names_compatible 2000%Z 1001%Z 1002%Z 1003%Z 81%positive lg Spec','V293_time_names_compatible 2000%Z 1001%Z 1002%Z 1003%Z 80%positive lg Spec'),text)
            self.assertEqual(int(re.search(r'line (\d+),',log).group(1)),c['exact_connection_line'])
            for bad in ['Syntax error','Cannot find library','Cannot find a physical path','inconsistent assumptions','was not found']:self.assertNotIn(bad,log)
    def test_fixed_source_and_scope(self):
        source=json.loads((G/'source/result.json').read_text());old=json.loads((R/'audit/logs/stage35-time-access/protocol.json').read_text())
        self.assertTrue(source['passed']);self.assertEqual([f['identity'] for f in source['functions']],old['functions'])
        self.assertFalse(source['verified_frontend']);self.assertFalse(source['port_simulation'])
        result=json.loads((G/'result.json').read_text())
        for k in ['canonical_same_LocalInv','GoodI_all_four_obligations','dead_task_local_resource_normalized','GoodLInv_NoAbs_global_proved','actual_api_rule','literal_joint_nonvacuity','literal_combined_GoodI_API_entry','caller_no_clock_bytes','framework_call_return_soundness_reused']:self.assertTrue(result[k],k)
        for k in ['whole_task_local_invariant','initialized_reachability','all_ISR_safety','good_os_proved','same_program_K1_K4','ucos3_started','formal_six_gates_promoted','verified_frontend','original_port_simulation','independent_concrete_call_return_trace','whole_source_clean_build']:self.assertFalse(result[k],k)
