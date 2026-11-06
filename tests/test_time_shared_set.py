"""Shared setter: actual kernel checks, nonvacuity and bounded claims."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage38-time-shared-set';G=L/'gate01'
P='certiucos/v293/proofs/V293TimeSharedSet.v';B='audit/probes/V293TimeSharedSetProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TimeSharedSetTests(unittest.TestCase):
    def test_production_and_probe_identities(self):
        inputs=json.loads((G/'inputs.json').read_text())
        for p in [P,B,'audit/logs/stage38-time-shared-set/protocol.json','audit/logs/stage38-time-shared-set/run-checks.py']:
            self.assertEqual(sha(R/p),inputs[p],p)
        # Appending future modules does not invalidate this module's registration.
        self.assertEqual((R/'_CoqProject').read_text().splitlines().count(P),1)
    def test_old_sources_and_frozen_evidence(self):
        old=json.loads((L/'baseline.json').read_text())['files']
        sources=[p for p in old if p.endswith('.v') and p.startswith(('framework/','tactics/','certiucos/v293/'))]
        self.assertEqual(len(sources),178)
        for p in sources:self.assertEqual(sha(R/p),old[p],p)
        for stage in ['stage36-time-shared','stage37-time-shared-good']:
            manifest=json.loads((R/'audit/logs'/stage/'final-evidence-manifest.json').read_text())
            for p,h in manifest.items():self.assertEqual(sha(R/p),h,p)
    def test_legal_abstract_step_not_state_relabel(self):
        text=(R/P).read_text()
        for term in ['Definition V293_time_set_step : osabstep','vl = (Vint32 n :: nil)','get O ostmid = Some (ostm old)','result = (None, set O ostmid (ostm n))','spec_prim_step','eqdomO_set2','tidsame','absinfer_prim','spec_stepS','change_aop_rule','V293_shared_replace_slot']:
            self.assertIn(term,text)
        self.assertNotRegex(text,r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture)\b')
    def test_actual_body_connection(self):
        text=(R/P).read_text()
        for term in ['Theorem V293_time_shared_set_copy','abscsq_rule','NoAbs li','can_change_aop frame','V293_time_set_close','apply V293_time_copy.','Theorem V293_OSTimeSet_shared_body','(V293_TimeSet_body now ticks saved)','V293_time_zero','V293_time_shared_critical_set','encrit1_rule','excrit1_rule','apply ret_rule']:
            self.assertIn(term,text)
        stmt=text.split('Theorem V293_OSTimeSet_shared_body :',1)[1].split('Proof.',1)[0]
        self.assertNotIn('store ',stmt);self.assertNotIn('evalval',stmt);self.assertNotIn('PV ',stmt)
        self.assertIn('<||V293_time_set_action n||>',stmt);self.assertIn('<||END None||>',stmt)
    def test_literal_entry_not_only_conditional_contract(self):
        text=(R/B).read_text()
        for term in ['SetterJointEntry','SetterCurrentFull','GV_separate_rw','SetterCallerLacksClock','SetterCallerEntry','SetterBodyInstantiation','SetterNoAbs','Int.repr 7 <> Int.repr 42','SetterLiteralAbstractTransition']:
            self.assertIn(term,text)
        self.assertNotIn('Require Import CertiOS.audit.probes.',text)
        self.assertNotRegex(text,r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture)\b')
    def test_actual_coqc_coqchk_and_assumptions(self):
        commands=json.loads((G/'commands.json').read_text())
        self.assertEqual([c['exit'] for c in commands],[0,0,0,1,1,0]);self.assertTrue(all(c['passed'] for c in commands))
        allowed={'FunctionalExtensionality.functional_extensionality_dep','Classical_Prop.classic'}
        for name,n in [('production',4),('probe',6)]:
            log=(G/(name+'.log')).read_text()
            self.assertEqual(log.count('Axioms:')+log.count('Closed under the global context'),n)
            self.assertTrue(set(re.findall(r'^([A-Za-z][\w.]*)\s+:',log,re.M))<=allowed)
    def test_prospective_single_factor_rejections(self):
        text=(R/P).read_text();controls=json.loads((G/'ablations.json').read_text())
        self.assertEqual([c['name'] for c in controls],['neutralized-abstract-update','wrong-physical-write'])
        for c in controls:
            self.assertTrue(c['single_factor']);self.assertTrue(c['expected_rejection_observed']);self.assertFalse(c['downstream_credit'])
            mutant=(G/(c['name']+'.v.snapshot.txt')).read_text();log=(G/(c['name']+'.log')).read_text()
            if c['name']=='neutralized-abstract-update':
                self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',text,re.S),re.findall(r'Proof\.(.*?)Qed\.',mutant,re.S))
                self.assertEqual(mutant.replace('result = (None, set O ostmid (ostm old)).','result = (None, set O ostmid (ostm n)).'),text)
            else:self.assertEqual(mutant.replace('apply V293_time_copy with (c:=Int.one).','apply V293_time_copy.'),text)
            self.assertEqual(int(re.search(r'line (\d+),',log).group(1)),c['exact_connection_line'])
            for bad in ['Syntax error','Cannot find library','Cannot find a physical path','inconsistent assumptions']:self.assertNotIn(bad,log)
    def test_fixed_c_and_honest_scope(self):
        source=json.loads((G/'source/result.json').read_text());old=json.loads((R/'audit/logs/stage35-time-access/protocol.json').read_text())
        self.assertTrue(source['passed']);self.assertEqual([f['identity'] for f in source['functions']],old['functions'])
        self.assertFalse(source['verified_frontend']);self.assertFalse(source['port_simulation'])
        result=json.loads((G/'result.json').read_text())
        for k in ['same_shared_invariant','real_physical_assignment','legal_abstract_primitive','full_normalized_setter_body','entry_clock_bytes_owned_by_inv','NoAbs_required','literal_old_new_different','literal_joint_nonvacuity']:self.assertTrue(result[k],k)
        for k in ['original_port_simulation','full_function_linked','initialized_reachability','all_ISR_safety','good_os_proved','formal_six_gates_promoted','whole_source_clean_build']:self.assertFalse(result[k],k)
