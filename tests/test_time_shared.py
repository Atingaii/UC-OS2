"""Stage36 shared time getter evidence; historical gates are never rebound."""
from pathlib import Path
import hashlib,json,re,unittest
ROOT=Path(__file__).resolve().parents[1];LOG=ROOT/'audit/logs/stage36-time-shared';GATE=LOG/'gate01'
PROOF='certiucos/v293/proofs/V293TimeShared.v';PROBE='audit/probes/V293TimeSharedProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TimeSharedTests(unittest.TestCase):
    def test_current_checked_inputs(self):
        for p,h in json.loads((GATE/'inputs.json').read_text()).items():self.assertEqual(sha(ROOT/p),h,p)
    def test_old_sources_and_exact_append(self):
        old=json.loads((LOG/'baseline.json').read_text())['files']
        sources=[p for p in old if p.endswith('.v') and p.startswith(('certiucos/v293/','framework/','tactics/'))]
        self.assertEqual(len(sources),176)
        for p in sources:self.assertEqual(sha(ROOT/p),old[p],p)
        data=(ROOT/'_CoqProject').read_bytes();suffix=(PROOF+'\n').encode()
        self.assertEqual(data.count(suffix),1);self.assertTrue(data.endswith(suffix))
        self.assertEqual(hashlib.sha256(data[:-len(suffix)]).hexdigest(),old['_CoqProject'])
    def test_real_shared_body_without_clock_byte_entry(self):
        text=(ROOT/PROOF).read_text();root=text.split('Theorem V293_OSTimeGet_shared_body :',1)[1].split('Qed.',1)[0]
        statement=root.split('Proof.',1)[0]
        self.assertIn('V293_time_shared_locals',statement);self.assertNotIn('V293_time_shared_core',statement)
        self.assertNotIn('V293_time_payload',statement);self.assertNotIn('clock tmp',statement)
        for term in ['apply (V293_time_zero','apply V293_time_shared_critical_get','eapply rete_rule','exists clock']:
            self.assertIn(term,root)
        for term in ['evalval','store ','cstep','GoodI']:self.assertNotIn(term,statement)
        critical=text.split('Theorem V293_time_shared_critical_get :',1)[1].split('Qed.',1)[0]
        for term in ['encrit1_rule','excrit1_rule','V293_time_irq_open_asrt','V293_time_irq_close_asrt','apply V293_time_shared_copy','forall i, ir i=false']:
            self.assertIn(term,critical)
        self.assertNotRegex(text,r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit)\b')
    def test_integrated_time_and_invariant_shape(self):
        text=(ROOT/PROOF).read_text()
        core=text.split('Definition V293_time_shared_core bn :=',1)[1].split('Lemma',1)[0]
        self.assertIn('EX n : int32',core)
        self.assertIn('V293_time_shared_fields n ** PV (bn,Int.zero) @ Tint32 |-> Vint32 n',core)
        for term in ['V293_time_core_precise','V293_time_core_good','V293_time_core_isr','V293_time_shared_clock_agreement','V293_shared_fields t ts es n']:
            self.assertIn(term,text)
        self.assertNotIn('A_notin_lenv',core);self.assertNotIn('Alvarenv',core)
    def test_literal_joint_entry_and_absent_caller_clock(self):
        text=(ROOT/PROBE).read_text()
        for term in ['SharedJointEntry','SharedJointMemory','SharedCallerEntry','SharedCoreSpatial','SharedLiteralClockAgreement','SharedCallerLacksClock','SharedGetterInstantiation','GV_separate_rw','V293_encoded_memory_mapsto','get SharedLocalMemory (80%positive,i)=None']:
            self.assertIn(term,text)
        self.assertNotRegex(text,r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit)\b')
    def test_fresh_fixed_source_and_old_body_unchanged(self):
        source=json.loads((GATE/'source/result.json').read_text())
        previous=json.loads((ROOT/'audit/logs/stage35-time-access/protocol.json').read_text())
        self.assertTrue(source['passed']);self.assertFalse(source['verified_frontend']);self.assertFalse(source['port_simulation'])
        self.assertEqual([f['identity'] for f in source['functions']],previous['functions'])
        old=json.loads((LOG/'baseline.json').read_text())['files']
        for p in ['certiucos/v293/proofs/V293TimeAccess.v','audit/physical-access-inventory.json','audit/repaired-source-inventory.json']:
            self.assertEqual(sha(ROOT/p),old[p])
    def test_compilation_and_kernel(self):
        commands=json.loads((GATE/'commands.json').read_text())
        self.assertEqual([c['exit'] for c in commands],[0,0,0,1,1,0]);self.assertTrue(all(c['passed'] for c in commands))
        self.assertEqual(commands[-1]['name'],'kernel')
        allowed={'FunctionalExtensionality.functional_extensionality_dep','Classical_Prop.classic'}
        for name,n in [('production',3),('probe',6)]:
            log=(GATE/(name+'.log')).read_text()
            self.assertEqual(log.count('Axioms:')+log.count('Closed under the global context'),n)
            self.assertEqual(set(re.findall(r'^([A-Za-z][\w.]*)\s+:',log,re.M)),allowed)
    def test_single_factor_rejections_preserve_all_proofs(self):
        proof=(ROOT/PROOF).read_text();controls=json.loads((GATE/'ablations.json').read_text())
        self.assertEqual([c['name'] for c in controls],['wrong-local-snapshot','wrong-shared-clock'])
        for c in controls:
            self.assertTrue(c['single_factor']);self.assertTrue(c['expected_rejection_observed']);self.assertFalse(c['downstream_credit'])
            mutant=(GATE/(c['name']+'.v.snapshot.txt')).read_text()
            self.assertNotEqual(mutant,proof)
            self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',mutant,re.S),re.findall(r'Proof\.(.*?)Qed\.',proof,re.S))
            log=(GATE/(c['name']+'.log')).read_text()
            self.assertEqual(int(re.search(r'line (\d+),',log).group(1)),c['exact_connection_line'])
            self.assertIn('Current bullet',log)
    def test_bounded_credit(self):
        result=json.loads((GATE/'result.json').read_text())
        for k in ['shared_clock_body','abstract_physical_time_agreement','joint_entry_satisfiable','all_ISR_flags_clear_required','initial_IE_true_only','reused_dependency_products']:
            self.assertTrue(result[k],k)
        for k in ['caller_owns_clock_bytes','extended_GoodI_proved','setter_refinement','original_port_simulation','full_function_linked','good_os_proved','formal_six_gates_promoted','whole_source_clean_build']:
            self.assertFalse(result[k],k)
