"""Fixed time body rules, independent spatial entry and prospective rejection."""
from pathlib import Path
import hashlib,json,re,unittest
ROOT=Path(__file__).resolve().parents[1];LOG=ROOT/'audit/logs/stage35-time-access';GATE=LOG/'gate01'
PROOF='certiucos/v293/proofs/V293TimeAccess.v';PROBE='audit/probes/V293TimeAccessProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TimeAccessTests(unittest.TestCase):
    def test_current_checked_inputs(self):
        gate=json.loads((GATE/'result.json').read_text());self.assertTrue(gate['passed']);self.assertEqual(gate['source_count'],176)
        for p,h in gate['input_sha256'].items():self.assertEqual(sha(ROOT/p),h,p)
    def test_fixed_source_correspondence(self):
        source=json.loads((GATE/'source/result.json').read_text());protocol=json.loads((LOG/'protocol.json').read_text())
        self.assertTrue(source['passed']);self.assertFalse(source['verified_frontend']);self.assertFalse(source['port_simulation'])
        self.assertEqual([f['identity'] for f in source['functions']],protocol['functions'])
        inventory=json.loads((ROOT/'audit/physical-access-inventory.json').read_text())
        self.assertEqual(inventory['source_identity_sha256'],protocol['source_identity'])
        for f in source['functions']:
            self.assertEqual(sha(ROOT/'csrc/upstream/v2.93.01/checkout/Source/os_time.c'),f['identity']['source_file_sha256'])
        self.assertEqual([c['exit'] for c in source['commands']],[0,0])
    def test_old_sources_and_exact_append(self):
        old=json.loads((LOG/'baseline.json').read_text())['files']
        sources=[p for p in old if p.endswith('.v') and p.startswith(('certiucos/v293/','framework/','tactics/'))]
        self.assertEqual(len(sources),175)
        for p in sources:self.assertEqual(sha(ROOT/p),old[p],p)
        data=(ROOT/'_CoqProject').read_bytes();suffix=(PROOF+'\n').encode()
        self.assertEqual(data.count(suffix),1);self.assertTrue(data.endswith(suffix));self.assertEqual(hashlib.sha256(data[:-len(suffix)]).hexdigest(),old['_CoqProject'])
    def test_bodies_and_real_rules(self):
        text=(ROOT/PROOF).read_text()
        for name in ['V293_OSTimeGet_body_hoare','V293_OSTimeSet_body_hoare']:
            theorem=text.split('Theorem '+name+' :',1)[1].split('Qed.',1)[0]
            self.assertIn('apply (V293_time_zero',theorem);self.assertIn('eapply V293_time_critical',theorem);self.assertIn('apply (V293_time_copy',theorem)
            pre=theorem.split('Proof.',1)[0]
            self.assertNotIn('evalval',pre);self.assertNotIn('store ',pre);self.assertNotIn('cstep',pre)
        self.assertIn('eapply rete_rule',text);self.assertIn('apply ret_rule',text)
        critical=text.split('Theorem V293_time_critical :',1)[1].split('Qed.',1)[0]
        for term in ['destruct enabled','encrit1_rule','encrit2_rule','excrit1_rule','excrit2_rule','invlth_isr I','forall extra']:
            self.assertIn(term,critical)
        self.assertNotRegex(text,r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit)\b')
    def test_nonvacuous_literal_entry(self):
        text=(ROOT/PROBE).read_text()
        for term in ['TimeEntrySpatial','TimeFrameSpatial','TimeGetterInstantiation','TimeSetterInstantiation','TimeLiteralReadback','V293_encoded_memory_mapsto','TimeApart 80%positive','TimeApart 81%positive','TimeApart 82%positive','clock Vundef Vundef TimeFrame','old (Vint32 new) Vundef TimeFrame','CurLINV V293_witness_li TimeTid']:
            self.assertIn(term,text)
        self.assertNotRegex(text,r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit)\b')
    def test_actual_compilation_and_kernel(self):
        commands=json.loads((GATE/'commands.json').read_text())
        self.assertEqual([c['exit'] for c in commands],[0,0,0,1,1,0]);self.assertTrue(all(c['passed'] for c in commands))
        self.assertEqual(commands[-1]['name'],'kernel')
        allowed={'FunctionalExtensionality.functional_extensionality_dep','Classical_Prop.classic'}
        for name,n in [('production',2),('probe',4)]:
            log=(GATE/(name+'.log')).read_text();self.assertEqual(log.count('Axioms:'),n)
            self.assertEqual(set(re.findall(r'^([A-Za-z][\w.]*)\s+:',log,re.M)),allowed)
    def test_single_factor_negatives(self):
        original=(ROOT/PROOF).read_text();ablations=json.loads((GATE/'ablations.json').read_text())
        self.assertEqual([a['name'] for a in ablations],['wrong-get-return','wrong-set-memory'])
        for a in ablations:
            self.assertTrue(a['expected_rejection_observed']);self.assertFalse(a['downstream_credit'])
            self.assertTrue(a['all_proofs_and_both_ASTs_unchanged'])
            mutant=(GATE/(a['name']+'.v.snapshot.txt')).read_text()
            self.assertNotEqual(mutant,original)
            self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',mutant,re.S),re.findall(r'Proof\.(.*?)Qed\.',original,re.S))
            log=(GATE/(a['name']+'.log')).read_text();self.assertIn('Error:',log)
            self.assertEqual(int(re.search(r'line (\d+),',log).group(1)),a['exact_connection_line'])
    def test_bounded_credit(self):
        gate=json.loads((GATE/'result.json').read_text())
        for key in ['actual_body_Hoare','both_initial_IE','allocated_local_entry','global_clock_is_caller_owned','reused_dependency_products']:self.assertTrue(gate[key],key)
        for key in ['full_shared_time_invariant','original_port_simulation','full_function_linked','good_os_proved','formal_six_gates_promoted','whole_source_clean_build']:self.assertFalse(gate[key],key)
