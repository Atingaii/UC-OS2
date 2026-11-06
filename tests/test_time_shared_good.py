"""Stage37: same integrated invariant, honest bounds, immutable old evidence."""
from pathlib import Path
import hashlib,json,re,unittest
ROOT=Path(__file__).resolve().parents[1];LOG=ROOT/'audit/logs/stage37-time-shared-good';GATE=LOG/'gate02'
PROOF='certiucos/v293/proofs/V293TimeSharedGood.v';PROBE='audit/probes/V293TimeSharedGoodProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TimeSharedGoodTests(unittest.TestCase):
    def test_current_checked_inputs(self):
        for p,h in json.loads((GATE/'inputs.json').read_text()).items():self.assertEqual(sha(ROOT/p),h,p)
    def test_old_sources_and_exact_append(self):
        old=json.loads((LOG/'baseline.json').read_text())['files']
        sources=[p for p in old if p.endswith('.v') and p.startswith(('certiucos/v293/','framework/','tactics/'))]
        self.assertEqual(len(sources),177)
        for p in sources:self.assertEqual(sha(ROOT/p),old[p],p)
        data=(ROOT/'_CoqProject').read_bytes();suffix=(PROOF+'\n').encode()
        self.assertEqual(data.count(suffix),1);self.assertTrue(data.endswith(suffix))
        self.assertEqual(hashlib.sha256(data[:-len(suffix)]).hexdigest(),old['_CoqProject'])
    def test_same_goodI_and_real_preservation(self):
        text=(ROOT/PROOF).read_text()
        self.assertIn('GoodI (V293_time_shared_inv bn) V293_scheduler V293_shared_li',text)
        good=text.split('Theorem V293_time_shared_good :',1)[1].split('Qed.',1)[0]
        self.assertNotIn('apply V293_shared_good',good)
        for term in ['V293_time_noisr_core','V293_shared_no_abstract_frame','V293_time_switch_store','indom ts ct','Mx = emp /\ Ox = emp','V293_scheduler_good']:self.assertIn(term,good)
        for term in ['V293_current_halves_write','GV_separate_rw','V293_shared_store_global','V293_shared_replace_slot']:self.assertIn(term,text)
        self.assertNotRegex(text,r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit)\b')
    def test_store_existence_not_assumed(self):
        text=(ROOT/PROOF).read_text();root=text.split('Theorem V293_time_owned_switch :',1)[1].split('Qed.',1)[0]
        statement=root.split('Proof.',1)[0]
        self.assertIn('exists Mf',statement)
        pre=statement.split('exists Mf',1)[0]
        for term in ['store ','evalval','cstep']:self.assertNotIn(term,pre)
        for term in ["store_exist_join'",'V293_time_switch_store','V293_shared_store_global','V293_shared_replace_slot','V293_shared_fields_get','mapstoval_load']:self.assertIn(term,root)
        for term in ['abstcblsid','absecblsid','ostmid','load (Tptr tp) Mf','load Tint32 Mf']:self.assertIn(term,statement)
    def test_literal_different_task_and_both_maps(self):
        text=(ROOT/PROBE).read_text()
        for term in ['SwitchLiteralOwnedEntry','SwitchLiteralSWINVEntry','SwitchLiteralExecution','SwitchLiveTaskBranch','SwitchDeadTaskBranch','SwitchBothTaskMaps','91%positive','92%positive','V293_encoded_memory_mapsto','SwitchAbstract ts es n','load Tint32 Mf']:self.assertIn(term,text)
        self.assertNotRegex(text,r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit)\b')
    def test_compilation_and_kernel(self):
        commands=json.loads((GATE/'commands.json').read_text())
        self.assertEqual([c['exit'] for c in commands],[0,0,0,1,1,0]);self.assertTrue(all(c['passed'] for c in commands))
        allowed={'FunctionalExtensionality.functional_extensionality_dep','Classical_Prop.classic'}
        for name,n in [('production',2),('probe',6)]:
            log=(GATE/(name+'.log')).read_text()
            self.assertEqual(log.count('Axioms:')+log.count('Closed under the global context'),n)
            self.assertTrue(set(re.findall(r'^([A-Za-z][\w.]*)\s+:',log,re.M))<=allowed)
    def test_single_factor_rejections_preserve_proofs(self):
        proof=(ROOT/PROOF).read_text();controls=json.loads((GATE/'ablations.json').read_text())
        self.assertEqual([c['name'] for c in controls],['wrong-clock-readback','wrong-abstract-current'])
        for c in controls:
            self.assertTrue(c['single_factor']);self.assertTrue(c['expected_rejection_observed']);self.assertFalse(c['downstream_credit'])
            mutant=(GATE/(c['name']+'.v.snapshot.txt')).read_text()
            self.assertNotEqual(mutant,proof)
            self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',mutant,re.S),re.findall(r'Proof\.(.*?)Qed\.',proof,re.S))
            log=(GATE/(c['name']+'.log')).read_text()
            self.assertEqual(int(re.search(r'line (\d+),',log).group(1)),c['exact_connection_line']);self.assertIn('No such assumption',log)
    def test_old_fixed_source_identities(self):
        source=json.loads((GATE/'source/result.json').read_text())
        previous=json.loads((ROOT/'audit/logs/stage35-time-access/protocol.json').read_text())
        self.assertTrue(source['passed']);self.assertFalse(source['verified_frontend']);self.assertFalse(source['port_simulation'])
        self.assertEqual([f['identity'] for f in source['functions']],previous['functions'])
    def test_bounded_credit(self):
        result=json.loads((GATE/'result.json').read_text())
        for k in ['same_extended_invariant_GoodI','owned_store_existence','same_final_memory_clock_readback','abstract_physical_time_preserved','literal_different_tid','live_dead_task_maps','local_invariant_empty_fixture','reused_dependency_products']:self.assertTrue(result[k],k)
        for k in ['setter_refinement','original_port_simulation','full_function_linked','good_os_proved','formal_six_gates_promoted','whole_source_clean_build']:self.assertFalse(result[k],k)
