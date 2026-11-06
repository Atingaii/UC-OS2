"""Raw uninitialized storage, actual allocation and real suffix evidence."""
import hashlib,json,re,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
LOG=ROOT/'audit/logs/stage33-time-tick-storage'
GATE=LOG/'gate01'
PROOF='certiucos/v293/proofs/V293TimeTickStorage.v'
PROBE='audit/probes/V293TimeTickStorageProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TimeTickStorageTests(unittest.TestCase):
    def test_checked_inputs_current(self):
        gate=json.loads((GATE/'result.json').read_text())
        self.assertTrue(gate['passed']);self.assertEqual(gate['source_count'],174)
        self.assertEqual(len(gate['input_sha256']),183)
        for p,h in gate['input_sha256'].items():self.assertEqual(sha(ROOT/p),h,p)
    def test_fixed_function_identity(self):
        protocol=json.loads((LOG/'protocol.json').read_text())
        inventory=json.loads((ROOT/'audit/physical-access-inventory.json').read_text())
        function=next(f['identity'] for f in inventory['functions'] if f['name']=='OSTimeTick')
        self.assertEqual(protocol['function_identity'],function)
        self.assertEqual(sha(ROOT/'csrc/upstream/v2.93.01/checkout/Source/os_core.c'),function['source_file_sha256'])
        self.assertEqual(inventory['source_identity_sha256'],protocol['source_identity_sha256'])
    def test_old_sources_and_project_append_only(self):
        files=json.loads((LOG/'baseline.json').read_text())['files']
        sources=[p for p in files if p.endswith('.v') and p.startswith(('certiucos/v293/','framework/','tactics/'))]
        self.assertEqual(len(sources),173)
        for p in sources:self.assertEqual(sha(ROOT/p),files[p],p)
        project=(ROOT/'_CoqProject').read_bytes();suffix=(PROOF+'\n').encode()
        self.assertEqual(project.count(suffix),1);self.assertTrue(project.endswith(suffix))
        self.assertEqual(hashlib.sha256(project[:-len(suffix)]).hexdigest(),files['_CoqProject'])
    def test_actual_allocation_and_raw_not_typed(self):
        proof=(ROOT/PROOF).read_text();probe=(ROOT/PROBE).read_text()
        allocation=proof.split('Theorem V293_tick_scan_allocation :',1)[1].split('Qed.',1)[0]
        for term in ['allocb M','cstep P','salloc nil','salloclv_step','alloc_empmem_mapstoval','Some Vundef']:
            self.assertIn(term,allocation)
        self.assertIn('rule_type_val_match (Tptr V293_tcb_type) Vundef = false',probe)
        self.assertIn('StorageFresh tick run',probe)
        self.assertIn('V293_tick_scan_allocation',probe)
    def test_real_suffix_no_execution_or_store_oracle(self):
        proof=(ROOT/PROOF).read_text();statement=proof.split('Theorem V293_tick_uninitialized_suffix_execution :',1)[1].split('exists Mf,',1)[0]
        self.assertIn('bc Vundef tasks',statement)
        for forbidden in ['cstep','V293_local_steps','store ','evalval ','Axiom','Admitted']:
            self.assertNotIn(forbidden,statement)
        for term in ['V293_tick_raw_slot_update','V293_tick_while_owned_execution','FinalTime','FinalPointer']:
            self.assertIn(term,proof)
    def test_independent_literal_entries_and_all_branches(self):
        probe=(ROOT/PROBE).read_text()
        for name in ['StorageAllocatedUninitialized','StorageEntrySatisfiable','StorageMixedExecution','StorageRunningOneWrapped','StorageRunningTwoNotTrue','StorageRunningZeroStillTicks']:
            self.assertIn('Theorem '+name,probe)
        self.assertIn('forall tick run enabled, run<256',probe)
        self.assertIn('if Nat.eqb run 1 then Vptr LoopIdle else Vundef',probe)
        self.assertIn('LoopFinalTasks',probe);self.assertIn('LoopFrameCells',probe)
        self.assertNotIn('Theorem OSTimeTickHook',probe)
    def test_actual_commands_and_independent_kernel(self):
        commands=json.loads((GATE/'commands.json').read_text())
        self.assertEqual([c['exit'] for c in commands],[0,0,0,0,0,1,1,0])
        self.assertTrue(all(c['passed'] and c['exit']==c['expected'] for c in commands))
        self.assertEqual(commands[-1]['command'][-2:],['CertiOS.certiucos.v293.proofs.V293TimeTickStorage','CertiOS.audit.probes.V293TimeTickStorageProbe'])
        for name,p in [('production',PROOF),('probe',PROBE)]:
            self.assertEqual((GATE/(name+'.v.snapshot.txt')).read_bytes(),(ROOT/p).read_bytes())
    def check_mutant(self,name,replacement):
        proof=(ROOT/PROOF).read_text();before='load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (if Nat.eqb run 1 then Vptr idle else Vundef) /\\'
        mutant=(GATE/(name+'.v.snapshot.txt')).read_text()
        self.assertEqual(proof.count(before),1);self.assertEqual(mutant,proof.replace(before,replacement))
        self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',proof,re.S),re.findall(r'Proof\.(.*?)Qed\.',mutant,re.S))
        log=(GATE/(name+'.log')).read_text();self.assertIn('FinalPointer',log);self.assertIn('Error:',log)
        self.assertNotIn('Cannot find a physical path',log)
        record=next(c for c in json.loads((GATE/'commands.json').read_text()) if c['name']==name)
        self.assertEqual(record['exit'],1)
    def test_single_factor_active_pointer(self):
        self.check_mutant('wrong-active-pointer','load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (if Nat.eqb run 1 then Vptr (V293_tick_head tasks idle) else Vundef) /\\')
    def test_single_factor_uninitialized_not_null(self):
        self.check_mutant('wrong-inactive-pointer','load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (if Nat.eqb run 1 then Vptr idle else Vnull) /\\')
    def test_assumptions_and_scope_not_promoted(self):
        allowed={'FunctionalExtensionality.functional_extensionality_dep','Classical_Prop.classic'}
        for name,roots in [('production',2),('probe',6)]:
            log=(GATE/(name+'.log')).read_text();self.assertEqual(log.count('Axioms:'),roots)
            self.assertEqual(set(re.findall(r'^([A-Za-z][\w.]*)\s+:',log,re.M)),allowed)
        result=json.loads((GATE/'result.json').read_text())
        for key in ['whole_source_clean_build','full_function_proved','good_os_proved','formal_six_gates_promoted']:self.assertFalse(result[key])
        self.assertIn('OPEN_BOUNDARY_CONTRACT',json.loads((LOG/'protocol.json').read_text())['hook_finding'])
        self.assertFalse(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture)\b',(ROOT/PROOF).read_text()))
if __name__=='__main__':unittest.main()
