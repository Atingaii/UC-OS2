"""Exact fixed-C startup writes, concrete lifecycle and bounded controls."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage41-init-misc';G=L/'gate02'
C='certiucos/v293/code/V293OSInitMisc.v';P='certiucos/v293/proofs/V293InitMisc.v';B='audit/probes/V293InitMiscProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
class InitMiscTests(unittest.TestCase):
    def test_exact_checked_inputs_and_registration(self):
        inputs=read(G/'inputs.json')
        for p in [C,P,B,'audit/logs/stage41-init-misc/protocol.json','audit/logs/stage41-init-misc/source-map.py','audit/logs/stage41-init-misc/run-checks.py']:
            self.assertEqual(sha(R/p),inputs[p],p)
        for p in [C,P]:self.assertEqual((R/'_CoqProject').read_text().splitlines().count(p),1)
        self.assertEqual(read(G/'result.json')['source_count'],183)
    def test_previous_sources_and_frozen_evidence_retained(self):
        old=read(L/'baseline.json')['files']
        sources=[p for p in old if p.endswith('.v') and p.startswith(('certiucos/v293/','framework/','tactics/'))]
        self.assertEqual(len(sources),181)
        for p in sources:self.assertEqual(sha(R/p),old[p],p)
        for stage in ['stage36-time-shared','stage37-time-shared-good','stage38-time-shared-set','stage39-time-set-api','stage40-time-names-good']:
            for p,h in read(R/'audit/logs'/stage/'final-evidence-manifest.json').items():self.assertEqual(sha(R/p),h,p)
    def test_fresh_fixed_c_complete_types_order_constants(self):
        source=read(G/'source/result.json');protocol=read(L/'protocol.json')
        self.assertTrue(source['passed']);self.assertTrue(source['all94_identities_equal'])
        self.assertEqual(source['source_identity'],protocol['source_identity']);self.assertEqual(source['function'],protocol['function'])
        expected=[('OSTime','Tint32'),('OSIntNesting','Tint8'),('OSLockNesting','Tint8'),('OSTaskCtr','Tint8'),('OSRunning','Tint8'),('OSCtxSwCtr','Tint32'),('OSIdleCtr','Tint32'),('OSIdleCtrRun','Tint32'),('OSIdleCtrMax','Tint32'),('OSStatRdy','Tint8')]
        self.assertEqual([(a['name'],a['model_type']) for a in source['mapped_assignments']],expected)
        self.assertEqual([a['source_assignment'] for a in source['mapped_assignments']],protocol['assignments'])
        for a in source['mapped_assignments']:self.assertEqual(a['C_type'],'unsigned char' if a['model_type']=='Tint8' else 'unsigned int')
        self.assertFalse(source['verified_frontend']);self.assertFalse(source['full_OSInit'])
        self.assertTrue(all(c['exit']==0 for c in source['commands']))
    def test_real_raw_writes_and_environment_boundary(self):
        text=(R/P).read_text()
        for term in ['EX old : val, Amapsto','V293_tick_raw_slot_update','sassignend_step','V293_init_sequence_execution','V293_init_readback','V293_init_preserved_frame','Theorem V293_OS_InitMisc_execution','Theorem V293_OS_InitMisc_call_return','snpcall_step','sfexec_step','sallocend_step','sret_step','sfreeend_step']:
            self.assertIn(term,text)
        stmt=text.split('Theorem V293_OS_InitMisc_call_return :',1)[1].split('Proof.',1)[0]
        self.assertIn('(ge,emp,M,ir,aux,O,op)',stmt);self.assertIn('(ge,emp,Mf,ir,aux,O,op)',stmt)
        self.assertIn('(ge,caller,Mf)',stmt);self.assertNotIn('CurLINV',stmt);self.assertNotIn('CurTid',stmt)
        for p in [C,P,B]:self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture)\b')
    def test_literal_nonvacuity_and_same_final_memory(self):
        text=(R/B).read_text();cells=text.split('Definition InitCells',1)[1].split('Lemma InitStar',1)[0]
        self.assertEqual(cells.count('Vundef'),2)
        for term in ['InitLiteralEntry','InitLiteralAST','InitConcreteCall','InitLiteralFinal','InitFullLiteralExecution','Int.repr 123','Int.repr 57','V293_init_preserved_frame']:
            self.assertIn(term,text)
        zero=text.split('Definition InitAllZero M :=',1)[1].split('Theorem InitLiteralFinal',1)[0]
        self.assertEqual(zero.count('load '),10);self.assertEqual(zero.count('Some (Vint32 Int.zero)'),10)
        final=text.split('Theorem InitFullLiteralExecution',1)[1].split('Proof.',1)[0]
        self.assertIn('(InitGE,caller,Mf)',final);self.assertIn('InitAllZero Mf',final)
        self.assertIn('load (Tptr Tvoid) Mf (90%positive,0%Z)=Some Vnull',final)
        self.assertIn('load Tint32 Mf (99%positive,0%Z)=Some (Vint32 (Int.repr 123))',final)
        self.assertNotIn('Require Import CertiOS.audit.probes.',text)
    def test_observed_coqc_coqchk_and_allowed_assumptions(self):
        commands=read(G/'commands.json')
        self.assertEqual([c['exit'] for c in commands],[0,0,0,0,1,0,0,1,0]);self.assertTrue(all(c['passed'] for c in commands))
        self.assertEqual(commands[-1]['command'][0],'/data/home/lucentzhou/.opam/default/bin/coqchk')
        allowed={'FunctionalExtensionality.functional_extensionality_dep','Classical_Prop.classic'}
        for n,roots in [('production',2),('probe',4)]:
            log=(G/(n+'.log')).read_text();self.assertEqual(log.count('Axioms:')+log.count('Closed under the global context'),roots)
            self.assertTrue(set(re.findall(r'^([A-Za-z][\w.]*)\s+:',log,re.M))<=allowed)
    def test_single_factor_mutations_and_rejection_scope(self):
        controls=read(G/'ablations.json');probe=(R/B).read_text();code=(R/C).read_text()
        self.assertEqual([c['name'] for c in controls],['wrong-stat-ready-one','omit-idlemax-assignment'])
        wrong=(G/'wrong-stat-ready-one.v.snapshot.txt').read_text()
        old='load Tint8 M (91%positive,0%Z)=Some (Vint32 Int.zero).';new=old.replace('Int.zero','Int.one')
        self.assertEqual(wrong.replace(new,old),probe)
        self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',wrong,re.S),re.findall(r'Proof\.(.*?)Qed\.',probe,re.S))
        omitted=(G/'omit-idlemax-code.v.snapshot.txt').read_text()
        self.assertEqual(omitted.replace('(stat_ready, Tint8)','(idle_max, Tint32); (stat_ready, Tint8)'),code)
        self.assertEqual((G/'literal-ast-positive.v.snapshot.txt').read_bytes(),(G/'omit-idlemax-assignment.v.snapshot.txt').read_bytes())
        for c in controls:
            self.assertTrue(c['single_factor']);self.assertTrue(c['expected_rejection_observed']);self.assertFalse(c['semantic_execution_credit']);self.assertFalse(c['downstream_credit'])
            log=(G/(c['name']+'.log')).read_text();self.assertEqual(int(re.search(r'line (\d+),',log).group(1)),c['exact_connection_line'])
            for bad in ['Syntax error','Cannot find library','Cannot find a physical path','inconsistent assumptions','was not found']:self.assertNotIn(bad,log)
        self.assertFalse(controls[0]['AST_correspondence_credit']);self.assertTrue(controls[1]['AST_correspondence_credit'])
    def test_bounded_completion_claims(self):
        result=read(G/'result.json')
        for k in ['passed','exact_ten_writes','uninitialized_entry_supported','concrete_body_execution','concrete_call_void_return','same_Mf_frame_retained','no_CurLINV_premise','literal_all10_readbacks','sentinel_preserved','abstract_time_not_silently_initialized']:self.assertTrue(result[k],k)
        for k in ['all_ISR_safety','OSInit_reachability','OSStart_reachability','good_os_proved','same_program_K1_K4','ucos3_started','formal_six_gates_promoted','verified_frontend','whole_source_clean_build']:self.assertFalse(result[k],k)
