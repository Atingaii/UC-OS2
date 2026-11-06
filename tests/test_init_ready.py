"""Concrete pre-start loop, one-byte lifecycle and strictly bounded evidence."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage42-init-ready';G=L/'gate01'
C='certiucos/v293/code/V293OSInitRdyList.v';P='certiucos/v293/proofs/V293InitRdyList.v';B='audit/probes/V293InitRdyListProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
class InitReadyTests(unittest.TestCase):
    def test_checked_inputs_and_registration(self):
        inputs=read(G/'inputs.json')
        for p in [C,P,B,'audit/logs/stage42-init-ready/protocol.json','audit/logs/stage42-init-ready/source-map.py','audit/logs/stage42-init-ready/run-checks.py']:self.assertEqual(sha(R/p),inputs[p],p)
        for p in [C,P]:self.assertEqual((R/'_CoqProject').read_text().splitlines().count(p),1)
        self.assertEqual(read(G/'result.json')['source_count'],185)
    def test_old_sources_and_frozen_evidence_retained(self):
        old=read(L/'baseline.json')['files'];sources=[p for p in old if p.endswith('.v') and p.startswith(('certiucos/v293/','framework/','tactics/'))]
        self.assertEqual(len(sources),183)
        for p in sources:self.assertEqual(sha(R/p),old[p],p)
        for stage in ['stage36-time-shared','stage37-time-shared-good','stage38-time-shared-set','stage39-time-set-api','stage40-time-names-good','stage41-init-misc']:
            for p,h in read(R/'audit/logs'/stage/'final-evidence-manifest.json').items():self.assertEqual(sha(R/p),h,p)
    def test_fresh_fixed_c_identity_and_exact_body(self):
        source=read(G/'source/result.json');protocol=read(L/'protocol.json')
        self.assertTrue(source['passed']);self.assertTrue(source['all94_identities_equal']);self.assertEqual(source['source_identity'],protocol['source_identity'])
        self.assertEqual(source['function'],protocol['function']);self.assertEqual(source['body'],protocol['expected_body'])
        self.assertEqual([n['kind'] for n in source['clang_body']['inner']],['DeclStmt','BinaryOperator','ForStmt','BinaryOperator','BinaryOperator','BinaryOperator','BinaryOperator'])
        for term in ['INT8U i;','i < ((12u) / 8u + 1u)','OSRdyTbl[i] = 0u;','OSTCBHighRdy = (OS_TCB *)0;','OSTCBCur = (OS_TCB *)0;']:self.assertIn(term,source['body'])
        self.assertFalse(source['verified_frontend']);self.assertFalse(source['full_OSInit']);self.assertTrue(all(c['exit']==0 for c in source['commands']))
    def test_real_loop_store_and_one_byte_lifecycle(self):
        text=(R/P).read_text();code=(R/C).read_text()
        for term in ['swhile','V293_rdy_increment','dcons i Tint8 dnil']:self.assertIn(term,code)
        for term in ['V293_tick_raw_slot_update','sassignend_step','addrval_to_addr','V293_rdy_while_true','V293_rdy_while_false','V293_OS_InitRdyList_execution','V293_OS_InitRdyList_call_return','V293_tick_allocate_frame','V293_tick_void_return','salloclv_step','snpcall_step','sfexec_step']:self.assertIn(term,text)
        stmt=text.split('Theorem V293_OS_InitRdyList_call_return :',1)[1].split('Proof.',1)[0]
        for term in ['fresh M bi','V293_rdy_globals','get Mf (bi,0%Z)=None','get Mf (b,off)=get Ms (b,off)','(ge,caller,Mf)']:self.assertIn(term,stmt)
        self.assertNotIn('CurTid',stmt);self.assertNotIn('CurLINV',stmt)
        for p in [C,P,B]:self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture)\b')
    def test_nonvacuity_independent_literal_and_final_readbacks(self):
        text=(R/B).read_text();cells=text.split('Definition RdyCells',1)[1].split('Ltac RdyApart',1)[0]
        self.assertEqual(cells.count('Vundef'),1);self.assertEqual(cells.count('Vptr'),2)
        for term in ['RdyFresh','RdyEnvironment','RdyLiteralEntry','RdyLiteralAST','RdyLiteralFinal','RdyConcreteCall','RdyFullLiteralExecution','V293_loadbytes_ext']:self.assertIn(term,text)
        stmt=text.split('Theorem RdyFullLiteralExecution',1)[1].split('Proof.',1)[0]
        self.assertEqual(stmt.count('load '),8);self.assertEqual(stmt.count('Some Vnull'),2)
        self.assertIn('(RdyGE,caller,Mf)',stmt);self.assertIn('get Mf (87%positive,0%Z)=None',stmt)
        ast=text.split('Theorem RdyLiteralAST',1)[1].split('Proof.',1)[0].split('=',1)[1]
        self.assertNotIn('V293_rdy_',ast);self.assertIn('swhile',ast);self.assertIn('Int.repr 2',ast)
        self.assertNotIn('Require Import CertiOS.audit.probes.',text)
    def test_observed_kernel_and_root_assumptions(self):
        commands=read(G/'commands.json');self.assertEqual([c['exit'] for c in commands],[0,0,0,0,1,0,0,1,0]);self.assertTrue(all(c['passed'] for c in commands))
        self.assertEqual(commands[-1]['command'][0],'/data/home/lucentzhou/.opam/default/bin/coqchk')
        allowed={'FunctionalExtensionality.functional_extensionality_dep','Classical_Prop.classic'}
        for n,roots in [('production',2),('probe',4)]:
            log=(G/(n+'.log')).read_text();self.assertEqual(log.count('Axioms:')+log.count('Closed under the global context'),roots)
            self.assertTrue(set(re.findall(r'^([A-Za-z][\w.]*)\s+:',log,re.M))<=allowed)
    def test_prospective_single_factor_controls(self):
        controls=read(G/'ablations.json');probe=(R/B).read_text();code=(R/C).read_text()
        self.assertEqual([c['name'] for c in controls],['wrong-current-nonnull','loop-bound-one'])
        wrong=(G/'wrong-current-nonnull.v.snapshot.txt').read_text();old='load (Tptr V293_tcb_type) M (86%positive,0%Z)=Some Vnull.';new=old.replace('Some Vnull','Some (Vptr (92%positive,Int.zero))')
        self.assertEqual(wrong.replace(new,old),probe);self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',wrong,re.S),re.findall(r'Proof\.(.*?)Qed\.',probe,re.S))
        self.assertEqual((G/'loop-bound-code.v.snapshot.txt').read_text().replace('(Int.repr 1)','(Int.repr 2)'),code)
        self.assertEqual((G/'literal-ast-positive.v.snapshot.txt').read_bytes(),(G/'loop-bound-one.v.snapshot.txt').read_bytes())
        for c in controls:
            self.assertTrue(c['single_factor']);self.assertTrue(c['expected_rejection_observed']);self.assertFalse(c['semantic_execution_credit']);self.assertFalse(c['downstream_credit'])
            log=(G/(c['name']+'.log')).read_text();self.assertEqual(int(re.search(r'line (\d+),',log).group(1)),c['exact_connection_line'])
            for bad in ['Syntax error','Cannot find library','Cannot find a physical path','inconsistent assumptions','was not found']:self.assertNotIn(bad,log)
        self.assertFalse(controls[0]['AST_correspondence_credit']);self.assertTrue(controls[1]['AST_correspondence_credit'])
    def test_no_inflated_completion(self):
        result=read(G/'result.json')
        for k in ['passed','native_two_iteration_loop','raw_uninitialized_entry','store_success_from_ownership','concrete_body_execution','concrete_call_local_allocation_void_return','local_byte_freed','frame_retained_at_body_exit','pointwise_outside_local_retained_after_free','literal_all7_global_readbacks_after_return','literal_sentinel_after_return','prestart_current_null','no_CurLINV_premise']:self.assertTrue(result[k],k)
        for k in ['arbitrary_R_transported_to_caller','all_ISR_safety','OSInit_reachability','OSStart_reachability','good_os_proved','same_program_K1_K4','ucos3_started','formal_six_gates_promoted','verified_frontend','whole_source_clean_build']:self.assertFalse(result[k],k)
