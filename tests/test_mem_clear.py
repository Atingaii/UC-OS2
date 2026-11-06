"""Fixed-source byte clearing, raw ownership and explicit representation gap."""
from pathlib import Path
import hashlib,importlib.util,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage43-mem-clear';G=L/'gate02'
C='certiucos/v293/code/V293OSMemClr.v';P='certiucos/v293/proofs/V293MemClr.v';B='audit/probes/V293MemClrProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda p:json.loads(p.read_text())
spec=importlib.util.spec_from_file_location('mem_clear_auditor',R/'scripts/project-audit.py')
AUDITOR=importlib.util.module_from_spec(spec);spec.loader.exec_module(AUDITOR)
class MemClearTests(unittest.TestCase):
    def test_checked_inputs_and_registration(self):
        inputs=read(G/'inputs.json')
        for p in [C,P,B,'audit/logs/stage43-mem-clear/protocol.json','audit/logs/stage43-mem-clear/source-map.py','audit/logs/stage43-mem-clear/run-checks.py']:self.assertEqual(sha(R/p),inputs[p],p)
        for p in [C,P]:self.assertEqual((R/'_CoqProject').read_text().splitlines().count(p),1)
        self.assertEqual(read(G/'result.json')['source_count'],187)
    def test_old_sources_and_frozen_evidence_retained(self):
        old=read(L/'baseline.json')['files'];sources=[p for p in old if p.endswith('.v') and p.startswith(('certiucos/v293/','framework/','tactics/'))]
        self.assertEqual(len(sources),185)
        for p in sources:self.assertEqual(sha(R/p),old[p],p)
        for stage in ['stage36-time-shared','stage37-time-shared-good','stage38-time-shared-set','stage39-time-set-api','stage40-time-names-good','stage41-init-misc','stage42-init-ready']:
            for p,h in read(R/'audit/logs'/stage/'final-evidence-manifest.json').items():self.assertEqual(sha(R/p),h,p)
    def test_fresh_fixed_c_identity_and_exact_body(self):
        source=read(G/'source/result.json');protocol=read(L/'protocol.json')
        self.assertTrue(source['passed']);self.assertTrue(source['all94_identities_equal']);self.assertEqual(source['source_identity'],protocol['source_identity'])
        self.assertEqual(source['function'],protocol['function']);self.assertEqual(source['body'],protocol['expected_body'])
        self.assertEqual([n['kind'] for n in source['clang_body']['inner']],['WhileStmt'])
        for term in ['while (size > 0u)','*pdest++ = (INT8U)0;','size--;']:self.assertIn(term,source['body'])
        self.assertFalse(source['verified_frontend']);self.assertFalse(source['full_OSInit']);self.assertTrue(all(c['exit']==0 for c in source['commands']))
    def test_general_actual_loop_and_zero_length_boundary(self):
        text=(R/P).read_text();code=(R/C).read_text()
        for term in ['swhile','V293_clr_advance','ederef','Tint16']:self.assertIn(term,code)
        for term in ['induction values','V293_rdy_assign','V293_rdy_while_true','V293_rdy_while_false','V293_clr_frame_in','V293_clr_frame_out','V293_OS_MemClr_loop_execution']:self.assertIn(term,text)
        stmt=text.split('Theorem V293_OS_MemClr_loop_execution :',1)[1].split('Proof.',1)[0]
        for term in ['Z.of_nat (length values)<=65535','off+Z.of_nat (length values)<=Int.max_unsigned','repeat (Vint32 Int.zero) (length values)','exists Mf','(ge,le,Mf,ir,aux,O,op)']:self.assertIn(term,stmt)
        self.assertNotIn('store ',stmt);self.assertNotIn('CurLINV',stmt)
        zero=text.split('Theorem V293_OS_MemClr_zero_size :',1)[1].split('Proof.',1)[0]
        self.assertIn('get le size=',zero);self.assertNotIn('get le dest',zero);self.assertNotIn('Tptr',zero)
        for p in [C,P,B]:self.assertIsNone(AUDITOR.FORBIDDEN.search(AUDITOR.coq_code((R/p).read_text())),p)
        self.assertIsNone(AUDITOR.FORBIDDEN.search(AUDITOR.coq_code('(* Parameter (* nested Axiom *) *) Definition x := 0.')))
        for token in ['Admitted','admit','Axiom','Axioms','Parameter','Parameters','Conjecture','Conjectures']:
            self.assertIsNotNone(AUDITOR.FORBIDDEN.search(AUDITOR.coq_code('(* note *) '+token+' bad : False.')),token)
    def test_independent_nonvacuity_readbacks_and_null_counterexample(self):
        text=(R/B).read_text()
        for term in ['ClrLiteralEntry','ClrLiteralAST','ClrConcreteExecution','ClrEmptyDoesNotReadDest','ClrZeroBytesNotNull','Vundef;Vint32 (Int.repr 7)','ClrByte 82%positive','ptomvallist_loadbytes']:self.assertIn(term,text)
        stmt=text.split('Theorem ClrConcreteExecution',1)[1].split('Proof.',1)[0]
        self.assertEqual(stmt.count('load '),7);self.assertIn('(emp,ClrLE,Mf)',stmt)
        ast=text.split('Theorem ClrLiteralAST',1)[1].split('Proof.',1)[0].split('=',1)[1]
        self.assertNotIn('V293_clr_',ast);self.assertIn('swhile',ast)
        mismatch=text.split('Theorem ClrZeroBytesNotNull :',1)[1].split('Proof.',1)[0]
        for term in ['=Vundef','=Vnull','<> encode_val','load (Tptr Tint8)','=Some Vundef']:self.assertIn(term,mismatch)
        self.assertNotIn('Require Import CertiOS.audit.probes.',text)
    def test_observed_kernel_and_root_assumptions(self):
        commands=read(G/'commands.json');self.assertEqual([c['exit'] for c in commands],[0,0,0,0,1,0,0,1,0]);self.assertTrue(all(c['passed'] for c in commands))
        self.assertEqual(commands[-1]['command'][0],'/data/home/lucentzhou/.opam/default/bin/coqchk')
        allowed={'FunctionalExtensionality.functional_extensionality_dep','Classical_Prop.classic'}
        for n,roots in [('production',2),('probe',5)]:
            log=(G/(n+'.log')).read_text();self.assertEqual(log.count('Axioms:')+log.count('Closed under the global context'),roots)
            self.assertTrue(set(re.findall(r'^([A-Za-z][\w.]*)\s+:',log,re.M))<=allowed)
    def test_prospective_single_factor_controls(self):
        controls=read(G/'ablations.json');probe=(R/B).read_text();code=(R/C).read_text()
        self.assertEqual([c['name'] for c in controls],['wrong-last-byte','omit-pointer-advance'])
        wrong=(G/'wrong-last-byte.v.snapshot.txt').read_text();old='load Tint8 M (82%positive,7)=Some (Vint32 Int.zero).';new=old.replace('Int.zero','(Int.repr 7)')
        self.assertEqual(wrong.replace(new,old),probe);self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',wrong,re.S),re.findall(r'Proof\.(.*?)Qed\.',probe,re.S))
        self.assertEqual((G/'omit-pointer-code.v.snapshot.txt').read_text().replace('sskip None','sassign (evar dest) (ebinop oplus (evar dest) (econst32 Int.one))'),code)
        self.assertEqual((G/'literal-ast-positive.v.snapshot.txt').read_bytes(),(G/'omit-pointer-advance.v.snapshot.txt').read_bytes())
        for c in controls:
            self.assertTrue(c['single_factor']);self.assertTrue(c['expected_rejection_observed']);self.assertFalse(c['semantic_execution_credit']);self.assertFalse(c['downstream_credit'])
            log=(G/(c['name']+'.log')).read_text();self.assertEqual(int(re.search(r'line (\d+),',log).group(1)),c['line'])
            for bad in ['Syntax error','Cannot find library','Cannot find a physical path','inconsistent assumptions','was not found']:self.assertNotIn(bad,log)
        self.assertFalse(controls[0]['AST_credit']);self.assertTrue(controls[1]['AST_credit'])
    def test_no_inflated_completion_and_failed_gate_retained(self):
        result=read(G/'result.json')
        for k in ['passed','native_while','all_lengths_through_uint16_max','raw_Vundef_target_allowed','actual_stores_from_ownership','whole_range_zeroed','same_block_guards_retained','zero_length_does_not_load_dest','pointer_advances_to_end','size_decrements_to_zero','arbitrary_same_environment_frame','representation_counterexample_checked','concrete_body_execution']:self.assertTrue(result[k],k)
        for k in ['concrete_call_allocation_free','all_executions_safety','typed_pointer_table_null_linked','OSInit_reachability','OSStart_reachability','good_os_proved','same_program_K1_K4','ucos3_started','formal_six_gates_promoted','verified_frontend','whole_source_clean_build']:self.assertFalse(result[k],k)
        self.assertEqual([c['exit'] for c in read(L/'gate01/commands.json')],[0,0,0,1])
        self.assertIn('Error:',(L/'gate01/probe.log').read_text())
