"""Unique null representation, unchanged old contracts, and actual byte-clear connection."""
from pathlib import Path
import hashlib,importlib.util,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage44-null-bytes'
P='certiucos/v293/proofs/V293NullBytes.v';B='audit/probes/V293NullBytesProbe.v'
read=lambda p:json.loads(p.read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class NullBytesTests(unittest.TestCase):
    def test_full_original_source_only_rebuild_and_exact_inputs(self):
        x=read(L/'cold-build03.json')
        self.assertEqual(x['exit'],0);self.assertEqual(x['source_count'],187)
        self.assertEqual(x['initial_products'],0);self.assertTrue(x['inputs_unchanged'])
        self.assertEqual(x['compiled_source_count'],187)
        for p,h in read(L/'cold-build03-inputs.json').items():self.assertEqual(sha(R/p),h,p)
        self.assertEqual((R/'_CoqProject').read_text().splitlines().count(P),1)
        self.assertEqual(read(L/'final-report.json')['current_active_sources'],188)
    def test_old_contracts_retained_without_weakening(self):
        rows=read(L/'old-contracts.json');self.assertEqual(len(rows),5)
        self.assertEqual(sum(x['theorems'] for x in rows),436)
        for row in rows:self.assertTrue(row['unchanged']);self.assertEqual(sha(R/row['path']),row['current_sha256'])
        old=read(L/'baseline.json')['sources'];changed={p for p,h in old.items() if sha(R/p)!=h}
        self.assertEqual(changed,{x['path'] for x in rows})
        complete=read(L/'old-contracts-complete.json')
        self.assertTrue(complete['all_unchanged']);self.assertEqual(complete['total'],526)
        self.assertTrue(complete['earlier_scope_was_incomplete'])
        spec=importlib.util.spec_from_file_location('null_scope_audit',R/'scripts/project-audit.py')
        audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
        header=r"(?m)^[ \t]*(?:Lemma|Theorem|Corollary)\s+([\w']+)(?=\s|:|\()"
        pattern=header+r"(.*?)\bProof(?:\s+with\s+[^.]*|\s+using\s+[^.]*|\s*)\."
        def declarations(raw):
            code=audit.coq_code(raw);matches=list(re.finditer(pattern,code,re.S))
            self.assertEqual([m[1] for m in matches],re.findall(header,code))
            return [(m[1],raw[m.start():m.end(2)]) for m in matches]
        fixture="(* Lemma ignored : False. Proof. *)\n  Lemma retained' : True. Proof. exact I. Qed.\n"
        self.assertEqual([x[0] for x in declarations(fixture)],["retained'"])
        for row in complete['rows']:
            a=declarations((R/row['before_snapshot']).read_text())
            b=declarations((R/row['path']).read_text())
            self.assertEqual(a,b);self.assertEqual(len(a),row['theorems'])
            self.assertTrue(row['complete_header_coverage'])
    def test_same_memory_native_execution_and_constructive_ownership(self):
        text=(R/P).read_text();probe=(R/B).read_text()
        stmt=text.split('Theorem V293_OS_MemClr_null_cell :',1)[1].split('Proof.',1)[0]
        for term in ['length values=4%nat','exists Mf','cstepstar','Amapsto (b,off) (Tptr tp) true Vnull','load (Tptr tp) Mf']:self.assertIn(term,stmt)
        for term in ['store ', 'MemoryNotFull', 'Admitted','Axiom','Parameter']:self.assertNotIn(term,stmt)
        for term in ['V293_OS_MemClr_loop_execution','V293_zero4_null_owned','ptomvallist','V293_raw_cells_separate']:self.assertIn(term,text)
        statement=probe.split('Theorem NullConcreteExecution :',1)[1].split('Proof.',1)[0]
        self.assertEqual(statement.count('load '),6)
        self.assertIn('NullState Mf |= NullOwned',statement)
        self.assertNotIn('Require Import CertiOS.audit.probes.',probe)
        for term in ['NullLiteralEntry','NullLiteralAST','Vundef;Vint32 (Int.repr 7)','NullByte 82%positive']:self.assertIn(term,probe)
        for n,count in [('production-final',2),('probe-final',12)]:
            log=(L/(n+'.log')).read_text();self.assertEqual(read(L/(n+'.json'))['exit'],0)
            self.assertEqual(log.count('Axioms:')+log.count('Closed under the global context'),count)
    def test_real_framework_and_target_kernel_check(self):
        x=read(L/'active-trust.json');self.assertTrue(x['passed']);self.assertEqual(x['roots_printed'],48)
        self.assertEqual([c['exit'] for c in x['commands']],[0,0]);self.assertTrue(x['assumptions_allowed'])
        self.assertNotIn('MemoryNotFull',str(x['assumptions']));self.assertFalse(x['kernel_GOOD_OS'])
        for name in ['toptheorem','V293NullBytes','V293NullBytesProbe']:self.assertIn(name,str(x['commands'][-1]['command']))
    def test_single_factor_codec_controls_and_boundary_results(self):
        rows=read(L/'codec-control-results03.json')
        self.assertEqual([x['name'] for x in rows],['positive','decoder-only','encoder-only','nonzero-as-null','legacy-alias'])
        self.assertEqual(len({x['probe_sha256'] for x in rows}),1)
        self.assertEqual(rows[0]['source_sha256'],sha(R/'framework/model/memory.v'))
        for row in rows:
            self.assertTrue(row['expected_result_observed']);self.assertTrue(row['single_factor'])
            self.assertFalse(row['semantic_execution_credit']);self.assertFalse(row['soundness_credit'])
            if row['name']!='positive':
                log=(L/('codec03-'+row['name']+'-Probe.log')).read_text()
                for bad in ['Syntax error','Cannot find library','inconsistent assumptions','was not found']:self.assertNotIn(bad,log)
        text=(R/B).read_text()
        for term in ['WrongLengthsRejected','UndefNotNull','NonzeroRejected','LegacyNullRejected','AllNullTypes','IntegerZeroUnchanged']:self.assertIn(term,text)
    def test_independent_wrong_readback_is_rejected(self):
        x=read(L/'execution-control.json');self.assertTrue(x['expected_rejection_observed']);self.assertTrue(x['proofs_unchanged'])
        self.assertEqual(x['positive_sha256'],sha(R/B));self.assertFalse(x['all_executions_safety_credit'])
        wrong=(L/'wrong-null-readback.v.snapshot.txt').read_text();good=(R/B).read_text()
        self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',wrong,re.S),re.findall(r'Proof\.(.*?)Qed\.',good,re.S))
    def test_refuted_dual_encoding_and_old_epoch_evidence_retained(self):
        self.assertEqual(read(L/'dual-encoding-counterexample.json')['exit'],0)
        self.assertIn('Closed under the global context',(L/'dual-encoding-counterexample.log').read_text())
        self.assertEqual(read(L/'build05.json')['exit'],2)
        self.assertIn('V293TaskRecordOwnership.v',(L/'build05.log').read_text())
        x=read(L/'old-probe-new-model.json');self.assertTrue(x['expected_rejection_observed'])
        self.assertEqual(x['source_sha256'],sha(R/'audit/probes/V293MemClrProbe.v'))
        archive=read(L/'before-products.json');self.assertEqual(len(archive['products']),935)
        self.assertEqual(sha(L/'before-products.tar.gz'),archive['archive_sha256'])
    def test_no_inflated_completion_and_old_failures_not_hidden(self):
        x=read(L/'final-report.json')
        for k in ['unique_zero_null_encoding','typed_null_cell_from_actual_clear','old_c_unchanged','old_evidence_files_unchanged']:self.assertTrue(x[k],k)
        for k in ['full_pointer_table_linked','full_TCB_list_linked','OSInit_reachability','OSStart_reachability','good_os_proved','same_program_K1_K4','ucos3_started','formal_six_gates_promoted','git_commit_or_push_performed']:self.assertFalse(x[k],k)
        self.assertEqual(read(L/'baseline-all-tests.json')['tests'],1138)
        d=read(L/'test-delta.json');self.assertEqual(d['old_failure_ids'],377);self.assertEqual(d['old_failure_ids_retained'],377)
        self.assertEqual(d['new_test_failures'],0)
        self.assertEqual([r['exit'] for r in read(L/'after-promotion.json')],[0,0,2,0])
