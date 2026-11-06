"""Fixed OS_InitTCBList two-call prefix, whole-table ownership and finite replay."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage46-init-tcb-clear'
C='certiucos/v293/code/V293OSInitTCBClear.v';P='certiucos/v293/proofs/V293InitTCBClear.v';B='audit/probes/V293InitTCBClearProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class InitTCBClearTests(unittest.TestCase):
    def test_previous_sources_c_tests_and_evidence_are_unchanged(self):
        base=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
        for p,h in base['files'].items():
            if p not in allowed:self.assertEqual(sha(R/p),h,p)
        self.assertEqual(len(base['sources']),189)
        current=[p for p in (R/'_CoqProject').read_text().splitlines() if p.endswith('.v')]
        self.assertEqual(current,base['sources']+[C,P]);self.assertEqual(len(current),191)
    def test_clang_checks_exact_fixed_function_and_all_four_layouts(self):
        x=read(L/'source03/result.json');self.assertTrue(x['passed']);self.assertTrue(x['all94_identities_equal'])
        self.assertEqual(x['source_identity'],'74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da')
        self.assertEqual(x['function']['name'],'OS_InitTCBList');self.assertEqual(x['function']['first_line'],1591)
        self.assertEqual(x['layout'],dict(TCB=56,TCB_array=728,priority_array=52,TCB_next_offset=20))
        self.assertEqual(x['commands'][-1]['exit'],0);self.assertEqual(x['commands'][-1]['command'][0],'clang')
        self.assertFalse(x['verified_frontend']);self.assertFalse(x['full_OSInit'])
        body=re.sub(r'\s+','',x['body'])
        for call in ['OS_MemClr((INT8U*)&OSTCBTbl[0],sizeof(OSTCBTbl));','OS_MemClr((INT8U*)&OSTCBPrioTbl[0],sizeof(OSTCBPrioTbl));']:self.assertIn(call,body)
    def test_stable_postcondition_is_whole_table_owned_not_only_loads(self):
        s=(R/P).read_text();stmt=s.split('Theorem V293_OS_InitTCBList_cleared_tables :',1)[1].split('Proof.',1)[0]
        for token in ['length oldtcbs=728%nat','length oldprios=52%nat','exists Mf','cstepstar P','V293_rdy_raw_cells','V293_null_pointer_cells bp 0 13++frame','(forall p, (p<13)%nat','load (Tptr V293_tcb_type) Mf']:self.assertIn(token,stmt)
        for forbidden in ['store ', 'free ', 'MemoryNotFull','Axiom','Admitted','Parameter','Conjecture']:self.assertNotIn(forbidden,stmt)
        for token in ['V293_raw_cells_return_frame','V293_raw_cells_permutation','V293_OS_MemClr_call_return','V293_zero4_null_owned','V293_init_clear_arguments']:self.assertIn(token,s)
    def test_second_parameters_are_constructed_fresh_in_actual_first_return(self):
        s=(R/P).read_text();body=s.split('Theorem V293_OS_InitTCBList_clear_calls :',1)[1].split('Qed.',1)[0]
        for token in ['V293_fresh_parameters_away M cells','V293_fresh_parameters_away M1 cells','as (M1&First&AfterFirst','P ks ge le M1','as (Mf&Second&Final']:self.assertIn(token,body)
        self.assertEqual(body.count('V293_MemClr_call_owned'),2)
        self.assertIn('memory_is_bounded M',s);self.assertIn('Maps.sub',s)
    def test_independent_nonempty_fixture_checks_same_final_memory(self):
        s=(R/B).read_text();stmt=s.split('Theorem InitConcreteExecution :',1)[1].split('Proof.',1)[0]
        self.assertNotIn('Require Import CertiOS.audit.probes.',s)
        for token in ['InitLiteralEntry','InitProgramLookup','InitLiteralAST','repeat Undef 728','Byte.repr 255','728 true','52 true']:self.assertIn(token,s)
        self.assertIn('V293_wstate InitGE emp Mf |= V293_rdy_raw_cells',stmt)
        self.assertEqual(stmt.count('load '),6)
        for token in ['(p<13)%nat','(82%positive,727)','(82%positive,728)','(84%positive,52)','(99%positive,0)']:self.assertIn(token,stmt)
        self.assertEqual(read(L/'probe07.json')['exit'],0)
        log=(L/'probe07.log').read_text();self.assertEqual(log.count('Axioms:')+log.count('Closed under the global context'),4)
    def test_actual_build_and_kernel_recheck(self):
        x=read(L/'build.json');self.assertEqual(x['exit'],0);self.assertEqual(x['active_sources'],191)
        self.assertEqual(x['old_products_reused'],945);self.assertFalse(x['source_only_cold_build'])
        x=read(L/'trust.json');self.assertTrue(x['passed']);self.assertEqual(x['roots_printed'],len(x['roots']))
        self.assertEqual([c['exit'] for c in x['commands']],[0,0]);self.assertTrue(x['assumptions_allowed']);self.assertFalse(x['kernel_GOOD_OS'])
        for token in ['toptheorem','V293OSInitTCBClear','V293InitTCBClear','V293InitTCBClearProbe']:self.assertIn(token,str(x['commands'][-1]['command']))
        self.assertNotIn('MemoryNotFull',str(x['assumptions']))
    def test_prospective_single_factor_final_connection_controls(self):
        plan=read(L/'control-plan.json');rows=read(L/'control-results.json');s=(R/B).read_text()
        self.assertTrue(plan['frozen_before_execution']);self.assertEqual(plan['positive_sha256'],sha(R/B))
        self.assertEqual([r['name'] for r in rows],['positive','tcb-first-byte-not-cleared','priority-slots-not-null','frame-value-corrupted'])
        self.assertIn('not mechanism ablations',plan['scope'])
        for row in rows:
            self.assertTrue(row['expected_result_observed']);self.assertTrue(row['single_factor']);self.assertTrue(row['proofs_unchanged']);self.assertFalse(row['all_execution_safety_credit'])
            snap=(L/(row['name']+'.v.snapshot.txt')).read_text()
            self.assertEqual(sha(L/(row['name']+'.v.snapshot.txt')),row['source_sha256'])
            self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',snap,re.S),re.findall(r'Proof\.(.*?)Qed\.',s,re.S))
            if row['name']!='positive':
                control=next(c for c in plan['controls'] if c['name']==row['name']);self.assertEqual(snap,s.replace(control['old'],control['new'],1));self.assertEqual(row['actual_error_lines'],[row['expected_error_line']])
        byteplan=read(L/'byte-control02-plan.json');byterows=read(L/'byte-control02-results.json')
        self.assertTrue(byteplan['frozen_before_execution']);self.assertEqual(len(byterows),2)
        self.assertTrue(all(row['expected_result_observed'] for row in byterows))
        self.assertEqual(byterows[0]['exit'],0);self.assertEqual(byterows[1]['actual_error_lines'],[byteplan['expected_error_line']])
        pos=(L/'priority-byte02-positive.v.snapshot.txt').read_text();neg=(L/'priority-byte02-not-cleared.v.snapshot.txt').read_text()
        self.assertEqual(sha(L/'priority-byte02-positive.v.snapshot.txt'),byteplan['positive_sha256'])
        self.assertEqual(neg,pos.replace(byteplan['old'],byteplan['new'],1))
        self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',pos,re.S),re.findall(r'Proof\.(.*?)Qed\.',neg,re.S))
    def test_adversarial_boundaries_are_explicit(self):
        rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),10)
        for row in rows:self.assertTrue(row['resolution']);self.assertIn(row['kind'],['test','bounded claim','limitation'])
        x=read(L/'proof-report.json')
        for key in ['old_sources_unchanged','old_tests_unchanged','old_evidence_unchanged','old_C_unchanged','full_priority_table','returned_writable_ownership','real_array_arguments','second_call_actual_first_memory']:self.assertTrue(x[key],key)
        for key in ['full_TCB_list','OS_InitTCBList_full_function','OSInit_reachability','OSStart_reachability','all_execution_safety','GOOD_OS','same_program_K1_K4','ucos3_started','six_gates_promoted','git_commit_or_push']:self.assertFalse(x[key],key)
        self.assertEqual(x['goal_status'],'active')
