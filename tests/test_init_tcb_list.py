"""Same-memory OS_InitTCBList body: real clears, native loop and heads."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage47-init-tcb-list'
C='certiucos/v293/code/V293OSInitTCBList.v';P='certiucos/v293/proofs/V293InitTCBList.v';B='audit/probes/V293InitTCBListProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class InitTCBListTests(unittest.TestCase):
    def test_previous_inputs_and_products_preserved(self):
        b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
        for p,h in b['files'].items():
            if p not in allowed:self.assertEqual(sha(R/p),h,p)
        for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
        self.assertEqual(len(b['sources']),191);self.assertEqual(len(b['products']),955)
        current=[p for p in (R/'_CoqProject').read_text().splitlines() if p.endswith('.v')]
        self.assertEqual(current,b['sources']+[C,P]);self.assertEqual(len(current),193)
    def test_actual_clang_body_and_fixed_layout(self):
        x=read(L/'source/result.json');y=read(L/'source-loop.json')
        self.assertTrue(x['passed']);self.assertTrue(x['all94_identities_equal'])
        self.assertEqual(x['source_identity'],'74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da')
        self.assertEqual(x['function']['name'],'OS_InitTCBList');self.assertEqual(x['function']['first_line'],1591)
        self.assertEqual(x['layout'],dict(TCB=56,TCB_array=728,priority_array=52,TCB_next_offset=20))
        self.assertTrue(y['passed']);self.assertEqual(y['input_sha256'],sha(L/'source/result.json'))
        self.assertIn(y['loop']+y['suffix'],re.sub(r'\s+','',x['body']))
        self.assertEqual([y['iterations'],y['TCB_count']],[12,13]);self.assertFalse(y['verified_frontend'])
        self.assertEqual([n['kind'] for n in x['clang_body']['inner']],['DeclStmt']*4+['CallExpr']*2+['ForStmt']+['BinaryOperator']*4)
    def test_native_loop_with_fixed_configuration_proof(self):
        c=(R/C).read_text();s=(R/P).read_text()
        loop=c.split('Definition V293_tcb_link_loop',1)[1].split('Definition',1)[0]
        self.assertIn('swhile (V293_tcb_link_guard ix)',loop);self.assertNotIn('seq 0',loop)
        self.assertEqual(s.count('eapply V293_rdy_while_true;'),12)
        self.assertEqual(s.count('apply V293_rdy_while_false;'),1)
        for token in ['Tcom_ptr 410','(seq 0 12)','((bt,692),Tcom_ptr 410,Vnull)','Vint32 (Int.repr 12)','(Vptr (bt,Int.repr 672))']:self.assertIn(token,s)
    def test_real_clear_return_feeds_loop_and_writable_post(self):
        s=(R/P).read_text();body=s.split('Theorem V293_OS_InitTCBList_body_execution :',1)[1].split('Qed.',1)[0];stmt=body.split('Proof.',1)[0]
        for token in ['length oldtcbs=728%nat','length oldprios=52%nat','exists Mf','cstepstar P','V293_init_tcb_body','V293_tcb_link_final','V293_tcb_untouched_cells bt 0 13','V293_null_pointer_cells bp 0 13','V293_rdy_raw_cells frame Atrue']:self.assertIn(token,stmt)
        for forbidden in ['store ', 'free ', 'MemoryNotFull','Axiom','Admitted','Parameter','Conjecture']:self.assertNotIn(forbidden,stmt)
        for token in ['V293_OS_InitTCBList_clear_calls','as (M1&Clear&Cleared)','V293_tcb_prepare_cleared','P ge le M1','Cleared) as (Mf&Links&Final)','exact Clear','apply Links']:self.assertIn(token,body)
        for token in ['(repeat (Vint32 Int.zero) 20)','(repeat (Vint32 Int.zero) 32)','(off+24)','V293_zero4_comptr_null_owned','V293_zero_tcb_next_cells']:self.assertIn(token,s)
        self.assertEqual(13*(20+32),676)
    def test_independent_finite_entry_and_same_memory_readbacks(self):
        s=(R/B).read_text();stmt=s.split('Theorem LinkConcreteExecution :',1)[1].split('Proof.',1)[0]
        self.assertNotIn('Require Import CertiOS.audit.probes.',s)
        for token in ['LinkLiteralEntry','LinkProgramLookup','LinkEnvironment','LinkLiteralAST','repeat Undef 728','Byte.repr 255','Theorem LinkMiddleAndEnds']:self.assertIn(token,s)
        self.assertEqual(stmt.count('load '),9)
        for token in ['(i<12)%nat','(p<13)%nat','(82%positive,692)','(95%positive,0)','(99%positive,0)']:self.assertIn(token,stmt)
        # 9 predicates, two range over 12 and 13 slots respectively.
        self.assertEqual(9-2+12+13,32)
        self.assertEqual(read(L/'probe05.json')['exit'],0)
        log=(L/'probe05.log').read_text();self.assertEqual(log.count('Axioms:')+log.count('Closed under the global context'),4)
        self.assertEqual(sha(R/B),sha(L/'probe05.v.snapshot.txt'))
    def test_prospective_single_claim_controls(self):
        plan=read(L/'control-plan.json');rows=read(L/'control-results.json');s=(R/B).read_text()
        self.assertTrue(plan['frozen_before_execution']);self.assertEqual(plan['positive_sha256'],sha(R/B))
        self.assertIn('not mechanism ablations',plan['scope']);self.assertEqual(len(rows),5)
        self.assertEqual(rows[0]['exit'],0)
        for row in rows:
            self.assertTrue(row['expected_result_observed']);self.assertTrue(row['single_factor']);self.assertTrue(row['proofs_unchanged']);self.assertFalse(row['all_execution_safety_credit'])
            snap=(L/(row['name']+'.v.snapshot.txt')).read_text()
            self.assertEqual(sha(L/(row['name']+'.v.snapshot.txt')),row['source_sha256'])
            self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',snap,re.S),re.findall(r'Proof\.(.*?)Qed\.',s,re.S))
            if row['name']!='positive':
                c=next(c for c in plan['controls'] if c['name']==row['name']);start=s.index('Theorem LinkMiddleAndEnds :')
                self.assertEqual(snap,s[:start]+s[start:].replace(c['old'],c['new'],1))
                self.assertEqual(row['actual_error_lines'],[c['expected_error_line']])
    def test_build_and_kernel_trust(self):
        x=read(L/'build.json');self.assertEqual(x['exit'],0);self.assertEqual(x['active_sources'],193)
        self.assertEqual(x['old_products_reused'],955);self.assertFalse(x['source_only_cold_build'])
        x=read(L/'trust.json');self.assertTrue(x['passed']);self.assertEqual(x['roots_printed'],54)
        self.assertEqual(len(x['roots']),54);self.assertEqual([c['exit'] for c in x['commands']],[0,0])
        self.assertTrue(x['assumptions_allowed']);self.assertNotIn('MemoryNotFull',str(x['assumptions']))
        for token in ['toptheorem','V293OSInitTCBList','V293InitTCBList','V293InitTCBListProbe']:self.assertIn(token,str(x['commands'][-1]['command']))
    def test_adversarial_limits_and_goal(self):
        rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),10)
        for row in rows:self.assertTrue(row['resolution']);self.assertIn(row['kind'],['test','bounded claim','limitation'])
        x=read(L/'proof-report.json')
        for key in ['old_sources_unchanged','old_tests_unchanged','old_evidence_unchanged','old_C_unchanged','full_TCB_list','full_priority_table','returned_writable_ownership','real_array_arguments','second_call_actual_first_memory','real_clear_return_to_native_loop']:self.assertTrue(x[key],key)
        for key in ['OS_InitTCBList_full_function','OSInit_reachability','OSStart_reachability','all_execution_safety','GOOD_OS','same_program_K1_K4','ucos3_started','six_gates_promoted','git_commit_or_push']:self.assertFalse(x[key],key)
        self.assertEqual(x['goal_status'],'active');self.assertEqual(x['formal_six_gates'],[94,1,1,1,1,0])
