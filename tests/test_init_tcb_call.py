"""Whole OS_InitTCBList call: actual allocation, body, release and caller ownership."""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage48-init-tcb-call'
C='certiucos/v293/code/V293OSInitTCBCall.v';P='certiucos/v293/proofs/V293InitTCBCall.v';B='audit/probes/V293InitTCBCallProbe.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class InitTCBCallTests(unittest.TestCase):
    def test_previous_inputs_and_products_preserved(self):
        b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
        for p,h in b['files'].items():
            if p not in allowed:self.assertEqual(sha(R/p),h,p)
        for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
        self.assertEqual(len(b['sources']),193);self.assertEqual(len(b['products']),965)
        active=[p for p in (R/'_CoqProject').read_text().splitlines() if p.endswith('.v')]
        self.assertEqual(active,b['sources']+[C,P]);self.assertEqual(len(active),195)
    def test_source_declarations_and_manual_void_return(self):
        x=read(L/'source/result.json');y=read(L/'source-call.json')
        self.assertTrue(x['passed']);self.assertTrue(x['all94_identities_equal']);self.assertTrue(y['passed'])
        self.assertEqual(x['source_identity'],'74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da')
        self.assertEqual(y['input_sha256'],sha(L/'source/result.json'))
        self.assertEqual(y['declarations'],[['ix','INT8U'],['ix_next','INT8U'],['ptcb1','OS_TCB *'],['ptcb2','OS_TCB *']])
        self.assertEqual(y['call_local_bytes'],[1,1,4,4]);self.assertFalse(y['verified_frontend'])
        self.assertTrue(y['C_fallthrough_void']);self.assertTrue(y['explicit_semantic_void_return'])
        self.assertIn('sret)',(R/C).read_text())
    def test_entry_no_preallocated_locals_or_return_oracle(self):
        s=(R/P).read_text();stmt=s.split('Theorem V293_OS_InitTCBList_call_return :',1)[1].split('Proof.',1)[0];pre=stmt.split('  exists Ms Mf,')[0]
        self.assertIn('(ge,caller,M,ir,aux,O,op)',pre)
        for token in ['fresh M bi','fresh M bn','fresh M b1','fresh M b2','NoDup (V293_tcb_call_blocks','ix<ix_next','V293_tcb_call_heads bl bf vl vf++frame']:self.assertIn(token,pre)
        for token in ['V293_tcb_link_locals','V293_tcb_link_final','free ', 'store ', 'MemoryNotFull']:self.assertNotIn(token,pre)
        self.assertIn('~In (fst a) (V293_tcb_call_blocks',pre)
        for token in ['Axiom','Admitted','Parameter','Conjecture']:self.assertNotIn(token,s)
    def test_real_allocate_body_free_and_caller_ownership(self):
        s=(R/P).read_text();body=s.split('Theorem V293_OS_InitTCBList_call_return :',1)[1]
        self.assertEqual(body.count('eapply salloclv_step;'),4);self.assertEqual(body.count('V293_tick_allocate_frame ge le'),4)
        for token in ['fresh M1 bn','fresh M2 b1','fresh M3 b2','ge le M4 ir aux','as (Ms&Exec&Final)','V293_tick_void_return','exact Return','V293_raw_cells_return_many','(ge,caller,Mf,ir,aux,O,op)','get Mf (c,Z.of_nat k)=None']:self.assertIn(token,body)
        helper=s.split('Lemma V293_raw_cells_return_many :',1)[1].split('Qed.',1)[0]
        for token in ['Maps.sub mp Mf','V293_raw_cells_absent_block','V293_raw_cells_environment','left;reflexivity']:self.assertIn(token,helper)
        self.assertEqual(read(L/'proof22.json')['exit'],0);self.assertEqual(sha(R/P),sha(L/'proof22.v.snapshot.txt'))
    def test_independent_shadowed_caller_and_same_memory(self):
        s=(R/B).read_text();stmt=s.split('Theorem LinkConcreteExecution :',1)[1].split('Proof.',1)[0]
        self.assertNotIn('Require Import CertiOS.audit.probes.',s)
        locals_=s.split('Definition LinkLocals :',1)[1].split('Definition LinkFrame :',1)[0]
        for b in [90,91,92,93]:self.assertNotIn(f'{b}%positive',locals_)
        self.assertIn('set emp 41%Z (110%positive,Tint32)',s)
        for token in ['LinkAbsentLocals','LinkLiteralEntry','LinkLiteralAST','LinkAway','evalval (evar 41%Z)','get Mf (b,Z.of_nat k)=None','load Tint8 Ms (90%positive,0)']:self.assertIn(token,s)
        self.assertEqual(stmt.count('load '),11) # 10 Mf predicates = 33 loads, plus one pre-free Ms counter
        self.assertEqual(10-2+12+13,33)
        x=read(L/'proof-report.json');self.assertEqual(read(L/x['probe_result'])['exit'],0)
        self.assertEqual(sha(R/B),sha(L/x['probe_snapshot']))
    def test_prospective_named_final_connection_controls(self):
        plan=read(L/'control-plan.json');rows=read(L/'control-results.json');s=(R/B).read_text()
        self.assertTrue(plan['frozen_before_execution']);self.assertEqual(plan['positive_sha256'],sha(R/B))
        self.assertIn('not mechanism ablations',plan['scope']);self.assertEqual(len(rows),5)
        for row in rows:
            self.assertTrue(row['expected_result_observed']);self.assertTrue(row['proofs_unchanged']);self.assertTrue(row['single_factor']);self.assertFalse(row['all_execution_safety_credit'])
            snap=(L/(row['name']+'.v.snapshot.txt')).read_text()
            self.assertEqual(sha(L/(row['name']+'.v.snapshot.txt')),row['source_sha256'])
            self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.',snap,re.S),re.findall(r'Proof\.(.*?)Qed\.',s,re.S))
            if row['name']!='positive':
                c=next(c for c in plan['controls'] if c['name']==row['name']);start=s.index('Theorem LinkReturnConnections :')
                self.assertEqual(snap,s[:start]+s[start:].replace(c['old'],c['new'],1));self.assertEqual(row['actual_error_lines'],[c['expected_error_line']])
    def test_build_and_kernel_trust(self):
        x=read(L/'build.json');self.assertEqual(x['exit'],0);self.assertEqual(x['active_sources'],195)
        self.assertEqual(x['old_products_reused'],965);self.assertFalse(x['source_only_cold_build'])
        x=read(L/'trust.json');self.assertTrue(x['passed']);self.assertEqual(x['roots_printed'],58)
        self.assertEqual(len(x['roots']),58);self.assertEqual([c['exit'] for c in x['commands']],[0,0])
        self.assertTrue(x['assumptions_allowed']);self.assertNotIn('MemoryNotFull',str(x['assumptions']))
        for token in ['toptheorem','V293OSInitTCBCall','V293InitTCBCall','V293InitTCBCallProbe']:self.assertIn(token,str(x['commands'][-1]['command']))
    def test_limits_and_adversarial_review(self):
        rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),10)
        for row in rows:self.assertTrue(row['resolution']);self.assertIn(row['kind'],['test','bounded claim','limitation'])
        x=read(L/'proof-report.json')
        for key in ['OS_InitTCBList_full_function','actual_four_local_allocations','actual_void_free_return','same_Mf_caller_writable_ownership','nonempty_shadowed_caller']:self.assertTrue(x[key],key)
        for key in ['OSInit_reachability','OSStart_reachability','all_execution_safety','GOOD_OS','same_program_K1_K4','ucos3_started','six_gates_promoted','git_commit_or_push']:self.assertFalse(x[key],key)
        self.assertEqual(x['goal_status'],'active');self.assertEqual(x['formal_six_gates'],[94,1,1,1,1,0])
