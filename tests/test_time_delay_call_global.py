"""真实客户端调用到全局切换的局部检查；语义有效性由 Coq/coqchk 复核。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage325-time-delay-call-global'
OLD = R / 'audit/logs/stage324-time-delay-allocated-sched'
P = 'certiucos/v293/proofs/V293TimeDlyCallGlobal.v'
Q = 'audit/probes/V293TimeDlyCallGlobalProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda name: json.loads((D / name).read_text())


class TimeDelayCallGlobalTests(unittest.TestCase):
    def test_exact_source_identity_and_replay(self):
        identities = read('source-identities.json')
        inventory = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        self.assertEqual(identities, json.loads((OLD / 'source-identities.json').read_text()))
        self.assertEqual({row['name'] for row in identities}, {'OSTimeDly', 'OS_Sched', 'OS_SchedNew'})
        for row in identities:
            self.assertIn(row, inventory['functions'])
            self.assertEqual(sha(D / (row['name'] + '.source.c.snapshot.txt')), row['source_lines_sha256'])
            self.assertEqual(hashlib.sha256((D / (row['name'] + '.configured.c.snapshot.txt')).read_bytes()[:-1]).hexdigest(),
                             row['preprocessed_definition_sha256'])
        self.assertEqual(read('source-replay.json')['exit'], 0)

    def test_stable_contract_constructs_real_entry_not_execution_or_store_oracle(self):
        source = (R / P).read_text()
        statement, proof = source.split('Theorem V293_dly_global_call_to_sched_refines:', 1)[1].split('Proof.', 1)
        inputs, outputs = statement.split('exists Mf,', 1)
        for token in ['V293_global_steps', 'V293_local_steps', 'cstepstar', 'store ', 'spec_step ', 'InOS']:
            self.assertNotIn(token, inputs)
        for token in ['get cles t=Some cle', 'po f=Some(V293_dly_function',
                      'fresh M ba', 'fresh M byloc', 'fresh M bs', 'V293_dly_call_cells']:
            self.assertIn(token, inputs)
        for token in ['V293_global_steps(pc,(po,pi,ip))(cge,cles,CM)',
                      'scall f[econst32 duration]),(kenil,kstop)', '(ge,caller,M)',
                      'scall sched nil', 'spec_step sd', 'V293_task_records Mf blocked', 'V293_bitmap_tasks']:
            self.assertIn(token, outputs)
        for token in ['V293_dly_global_call_entry', 'V293_dly_raw_body_to_sched', 'V293_local_steps_global',
                      'exact Entry', 'Body f']:
            self.assertIn(token, proof)
        entry = source.split('Theorem V293_dly_global_call_entry:', 1)[1].split('(* Stable function interface:', 1)[0]
        for token in ['V293_constant_call_global', 'sfexec_step', 'sallocp_step', 'salloclv_step',
                      'sallocend_step', 'V293_success_assign_zero', 'V293_bound_call_inos']:
            self.assertIn(token, entry)
        raw = source.split('Theorem V293_dly_raw_body_to_sched:', 1)[1].split('(* The client prefix', 1)[0]
        self.assertNotIn('V293_dly_call_entry', raw)
        self.assertNotIn('V293_dly_allocated_to_sched_refines', raw)
        self.assertNotIn('Require Import CertiOS.audit.', source)
        self.assertNotRegex(source, r'Require Import CertiOS\.(?:ucos|os_code|os_proof)\.')

    def test_distinct_client_heap_env_and_real_os_freshness(self):
        source = (R / Q).read_text()
        for token in ['Definition DXcle:env:=set emp 777%Z(12%positive,Tint32)',
                      'Definition DXclient:clientst:=(emp,DXcles,DXcm)',
                      '((12%positive,0%Z),Tint32,Vint32(Int.repr 99))',
                      '(DWge,emp,DAmem false c)', 'Theorem DXdistinct_heaps:', 'Lemma DXclient_alias:',
                      'get(emp:env)103%Z=None', 'get DWge 103%Z=Some(10%positive,Tptr V293_tcb_type)',
                      '(DAfresh false c 12%positive', '(DAfresh false c 11%positive', '(DAfresh false c 13%positive']:
            self.assertIn(token, source)
        distinct = source.split('Theorem DXdistinct_heaps:', 1)[1].split('Proof.', 1)[0]
        for token in ['V293_global_steps DAprog DXclient', 'load Tint32 M(12%positive,0%Z)=Some(Vint32(Int.repr 3))',
                      'load Tint32 DXcm(12%positive,0%Z)=Some(Vint32(Int.repr 99))', 'get DXcle 777%Z']:
            self.assertIn(token, distinct)
        production = (R / P).read_text()
        self.assertIn('CltEnvMod.get_set_same Get', production)
        self.assertIn('apply V293_client_no_os_context', production)
        prefix = production.split('Theorem V293_constant_call_global:', 1)[1].split('Theorem V293_dly_raw_body_to_sched:', 1)[0]
        for token in ['spcall_step', 'expr_step', 'svfevalnil_step']:
            self.assertIn(token, prefix)
        self.assertEqual(prefix.count('eapply V293_client_unchanged_global'), 3)

    def test_one_global_trace_from_call_through_scheduler(self):
        source = (R / Q).read_text()
        run = source.split('Theorem DXglobal_run:', 1)[1].split('Lemma DXcut_exact:', 1)[0]
        self.assertEqual(run.split('exists bs byblock Mf,')[0].strip(), 'forall c enabled,')
        for token in ['V293_dly_global_call_to_sched_refines', 'V293_sched_call_to_switch DAprogram',
                      'V293_global_trans;[exact Blocked', 'V293_local_steps_global', 'DXextends',
                      'exact Step', 'exact TaskFrame', 'exact Facts']:
            self.assertIn(token, run)
        for token in ['DAallocated_run', 'DAallocated_switch', 'DArun', 'DWblocked_run']:
            self.assertNotIn(token, source)
        definition = source.split('Definition DXrun', 1)[1].split('Lemma DXclient_alias:', 1)[0]
        self.assertIn('V293_global_steps DAprog DXclient(DXinitial c enabled)(DXcut enabled bs Mf)', definition)

    def test_actual_global_switch_same_state_high_selection_and_resources(self):
        source = (R / Q).read_text()
        for token in ['Theorem DXglobal_switch:', 'rewrite DXcut_exact in Run', 'V293_sched_switch_commit',
                      'exact Switch|apply rt1n_refl', 'Theorem DXhigh_switch:', 'eapply hswi_step',
                      'exact DWselected', 'Theorem DXboth_IE:', 'Theorem DXglobal_wrap:',
                      'rewrite DWcounter_wrap in Counter', 'eapply DAfacts_frame']:
            self.assertIn(token, source)
        switch = source.split('Theorem DXglobal_switch:', 1)[1].split('Proof.', 1)[0]
        for token in ['V293_global_steps DAprog DXclient(DXinitial c enabled)',
                      'lpstep DAprog DAtasks DXclient', 'Mcut', 'Mf', 'V293_task_records Mf',
                      'V293_bitmap_tasks 64 0', 'Some(Vptr OwnershipWaiting)', 'Int.add c Int.one',
                      'Some(V293_byteval 4)', 'Int.repr 99', 'DAfacts Mf', 'get Mf(byblock,0%Z)=None',
                      'SKIP,(kenil,DAcontinuation)', 'OwnershipWaiting=Some DWready',
                      'get(DAenvs bs)OwnershipWaiting=Some DCle', 'Some(true,nil,nil)']:
            self.assertIn(token, switch)
        high = source.split('Theorem DXhigh_switch:', 1)[1].split('Proof.', 1)[0]
        self.assertIn('DXclient(DEfinalabs(Int.repr 3))', high)
        self.assertIn('oscurt OwnershipWaiting', high)

    def test_prospective_single_binding_ablation_is_early_and_bounded(self):
        protocol = read('protocol.json')
        self.assertTrue(protocol['prospective'])
        self.assertEqual(sha(D / 'protocol.json'), 'd08aade9c987638cb04b48f0b112f19d7356a7681e63cc59452f759f0b0eeb58')
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
        self.assertIn('remove only OSTimeDly OS binding 1200', protocol['ablation']['factor'])
        self.assertIn('early call-link gate only', protocol['ablation']['scope'])
        source = (R / Q).read_text()
        for token in ['if Z.eq_dec f 1200%Z then None else DAprogram f', 'Lemma DXonly_binding:',
                      'forall f,f<>1200%Z ->DXmissing f=DAprogram f', 'Theorem DXsame_client_prefix:',
                      'V293_global_steps DXmissingprog DXclient(DXinitial c enabled)(DXentry c enabled)',
                      'eapply V293_constant_call_global', 'Theorem DXentry_gate:',
                      '~(exists C\' st\',loststep DXmissing', 'apply V293_missing_port_has_no_step']:
            self.assertIn(token, source)
        gate = source.split('Theorem DXentry_gate:', 1)[1].split('Proof.', 1)[0]
        self.assertNotIn('InOS', gate)
        self.assertNotIn('lpstep', gate)
        self.assertNotIn('hpstep', gate)
        self.assertNotIn('V293_global_steps', gate)

    def test_recursive_trust_and_two_stable_compiles(self):
        roots = []
        for p in [P, Q]:
            source = (R / p).read_text()
            self.assertNotRegex(source, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', source, re.M)]
        self.assertEqual(len(roots), 18)
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(x['exit'] == 0 for x in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']), {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        for name, p in [('production', P), ('probe', Q)]:
            for i in [1, 2]:
                result = read(f'stable-{name}-{i}.json')
                self.assertEqual(result['exit'], 0)
                self.assertEqual(result['initial_source_sha256'], sha(R / p))
                self.assertEqual(result['source_sha256'], sha(R / p))

    def test_history_registration_and_honest_boundary(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in read('baseline.json')['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        project = (R / '_CoqProject').read_bytes()
        self.assertTrue(project.startswith((D / '_CoqProject.baseline').read_bytes() + (P + '\n').encode()))
        self.assertEqual(project.splitlines().count(P.encode()), 1)
        self.assertEqual({str(p.relative_to(R)): sha(p) for p in R.rglob('*.pyc')}, read('bytecode-baseline.json'))
        boundary = read('function-boundary.json')
        for name in ['raw_entry_connected_to_blocking', 'raw_entry_connected_to_blocking_switch',
                     'scheduler_execution_from_this_call', 'whole_call_global_reachability_proved',
                     'client_heap_and_env_preserved']:
            self.assertTrue(boundary[name])
        for name in ['full_api_proved', 'priority_cache_synchronized', 'resumption_return_proved',
                     'global_ProgSim_proved', 'GOOD_OS_proved']:
            self.assertFalse(boundary[name])
        self.assertTrue(all(row['located'] and not any(v for k, v in row.items() if k != 'located')
                            for row in boundary['stages'].values()))
        doc = (R / 'audit/STAGE325_TIME_DELAY_CALL_GLOBAL.md').read_text()
        for token in ['不是完整 API', '不是全局记录不变量', '不是全局 ProgSim', '客户端堆',
                      '优先级缓存', '仅检验早期调用链接', '不声称负例原全局状态无任何后继', 'GOOD_OS', 'uCOS3']:
            self.assertIn(token, doc)
        for name in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / name).read_bytes().endswith((D / (name + '.baseline')).read_bytes()))


if __name__ == '__main__':
    unittest.main()
