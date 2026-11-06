"""显式扫描器准备后的实际tick片段；不把它视为合法ISR入口。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage332-switched-tick-prefix'
OLD = R / 'audit/logs/stage331-switched-countdown-closure'
P = 'certiucos/v293/proofs/V293SwitchedTickPrefix.v'
Q = 'audit/probes/V293SwitchedTickPrefixProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class SwitchedTickPrefixTests(unittest.TestCase):
    def test_fixed_source_replayed_with_same_tick_identity(self):
        rows = read('source-identities.json')
        self.assertEqual({r['name'] for r in rows}, {'OSTimeDly', 'OS_Sched', 'OS_SchedNew', 'OSTimeTick'})
        self.assertEqual(rows, json.loads((OLD / 'source-identities.json').read_text()))
        self.assertEqual(read('source-replay.json')['exit'], 0)
        inv = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        for row in rows:
            self.assertIn(row, inv['functions'])
            self.assertEqual(sha(D / (row['name'] + '.source.c.snapshot.txt')), row['source_lines_sha256'])
            b = (D / (row['name'] + '.configured.c.snapshot.txt')).read_bytes()
            self.assertEqual(hashlib.sha256(b[:-1]).hexdigest(), row['preprocessed_definition_sha256'])

    def test_public_interface_constructs_execution_from_ownership(self):
        s = (R / P).read_text()
        st, pf = s.split('Theorem V293_ready_countdown_iteration_prefix :', 1)[1].split('Proof.', 1)
        inputs, outputs = st.split(' exists Mf,', 1)
        for token in ['store ', 'spec_step', 'cstep', 'TaskSim', 'V293_global_steps', 'V293_local_steps']:
            self.assertNotIn(token, inputs)
        for token in ['(2<=d<=Int.max_unsigned)%Z', 'get O abstcblsid', 'get tasks(bt,Int.repr base)',
                      'V293_ready_full br bg bp current **', 'V293_owned_record_cell', 'GoodInvAsrt R']:
            self.assertIn(token, inputs)
        for token in ['store Tint32 M', 'V293_local_steps P', 'curs(V293_tick_iteration ptcb rows group)',
                      'curs(V293_tick_advance ptcb)', 'spec_step sd', 'V293_tick_wait_step',
                      'V293_ready_full br bg bp current **', 'get Mf(b,i)=get M(b,i)']:
            self.assertIn(token, outputs)
        self.assertIn('V293_ready_countdown_delay_execution', pf)
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertNotRegex(s, r'Require Import CertiOS\.(?:ucos|os_code|os_proof)\.')

    def test_actual_guards_assignment_critical_entry_and_precise_frame(self):
        s = (R / P).read_text()
        for token in ['V293_ready_countdown_store', 'V293_tick_field_eval', 'V293_tick_assign32_execution',
                      'V293_tick_delay_address', 'V293_rekey_if_execution with(flag:=true)',
                      'V293_rekey_if_execution with(flag:=false)', 'apply encrit_step',
                      '((ge,le,Mf),ir,(false,si,enabled::ci))', 'kseq(sprim excrit)ks',
                      '(base+48<=i)%Z', 'V293_csteps_local']:
            self.assertIn(token, s)
        self.assertNotIn('apply excrit_step', s)
        self.assertNotIn('alloc ', s)
        self.assertNotIn('V293_tick_advance_execution', s)
        self.assertIn('eapply good_inv_prop', s)

    def test_preparation_extends_original_switched_heap_explicitly(self):
        s = (R / Q).read_text()
        setup = s.split('Definition SPsetup', 1)[1].split('Definition SPexecution', 1)[0]
        for token in ['fresh M b', 'alloc 700%Z', 'cstep DAprogram', 'allocb M b',
                      'store(Tptr V293_tcb_type)', '(b,0%Z)(Vptr OwnershipReady)=Some Mp']:
            self.assertIn(token, setup)
        st, pf = s.split('Theorem SPsame_input_ablation:', 1)[1].split('Proof.', 1)
        self.assertEqual(st.split('exists bs')[0], 'forall c enabled,')
        for token in ['V293_global_steps DAprog DXclient(DXinitial c enabled)(DXfinal enabled bs M)',
                      'DGpost c bs M', 'SPsetup b M Mp', 'SPprepared c bs b Mp',
                      'SPexecution b Mp Mf', 'SPpost c bs b Mf']:
            self.assertIn(token, st)
        for token in ['DGglobal_switch c enabled', 'SPprepare c bs M After', 'SPfirst c bs b Mp Prepared']:
            self.assertIn(token, pf)
        self.assertNotIn('OwnershipCellsMemory', s)
        self.assertNotIn('Definition SPmem', s)

    def test_prospective_single_assignment_mutant_executes_and_late_fails(self):
        protocol = read('protocol.json')
        self.assertTrue(protocol['prospective'])
        self.assertEqual(sha(D / 'protocol.json'), '25a83405ed48cfbd4cd5f72f30eab9aab071f4ecd07d82cc7007c5f0341206a2')
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
        self.assertEqual(protocol['ablation']['factor'], 'replace only the decrement assignment by administrative skip')
        self.assertIn('not mutant ISR', protocol['ablation']['scope'])
        s = (R / Q).read_text()
        original = (R / 'certiucos/v293/code/V293OSTimeTick.v').read_text()
        original = original.split('Definition V293_tick_delay', 1)[1].split('Definition V293_tick_advance', 1)[0]
        original = original.split(' in\n', 1)[1].strip().removesuffix('.')
        assignment = '(sassign delay (ebinop ominus delay (econst32 Int.one)))'
        self.assertEqual(original.count(assignment), 1)
        expected = original.replace(assignment, '(sskip None)', 1)
        expected = re.sub(r'\bdelay\b', '(V293_tick_field ptcb 13%Z)', expected)
        mutant = s.split('Definition SPmutant_delay ptcb rows group:=', 1)[1].split('Definition SPmutant_iteration', 1)[0]
        mutant = mutant.strip().removesuffix('.')
        canon = lambda t: re.sub(r'[\s()]', '', t)
        self.assertEqual(canon(mutant), canon(expected))
        st, pf = s.split('Theorem SPsame_input_ablation:', 1)[1].split('Proof.', 1)
        for token in ['SPexecution b Mp Mf', 'V293_task_records Mf SCtasks2', 'SPmutant_execution b Mp',
                      'SPowned c bs b(false,nil,[true])DGabs Mp', '~V293_task_records Mp SCtasks2']:
            self.assertIn(token, st)
        self.assertIn('SPmutant_late_gate c bs b Mp Prepared', pf)
        self.assertIn('rewrite Delay in Delay2;discriminate', s)

    def test_same_full_ready_frame_current_and_bounded_claim(self):
        s = (R / Q).read_text()
        self.assertIn('V293_ready_full 30%positive 31%positive 83%positive OwnershipWaiting **', s)
        st = s.split('Lemma SPobserved:', 1)[1].split('Proof.', 1)[0]
        for token in ['In(a,tp,v)(DOcells c)',
                      'load(Tptr V293_tcb_type)M(10%positive,0%Z)=Some(Vptr OwnershipWaiting)',
                      'get SCabs2 curtid=Some(oscurt OwnershipWaiting)']:
            self.assertIn(token, st)
        doc = (R / 'audit/STAGE332_SWITCHED_TICK_PREFIX.md').read_text()
        for text in ['不是合法ISR入口', '不是完整OSTimeTick调用', '缓存仍为4', '没有TCB Next所有权',
                     '指针初始化只是资源准备', '晚对应关系门', '旧任务仍等待']:
            self.assertIn(text, doc)

    def test_recursive_trust_and_stable_sources(self):
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
        trust = read('trust.json')
        self.assertEqual(len(roots), 9)
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], 9)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']), {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        for name, p in [('production', P), ('probe', Q)]:
            for i in [1, 2]:
                row = read(f'stable-{name}-{i}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / p))
                self.assertEqual(row['source_sha256'], sha(R / p))

    def test_history_and_bounded_completion(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in read('baseline.json')['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        for n in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / n).read_bytes().endswith((D / (n + '.baseline')).read_bytes()))
        self.assertEqual((R / '_CoqProject').read_bytes(),
                         (D / '_CoqProject.baseline').read_bytes() + (P + '\n').encode())
        doc = (R / 'audit/STAGE332_SWITCHED_TICK_PREFIX.md').read_text()
        for token in ['GOOD_OS', 'uCOS3', 'K1–K4', '总目标保持active', '手工源码模型', '原全局轨迹止于']:
            self.assertIn(token, doc)
