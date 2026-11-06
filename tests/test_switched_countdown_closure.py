"""切换末端的store级资源接缝；不把它视为时钟中断执行。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage331-switched-countdown-closure'
OLD = R / 'audit/logs/stage330-time-delay-nested-return'
P = 'certiucos/v293/proofs/V293SwitchedCountdownClosure.v'
Q = 'audit/probes/V293SwitchedCountdownClosureProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class SwitchedCountdownClosureTests(unittest.TestCase):
    def test_fixed_source_replayed_with_tick_identity(self):
        rows = read('source-identities.json')
        self.assertEqual({r['name'] for r in rows}, {'OSTimeDly', 'OS_Sched', 'OS_SchedNew', 'OSTimeTick'})
        self.assertEqual([r for r in rows if r['name'] != 'OSTimeTick'],
                         json.loads((OLD / 'source-identities.json').read_text()))
        self.assertEqual(read('source-replay.json')['exit'], 0)
        inv = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        for row in rows:
            self.assertIn(row, inv['functions'])
            self.assertEqual(sha(D / (row['name'] + '.source.c.snapshot.txt')), row['source_lines_sha256'])
            b = (D / (row['name'] + '.configured.c.snapshot.txt')).read_bytes()
            self.assertEqual(hashlib.sha256(b[:-1]).hexdigest(), row['preprocessed_definition_sha256'])

    def test_public_interface_has_only_owned_resource_inputs(self):
        s = (R / P).read_text()
        st, pf = s.split('Theorem V293_ready_countdown_store :', 1)[1].split('Proof.', 1)
        inputs, outputs = st.split(' exists Mf,', 1)
        for token in ['store ', 'spec_step', 'cstep', 'TaskSim', 'V293_global_steps']:
            self.assertNotIn(token, inputs)
        for token in ['(2<=d<=Int.max_unsigned)%Z', 'get O abstcblsid',
                      'get tasks t', 'V293_ready_full br bg bp current **R']:
            self.assertIn(token, inputs)
        for token in ['store Tint32 M', 'spec_step sd', 'V293_tick_wait_step t',
                      'V293_ready_full br bg bp current **R', 'get Mf(b,i)=get M(b,i)']:
            self.assertIn(token, outputs)
        self.assertIn('V293_owned_task_records_focus', pf)
        self.assertIn('V293_time_wait_record_store', pf)
        self.assertIn('V293_owned_task_records_reassemble', pf)
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertNotRegex(s, r'Require Import CertiOS\.(?:ucos|os_code|os_proof)\.')

    def test_unchanged_ready_relation_and_precise_store_frame(self):
        s = (R / P).read_text()
        st, pf = s.split('Lemma V293_ready_countdown_rel :', 1)[1].split('Proof.', 1)
        self.assertEqual(st.count('V293_ready_rel lo hi entries'), 2)
        self.assertIn('V293_tick_wait_bitmap_tasks', pf)
        self.assertIn('V293_tick_priority_table', pf)
        for token in ['V293_storebytes_outside', 'V293_shared_replace_slot',
                      'V293_tick_wait_transition', 'V293_owned_record_cell_update']:
            self.assertIn(token, s)
        self.assertNotIn('alloc ', s)
        self.assertIn('(Int.unsigned(snd t)+48<=i)%Z', s)

    def test_two_countdowns_start_at_actual_global_switch_heap(self):
        s = (R / Q).read_text()
        st, pf = s.split('Theorem SCtwo_countdowns:', 1)[1].split('Proof.', 1)
        self.assertEqual(st.split('exists bs')[0], 'forall c enabled,')
        for token in ['V293_global_steps DAprog DXclient(DXinitial c enabled)(DXfinal enabled bs M)',
                      'DGpost c bs M', 'store Tint32 M(60%positive,44%Z)',
                      'store Tint32 M2(60%positive,44%Z)', 'SCpost c bs SCabs2 M2',
                      'SCpost c bs SCabs1 M1', 'get M1(b,i)=get M(b,i)']:
            self.assertIn(token, st)
        for token in ['DGglobal_switch c enabled', 'SCfirst c bs M After', 'SCsecond c bs M2 H2']:
            self.assertIn(token, pf)
        self.assertNotIn('OwnershipCellsMemory', s)
        self.assertNotIn('Definition SCmem', s)

    def test_old_task_remains_waiting_and_current_frame_unchanged(self):
        s = (R / Q).read_text()
        self.assertIn('get SCtasks1 OwnershipReady=Some(Int.repr 4,wait os_stat_time(Int.repr 1),Vnull)', s)
        self.assertIn('get SCabs1 curtid=Some(oscurt OwnershipWaiting)', s)
        self.assertIn('V293_ready_full 30%positive 31%positive 83%positive OwnershipWaiting **DGframe c bs', s)
        st = s.split('Lemma SCobserved:', 1)[1].split('Proof.', 1)[0]
        self.assertIn('In(a,tp,v)(DOcells c)', st)
        self.assertIn('load(Tptr V293_tcb_type)M(10%positive,0%Z)=Some(Vptr OwnershipWaiting)', st)
        doc = (R / 'audit/STAGE331_SWITCHED_COUNTDOWN_CLOSURE.md').read_text()
        for text in ['不是实际tick AST执行', '缓存仍为4', '没有暗中添加TCB Next字段', '不是到期唤醒']:
            self.assertIn(text, doc)

    def test_prospective_same_store_commit_ablation(self):
        protocol = read('protocol.json')
        self.assertTrue(protocol['prospective'])
        self.assertEqual(sha(D / 'protocol.json'), '20e19cef53be060d4d169db34bd00bf101954acf6536b8174b840aa9abde2d01')
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
        self.assertIn('only abstract task-map commit', protocol['ablation']['factor'])
        self.assertIn('not mutant ISR', protocol['ablation']['scope'])
        st, pf = (R / Q).read_text().split('Theorem SCcommit_ablation:', 1)[1].split('Proof.', 1)
        for token in ['DGpost c bs M', 'store Tint32 M(60%positive,44%Z)',
                      'V293_task_records M2 SCtasks2', '~V293_task_records M2(DEblocked(Int.repr 3))']:
            self.assertIn(token, st)
        self.assertIn('SCfirst c bs M After', pf)
        self.assertIn('rewrite L2 in Delay;discriminate', pf)

    def test_recursive_trust_and_stable_sources(self):
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
        trust = read('trust.json')
        self.assertEqual(len(roots), 10)
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], 10)
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
        doc = (R / 'audit/STAGE331_SWITCHED_COUNTDOWN_CLOSURE.md').read_text()
        for token in ['GOOD_OS', 'uCOS3', 'K1–K4', '总目标保持active', '晚对应关系门']:
            self.assertIn(token, doc)
