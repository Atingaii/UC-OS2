"""同一实际切换堆上的真实while一步；文字检查不替代Coq内核。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage334-switched-linked-tick-loop'
OLD = R / 'audit/logs/stage333-ready-tick-linked-entry'
P = 'certiucos/v293/proofs/V293SwitchedLinkedTickLoop.v'
Q = 'audit/probes/V293SwitchedLinkedTickLoopProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class SwitchedLinkedTickLoopTests(unittest.TestCase):
    def test_fixed_source_identity_replayed(self):
        rows = read('source-identities.json')
        self.assertEqual({r['name'] for r in rows}, {'OSTimeDly', 'OS_Sched', 'OS_SchedNew', 'OSTimeTick'})
        self.assertEqual(rows, json.loads((OLD / 'source-identities.json').read_text()))
        self.assertEqual(read('source-replay.json')['exit'], 0)
        inv = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        for row in rows:
            self.assertIn(row, inv['functions'])
            self.assertEqual(sha(D / (row['name'] + '.source.c.snapshot.txt')), row['source_lines_sha256'])
            data = (D / (row['name'] + '.configured.c.snapshot.txt')).read_bytes()
            self.assertEqual(hashlib.sha256(data[:-1]).hexdigest(), row['preprocessed_definition_sha256'])
        tick = (D / 'OSTimeTick.configured.c.snapshot.txt').read_text()
        for token in ['ptcb = OSTCBList;', 'while (ptcb->OSTCBPrio != (12u))',
                      'ptcb = ptcb->OSTCBNext;', 'ptcb->OSTCBDly--;']:
            self.assertIn(token, tick)

    def test_stable_interface_derives_reads_and_effects(self):
        s = (R / P).read_text()
        guard = s.split('Lemma V293_ready_tick_guard :', 1)[1].split('Proof.', 1)[0]
        inputs, outputs = guard.split(' evalval(', 1)
        for token in ['load ', 'store ', 'evalval', 'V293_local_steps']:
            self.assertNotIn(token, inputs)
        self.assertIn('V293_ready_full br bg bp current **', inputs)
        self.assertIn('Some(Vint32(if Nat.eqb p 12', outputs)
        st = s.split('Theorem V293_ready_countdown_while_step :', 1)[1].split('Proof.', 1)[0]
        inputs, outputs = st.split(' exists Md Mf,', 1)
        for token in ['load ', 'store ', 'evalval', 'cstep', 'TaskSim', 'spec_step', 'V293_local_steps']:
            self.assertNotIn(token, inputs)
        for token in ['p<13 ->p<>12', '(2<=d<=Int.max_unsigned)%Z', 'GoodInvAsrt R',
                      'get tasks(bt,Int.repr base)', 'V293_owned_record_cell']:
            self.assertIn(token, inputs)
        for token in ['store Tint32 M', 'store(Tptr V293_tcb_type)Md', 'spec_step sd',
                      'V293_ready_full br bg bp current **', 'get Mf(b,i)=get M(b,i)']:
            self.assertIn(token, outputs)
        for token in ['V293_ready_full_records', 'V293_priority_repr_injective',
                      'V293_record_star_load_l', 'V293_tick_guard_eval']:
            self.assertIn(token, s)
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertNotRegex(s, r'Require Import CertiOS\.(?:ucos|os_code|os_proof)\.')

    def test_actual_while_guard_and_residual_loop(self):
        s = (R / P).read_text()
        st, proof = s.split('Theorem V293_ready_countdown_while_step :', 1)[1].split('Proof.', 1)
        loop = 'curs(swhile(V293_tick_guard ptcb)(V293_tick_iteration ptcb rows group))'
        self.assertEqual(st.count(loop), 2)
        for token in ['V293_ready_tick_guard', 'Nat.eqb_neq', 'V293_ready_countdown_linked_iteration',
                      'apply swhile_step', 'evalval_imply_estepstar;exact Guard',
                      'apply svwhilet_step', 'exact Execute', 'apply sskip_step']:
            self.assertIn(token, proof)
        q = (R / Q).read_text()
        self.assertIn('Definition LGloop:=swhile(V293_tick_guard 700%Z)(V293_tick_iteration', q)
        self.assertIn('OwnershipWaiting\n (DEblocked(Int.repr 3))60%positive 0 4 3', q)
        self.assertIn('((LHge,LHle b,Mf),(fun _:hid=>false),(true,nil,nil))', q)

    def test_original_client_heap_crosses_actual_scheduler_and_switch(self):
        s = (R / Q).read_text()
        self.assertNotIn('Definition LHmem', s)
        self.assertNotIn('Definition LGmem', s)
        for token in ['DOrest **V293_owned_record_cells LHlinks',
                      'V293_global_steps DAprog DXclient(LHinitial c enabled)(LGcut',
                      'LHglobal_ready c enabled', 'V293_owned_sched_call', 'LGlookup c enabled Mb Owned',
                      'LGentry c enabled Mb Owned', 'V293_local_function_extension', 'V293_local_steps_global',
                      'V293_owned_global_switch', 'V293_global_trans', 'exact Switch',
                      'V293_global_steps DAprog DXclient(LHinitial c enabled)(LGfinal enabled bs Mf)']:
            self.assertIn(token, s)
        aggregate = s.split('Theorem LGsame_input_ablation:', 1)[1]
        st, proof = aggregate.split('Proof.', 1)
        self.assertTrue(st.startswith('forall c enabled,exists '))
        for token in ['LGglobal_switch c enabled', 'LGprepare c bs M Post',
                      'LGiteration c bs b Mp Prepared', 'LGmutant_late_gate c bs b Mp Prepared']:
            self.assertIn(token, proof)
        for token in ['LGexecution b Mp Mf', 'LGmutant_execution b Mp Mmut',
                      'LHsetup b M Mp', 'LGpost c bs M']:
            self.assertIn(token, st)

    def test_scanner_comes_from_same_switched_heap(self):
        s = (R / Q).read_text()
        prepare = s.split('Lemma LGprepare:', 1)[1].split('Definition LGloop', 1)[0]
        for token in ['LGpost c bs M ->exists b Mp', 'fresh_exist M', 'V293_tick_scan_allocation',
                      'V293_ready_tick_head_execution', 'LHsetup b M Mp',
                      '(allocb M b 0%Z(typelen(Tptr V293_tcb_type)))', '703%Z b 91%positive']:
            self.assertIn(token, prepare)
        for token in ['LHmem', 'OwnershipCellsMemory', 'V293_tick_raw_slot_update']:
            self.assertNotIn(token, prepare)
        observed = s.split('Theorem LGobserved:', 1)[1].split('(* The only input', 1)[0]
        for token in ['LGabs2 scan M', '(10%positive,0%Z)=Some(Vptr OwnershipWaiting)',
                      '(84%positive,0%Z)=Some(V293_byteval 4)', 'Int.add c Int.one', 'Int.repr 99']:
            self.assertIn(token, observed)

    def test_prospective_next_only_mutant_executes_before_rejection(self):
        self.assertEqual(sha(D / 'protocol.json'), '23f2260c43f3473d6eb36cf539ba5c16166e6d70a1e36ee81efbb048ca639eae')
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
        protocol = read('protocol.json')
        self.assertTrue(protocol['prospective'])
        self.assertEqual(protocol['ablation']['factor'], 'replace only the Next assignment by skip inside the while iteration')
        s = (R / Q).read_text()
        source = (R / 'certiucos/v293/code/V293OSTimeTick.v').read_text()
        original = source.split('Definition V293_tick_iteration', 1)[1].split('Definition ', 1)[0]
        original = re.sub(r'\(\*[\s\S]*?\*\)', '', original).split(':=', 1)[1].strip().removesuffix('.')
        self.assertEqual(original.count('(V293_tick_advance ptcb)'), 1)
        expected = original.replace('(V293_tick_advance ptcb)', '(sskip None)', 1)
        old_probe = (R / 'audit/probes/V293ReadyTickLinkedEntryProbe.v').read_text()
        mutant = old_probe.split('Definition LHmutant_iteration ptcb rows group:=', 1)[1].split('Definition LHmutant_execution', 1)[0]
        canon = lambda t: re.sub(r'[\s()]', '', t.strip().removesuffix('.'))
        self.assertEqual(canon(mutant), canon(expected))
        self.assertIn('LGmutant_loop:=swhile(V293_tick_guard 700%Z)(LHmutant_iteration', s)
        late = s.split('Theorem LGmutant_late_gate:', 1)[1].split('Lemma LGcurrent:', 1)[0]
        for token in ['LGmutant_execution b M Mf', 'V293_ready_tick_guard', 'apply swhile_step',
                      'apply svwhilet_step', 'V293_ready_countdown_delay_execution', 'apply excrit_step',
                      'LGowned c bs b(true,nil,nil)LGabs2 OwnershipReady Mf', '~LGposttick c bs b Mf',
                      'rewrite Pointer in Next;discriminate']:
            self.assertIn(token, late)

    def test_recursive_kernel_check_and_repeat_compilation(self):
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
        trust = read('trust.json')
        self.assertEqual(len(roots), 16)
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], 16)
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

    def test_history_append_contract_and_bounded_claims(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in read('baseline.json')['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        for n in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / n).read_bytes().endswith((D / (n + '.baseline')).read_bytes()))
        prefix = (D / '_CoqProject.baseline').read_bytes() + (P + '\n').encode()
        current = (R / '_CoqProject').read_bytes()
        self.assertTrue(current.startswith(prefix))
        self.assertTrue(all(line.startswith('certiucos/v293/') and line.endswith('.v')
                            for line in current[len(prefix):].decode().splitlines()))
        doc = (R / 'audit/STAGE334_SWITCHED_LINKED_TICK_LOOP.md').read_text()
        for token in ['GOOD_OS', 'uCOS3', 'K1–K4', '总目标保持active', '手工源码模型',
                      '不是合法ISR入口', '不是完整OSTimeTick调用', '残余while',
                      '不是OSInit/TaskCreate的初始化来源证明', '缓存仍为4',
                      '完整ready_full本身不拥有Next', 'ready记录也不提供delay44所有权']:
            self.assertIn(token, doc)
