"""链表头赋值与一次完整未到期迭代的有界证明检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage333-ready-tick-linked-entry'
OLD = R / 'audit/logs/stage332-switched-tick-prefix'
P = 'certiucos/v293/proofs/V293ReadyTickLinkedEntry.v'
Q = 'audit/probes/V293ReadyTickLinkedEntryProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class ReadyTickLinkedEntryTests(unittest.TestCase):
    def test_fixed_source_identity_replayed(self):
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
        tick = (D / 'OSTimeTick.configured.c.snapshot.txt').read_text()
        for text in ['ptcb = OSTCBList;', 'ptcb = ptcb->OSTCBNext;', 'ptcb->OSTCBDly--;']:
            self.assertIn(text, tick)

    def test_stable_interface_has_no_execution_or_store_input(self):
        s = (R / P).read_text()
        for name, boundary in [('V293_ready_tick_head_execution', ' exists Mh,'),
                               ('V293_ready_tick_advance_execution', ' exists Mf,'),
                               ('V293_ready_countdown_linked_iteration', ' exists Md Mf,')]:
            statement = s.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]
            inputs, outputs = statement.split(boundary, 1)
            for token in ['store ', 'spec_step', 'cstep', 'TaskSim', 'V293_global_steps', 'V293_local_steps']:
                self.assertNotIn(token, inputs)
            self.assertIn('V293_owned_record_cell', inputs)
            self.assertIn('store(Tptr V293_tcb_type)', outputs)
            self.assertIn('get Mf(b,i)=get M(b,i)' if name.endswith('advance_execution') else
                          'get Mh(b,i)=get M(b,i)' if name.endswith('head_execution') else
                          'get Mf(b,i)=get M(b,i)', outputs)
        st = s.split('Theorem V293_ready_countdown_linked_iteration :', 1)[1].split('Proof.', 1)[0]
        for token in ['(2<=d<=Int.max_unsigned)%Z', 'get O abstcblsid', 'get tasks(bt,Int.repr base)',
                      'V293_ready_full br bg bp current **', 'GoodInvAsrt R',
                      'V293_local_steps P', 'spec_step sd', '(enabled,si,ci)', 'load Tint32 Mf']:
            self.assertIn(token, st)
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertNotRegex(s, r'Require Import CertiOS\.(?:ucos|os_code|os_proof)\.')

    def test_source_read_write_and_real_critical_exit(self):
        s = (R / P).read_text()
        for token in ['get le head=None', 'get ge head=Some(bh,Tptr V293_tcb_type)',
                      'curs(sassign(evar ptcb)(evar head))', 'V293_tick_raw_slot_update',
                      'V293_tick_field_eval ge le M ptcb bc bt base 7%Z 20%Z',
                      'V293_assign_pointer_execution', 'apply eq_vcomptr',
                      'V293_ready_countdown_iteration_prefix', 'exact Advance',
                      'apply excrit_step', 'V293_ready_full_records', 'OutsideA', 'OutsideD']:
            self.assertIn(token, s)
        # No successful load or store is supplied by the caller of the stable seam.
        inputs = s.split('Theorem V293_ready_countdown_linked_iteration :', 1)[1].split(' exists Md Mf,', 1)[0]
        self.assertNotIn('load ', inputs)
        self.assertNotIn('V293_ready_full_good', s)

    def test_links_are_present_before_actual_client_prefix(self):
        s = (R / Q).read_text()
        for token in ['Definition LHlinks:list V293_record_cell', '((91%positive,0%Z)',
                      '((60%positive,20%Z)', 'Definition LHframe c:=DAframe false c++LHlinks',
                      'Definition LHmem c:=merge(OwnershipCellsMemory(LHsmall c))DSlookup',
                      '((LHge,emp,LHmem c)', 'LHentry c enabled',
                      'V293_dly_global_call_ready', '(LHresources c)', 'LHrun c enabled Mf']:
            self.assertIn(token, s)
        statement, proof = s.split('Theorem LHsame_input_ablation:', 1)[1].split('Proof.', 1)
        self.assertTrue(statement.startswith('forall c enabled,exists M b Mp Md Mf Mmut,'))
        for token in ['LHglobal_ready c enabled', 'LHprepare c enabled M Post',
                      'LHiteration c b enabled Mp Prepared', 'LHmutant_late_gate c b enabled Mp Prepared']:
            self.assertIn(token, proof)
        for token in ['LHrun c enabled M', 'LHsetup b M Mp', 'LHprepared c b enabled Mp',
                      'LHexecution b enabled Mp Mf', 'LHmutant_execution b enabled Mp Mmut']:
            self.assertIn(token, statement)

    def test_scanner_is_allocated_then_initialized_by_source_head_read(self):
        s = (R / Q).read_text()
        setup = s.split('Definition LHsetup', 1)[1].split('Lemma LHrest_good', 1)[0]
        for token in ['fresh M b', 'alloc 700%Z', 'cstep DAprogram', 'allocb M b',
                      'sassign(evar 700%Z)(evar 703%Z)', '(b,0%Z)(Vptr OwnershipReady)=Some Mp']:
            self.assertIn(token, setup)
        prepare = s.split('Lemma LHprepare:', 1)[1].split('Definition LHexecution', 1)[0]
        self.assertIn('V293_tick_scan_allocation', prepare)
        self.assertIn('V293_ready_tick_head_execution', prepare)
        self.assertNotIn('V293_tick_raw_slot_update', prepare)
        self.assertIn('Definition LHge:=set DWge 703%Z(91%positive,Tptr V293_tcb_type)', s)
        self.assertIn('Definition LHle b:env:=set(emp:env)700%Z', s)

    def test_prospective_next_only_mutant_executes_and_late_rejects(self):
        self.assertEqual(sha(D / 'protocol.json'), '662fa94dce340a9b8f0f5afa037244ee9c2507c08d459456395f917153c8054c')
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
        protocol = read('protocol.json')
        self.assertTrue(protocol['prospective'])
        self.assertEqual(protocol['ablation']['factor'], 'replace only the Next assignment by skip')
        s = (R / Q).read_text()
        source = (R / 'certiucos/v293/code/V293OSTimeTick.v').read_text()
        original = source.split('Definition V293_tick_iteration', 1)[1].split('Definition ', 1)[0]
        original = re.sub(r'\(\*[\s\S]*?\*\)', '', original)
        original = original.split(':=', 1)[1].strip().removesuffix('.')
        self.assertEqual(original.count('(V293_tick_advance ptcb)'), 1)
        expected = original.replace('(V293_tick_advance ptcb)', '(sskip None)', 1)
        mutant = s.split('Definition LHmutant_iteration ptcb rows group:=', 1)[1].split('Definition LHmutant_execution', 1)[0]
        canon = lambda t: re.sub(r'[\s()]', '', t.strip().removesuffix('.'))
        self.assertEqual(canon(mutant), canon(expected))
        late = s.split('Theorem LHmutant_late_gate:', 1)[1].split('Theorem LHsame_input_ablation:', 1)[0]
        for token in ['LHmutant_execution b enabled M Mf', 'V293_ready_countdown_delay_execution',
                      'apply excrit_step', 'LHowned c b(enabled,nil,nil)LHabs2 OwnershipReady Mf',
                      'load Tint32 Mf(60%positive,44%Z)=Some(Vint32(Int.repr 2))',
                      '~LHposttick c b enabled Mf', 'rewrite Pointer in Next;discriminate']:
            self.assertIn(token, late)

    def test_recursive_kernel_check_and_repeat_compilation(self):
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
        trust = read('trust.json')
        self.assertEqual(len(roots), 15)
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], 15)
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

    def test_history_and_explicit_limitations(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in read('baseline.json')['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        for n in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / n).read_bytes().endswith((D / (n + '.baseline')).read_bytes()))
        self.assertEqual((R / '_CoqProject').read_bytes(),
                         (D / '_CoqProject.baseline').read_bytes() + (P + '\n').encode())
        doc = (R / 'audit/STAGE333_READY_TICK_LINKED_ENTRY.md').read_text()
        for token in ['GOOD_OS', 'uCOS3', 'K1–K4', '总目标保持active', '手工源码模型',
                      '不是合法ISR入口', '不是完整OSTimeTick调用', '原全局轨迹止于',
                      '不是OSInit/TaskCreate的初始化来源证明', '缓存仍为4', '旧任务仍等待',
                      '完整ready_full本身不拥有Next']:
            self.assertIn(token, doc)
