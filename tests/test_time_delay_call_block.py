"""真实延时调用至阻塞/临界退出的局部检查点；不代替全目标验收。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage323-time-delay-call-block'
OLD = R / 'audit/logs/stage322-time-delay-call-entry'
P = 'certiucos/v293/proofs/V293TimeDlyTail.v'
Q = 'audit/probes/V293TimeDlyTailProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda name: json.loads((D / name).read_text())


class TimeDelayCallBlockTests(unittest.TestCase):
    def test_exact_source_declarations_and_independent_replay(self):
        identities = read('source-identities.json')
        inventory = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        self.assertEqual(identities, json.loads((OLD / 'source-identities.json').read_text()))
        self.assertEqual({row['name'] for row in identities}, {'OSTimeDly', 'OS_Sched', 'OS_SchedNew'})
        for row in identities:
            self.assertIn(row, inventory['functions'])
            self.assertEqual(sha(D / (row['name'] + '.source.c.snapshot.txt')), row['source_lines_sha256'])
            self.assertEqual(hashlib.sha256((D / (row['name'] + '.configured.c.snapshot.txt')).read_bytes()[:-1]).hexdigest(),
                             row['preprocessed_definition_sha256'])
        source = (D / 'OSTimeDly.configured.c.snapshot.txt').read_text()
        tokens = ['y = OSTCBCur->OSTCBY;', 'OSRdyTbl[y] &=', 'if (OSRdyTbl[y] == 0u)',
                  'OSRdyGrp &=', 'OSTCBCur->OSTCBDly = ticks;', 'V293_ExitCritical(&cpu_sr);', 'OS_Sched();']
        self.assertEqual([source.index(t) for t in tokens], sorted(source.index(t) for t in tokens))
        self.assertEqual(read('source-replay.json')['exit'], 0)

    def test_suffix_constructs_stores_without_restarting_first_y(self):
        source = (R / P).read_text()
        for name in ['V293_dly_after_y_execution', 'V293_dly_after_y_updates']:
            statement = source.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]
            inputs, outputs = statement.split('exists Mf,', 1)
            for token in ['cstepstar', 'V293_local_steps', 'store ', 'GOOD_OS']:
                self.assertNotIn(token, inputs)
            self.assertIn('V293_dly_env', inputs)
            self.assertIn('V293_owned_record_cells', inputs)
            self.assertIn('V293_dly_after_y current rows group y', outputs)
        for token in ['V293_tick_cells_store_at _ 7', 'V293_tick_cells_store_at _ 8',
                      'V293_tick_cells_store_at _ 9', 'V293_tick_cells_store_at _ 6',
                      'V293_dly_field current 13%Z', 'base+44', 'destruct(cv=?0)eqn:Zero']:
            self.assertIn(token, source)
        for token in ['V293_dly_body_first_y', 'V293_dly_body_enters_positive',
                      'V293_OSTimeDly_body_to_sched_refines', 'apply encrit_step',
                      'V293_dly_raw_y_assignment', 'Require Import CertiOS.audit.']:
            self.assertNotIn(token, source)

    def test_refinement_uses_same_heap_original_step_and_owned_slots(self):
        source = (R / P).read_text()
        statement, proof = source.split('Theorem V293_dly_after_y_refines :', 1)[1].split('Proof.', 1)
        inputs, outputs = statement.split('exists Mf,', 1)
        for token in ['cstepstar', 'store ', 'spec_step ', 'V293_task_records M']:
            self.assertNotIn(token, inputs)
        for token in ['V293_task_records Mf blocked', 'V293_priority_table entries blocked',
                      'V293_bitmap_tasks(fst cleared)(snd cleared)blocked', 'spec_step sd',
                      '(ge,le,Mf,ir,au,O\',op)|=']:
            self.assertIn(token, outputs)
        for token in ['V293_tick_records_replace', 'V293_shared_fields_get',
                      'V293_shared_replace_slot', 'apply V293_dly_block_transition',
                      'V293_dly_after_y_updates']:
            self.assertIn(token, proof)

    def test_closed_real_call_consumes_prefix_and_stable_suffix(self):
        source = (R / Q).read_text()
        for name in ['DYcall_blocks', 'DYclosed_call_resources']:
            statement = source.split('Theorem ' + name + ':', 1)[1].split('Proof.', 1)[0]
            self.assertEqual(statement.split('exists Mf,', 1)[0].strip(), 'forall enabled sd,')
            for token in ['scall 1200%Z[econst32(Int.repr 3)]', '((DCge,emp,DCmem)',
                          'scall 112%Z nil', 'V293_task_records Mf DTblocked',
                          'V293_bitmap_tasks 64 0 DTblocked', 'spec_step sd']:
                self.assertIn(token, statement)
        for token in ['DCcall_first_y enabled', 'DYprepare My enabled Post',
                      'V293_dly_after_y_to_sched_refines', 'exact Prefix|exact Tail',
                      'apply DYobservations with(enabled:=enabled)', 'apply DTlow_owned']:
            self.assertIn(token, source)
        old_probe = (R / 'audit/probes/V293TimeDlyCallEntryProbe.v').read_text()
        self.assertIn('V293_record_layout OwnershipReady 4 rdy', old_probe)
        self.assertIn('++DLlow', old_probe)

    def test_restored_aux_parameter_cpu_canary_and_current_resources(self):
        source = (R / P).read_text()
        stable = source.split('Theorem V293_dly_after_y_to_sched_refines :', 1)[1]
        for token in ['(false,si,cons enabled ci)', '((ge,le,Mf),ir,(enabled,si,ci))',
                      '(ge,le,M,ir,(enabled,si,ci),O,op)|=', 'apply excrit_step']:
            self.assertIn(token, stable)
        source = (R / Q).read_text()
        facts = source.split('Definition DYfacts', 1)[1].split('Lemma DYobservations:', 1)[0]
        for token in ['load Tint32 M(60%positive,44%Z)', 'load Tint8 M(11%positive,0%Z)',
                      'load Tint32 M(12%positive,0%Z)=Some(Vint32(Int.repr 3))',
                      'load Tint32 M(13%positive,0%Z)=Some(Vint32 Int.zero)',
                      'load Tint32 M(90%positive,0%Z)=Some(Vint32(Int.repr 99))',
                      'V293_bytes_writable M 13%positive 0%Z 4',
                      'get O curtid=Some(oscurt OwnershipReady)', 'get O abstcblsid']:
            self.assertIn(token, facts)
        self.assertIn('V293_tick_raw_owned_writable 13%positive Tint32', source)
        self.assertIn('((70%positive,0%Z),Tint8,V293_byteval 0)', source)
        self.assertIn('((71%positive,0%Z),Tint8,V293_byteval 0)', source)

    def test_prospective_single_factor_ablation_is_separate_fragment(self):
        protocol = read('protocol.json')
        self.assertTrue(protocol['prospective'])
        self.assertEqual(sha(D / 'protocol.json'), '21555b7233026a9ea3f20da03eeb3c685d66b7784526f4912cbb31e923312048')
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
        self.assertIn('omit only final delay write', protocol['ablation']['factor'])
        self.assertIn('fragment trace only', protocol['ablation']['scope'])
        source = (R / Q).read_text()
        self.assertIn('DYno_write_cont:=kseq(sseq(sskip None)(sskip None))', source)
        statement, proof = source.split('Theorem DYno_delay_write:', 1)[1].split('Proof.', 1)
        for token in ['(curs DCafter,(kenil,DCcont))',
                      'DCprogram(curs DCafter,(kenil,DYno_write_cont))',
                      'DYowned Int.zero 64 0 DLtasks', 'DYfacts Int.zero 64 0 DLtasks Mf DCabs',
                      'load Tint32 Mf(60%positive,44%Z)<>Some(Vint32(Int.repr 3))']:
            self.assertIn(token, statement)
        for token in ['spec_step', 'V293_task_records Mf', 'V293_bitmap_tasks']:
            self.assertNotIn(token, statement)
        for token in ['DCcall_first_y enabled', 'V293_dly_after_y_execution',
                      'apply excrit_step', 'rewrite OldDelay;discriminate']:
            self.assertIn(token, proof)
        self.assertNotIn('V293_dly_after_y_to_sched_refines', proof)

    def test_recursive_trust_and_stable_compiles(self):
        roots = []
        for p in [P, Q]:
            source = (R / p).read_text()
            self.assertNotRegex(source, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', source, re.M)]
        self.assertEqual(len(roots), 10)
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

    def test_frozen_history_and_honest_documented_scope(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in read('baseline.json')['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        project = (R / '_CoqProject').read_bytes()
        self.assertTrue(project.startswith((D / '_CoqProject.baseline').read_bytes() + (P + '\n').encode()))
        self.assertEqual(project.splitlines().count(P.encode()), 1)
        self.assertEqual({str(p.relative_to(R)): sha(p) for p in R.rglob('*.pyc')}, read('bytecode-baseline.json'))
        boundary = read('function-boundary.json')
        self.assertTrue(boundary['raw_entry_connected_to_blocking'])
        for name in ['full_api_proved', 'raw_entry_connected_to_blocking_switch',
                     'scheduler_execution_from_this_call', 'whole_call_global_reachability_proved',
                     'priority_cache_synchronized']:
            self.assertFalse(boundary[name])
        self.assertTrue(all(row['located'] and not any(v for k, v in row.items() if k != 'located')
                            for row in boundary['stages'].values()))
        doc = (R / 'audit/STAGE323_TIME_DELAY_CALL_BLOCK.md').read_text()
        for token in ['不是完整 API', '不是全局记录不变量', '不是全局 ProgSim',
                      '不重跑整个 body', '入口辅助状态快照', '客户端堆', '优先级缓存',
                      '不拼成原程序的一条完整调用轨迹', 'GOOD_OS', 'uCOS3']:
            self.assertIn(token, doc)
        for name in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / name).read_bytes().endswith((D / (name + '.baseline')).read_bytes()))


if __name__ == '__main__':
    unittest.main()
