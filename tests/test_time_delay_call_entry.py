"""真实延时调用分配与 raw y 首次赋值；不是整核验收。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage322-time-delay-call-entry'
OLD = R / 'audit/logs/stage321-time-delay-global-switch'
P = 'certiucos/v293/proofs/V293TimeDlyCallEntry.v'
Q = 'audit/probes/V293TimeDlyCallEntryProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda name: json.loads((D / name).read_text())


class TimeDelayCallEntryTests(unittest.TestCase):
    def test_exact_source_declarations_and_independent_replay(self):
        identities = read('source-identities.json')
        inventory = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        self.assertEqual(identities, json.loads((OLD / 'source-identities.json').read_text()))
        for row in identities:
            self.assertIn(row, inventory['functions'])
            self.assertEqual(sha(D / (row['name'] + '.source.c.snapshot.txt')), row['source_lines_sha256'])
            self.assertEqual(hashlib.sha256((D / (row['name'] + '.configured.c.snapshot.txt')).read_bytes()[:-1]).hexdigest(),
                             row['preprocessed_definition_sha256'])
        source = (D / 'OSTimeDly.configured.c.snapshot.txt').read_text()
        for token in ['INT8U y;', 'OS_CPU_SR cpu_sr = 0u;', 'y = OSTCBCur->OSTCBY;']:
            self.assertIn(token, source)
        self.assertNotIn('y = 0', source)
        self.assertEqual(read('source-replay.json')['exit'], 0)

    def test_allocation_and_initializer_are_outputs_not_oracles(self):
        source = (R / P).read_text()
        statement, proof = source.split('Theorem V293_dly_call_entry:', 1)[1].split('Proof.', 1)
        inputs, outputs = statement.split('exists Mp Mi,', 1)
        for forbidden in ['V293_local_steps', 'cstepstar', 'store ', 'ProgSim', 'GOOD_OS']:
            self.assertNotIn(forbidden, inputs)
        for token in ['P f=Some(V293_dly_function', 'fresh M bt', 'fresh M by_', 'fresh M bs']:
            self.assertIn(token, inputs)
        for token in ['store Tint32', 'scall f[econst32 n]', 'Amapsto(by_,0%Z)Tint8 true Vundef']:
            self.assertIn(token, outputs)
        for token in ['V293_dly_call_allocate', 'V293_time_parameter_store', 'V293_success_assign_zero',
                      'sallocp_step', 'salloclv_step', 'sfexec_step', 'spcall_step', 'svfevalnil_step']:
            self.assertIn(token, source)
        self.assertNotIn('Require Import CertiOS.audit.', source)

    def test_raw_y_is_written_from_actual_tcb_before_typed_ownership(self):
        source = (R / P).read_text()
        statement, proof = source.split('Theorem V293_dly_raw_y_assignment:', 1)[1].split('Proof.', 1)
        inputs, outputs = statement.split('exists Mf,', 1)
        self.assertIn('Amapsto(by_,0%Z)Tint8 true Vundef **R', inputs)
        self.assertNotIn('V293_owned_record_cell', inputs)
        for token in ['Some(Vptr(bt,Int.repr base))', '(base+52)%Z', 'row<256']:
            self.assertIn(token, inputs)
        for token in ['store Tint8', 'V293_dly_field current 18%Z', 'V293_owned_record_cell', 'b<>by_']:
            self.assertIn(token, outputs)
        for token in ['V293_pub_field_value', 'V293_tick_raw_slot_update', 'V293_assign_byte_offset_execution',
                      'V293_dly_body_enters_positive', 'apply encrit_step']:
            self.assertIn(token, source)
        self.assertNotIn('V293_OSTimeDly_body_to_sched_refines', source)

    def test_nonempty_actual_caller_prefix_and_resources(self):
        source = (R / Q).read_text()
        statement = source.split('Theorem DCcall_first_y:', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(statement.split('exists Mp Mi Mf,', 1)[0].strip(), 'forall enabled,')
        for token in ['scall 1200%Z[econst32(Int.repr 3)]', '((DCge,emp,DCmem)', 'DCpost Mf enabled',
                      'V293_task_records Mf DLtasks', 'Some Vundef', 'Vint32(Int.repr 99)', 'DCcont',
                      '(false,nil,[enabled])', 'get DCabs abstcblsid']:
            self.assertIn(token, statement)
        for token in ['V293_dly_call_entry', 'V293_dly_body_first_y', 'exact Entry|exact Prefix',
                      'DCfresh', 'OwnershipCellsOutside', 'DCframe_records', 'DCboth_IE',
                      'DCinitialized_cpu_writable', 'V293_tick_raw_owned_writable']:
            self.assertIn(token, source)
        for token in ['V293_record_layout OwnershipReady 4 rdy', '++DLlow', 'V293_shared_fields',
                      'OwnershipCellsMemory DCcells']:
            self.assertIn(token, source)

    def test_initializer_only_ablation_reaches_late_value_gate(self):
        protocol = read('protocol.json')
        self.assertTrue(protocol['prospective'])
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
        self.assertIn('omit only cpu_sr initializer', protocol['ablation']['factor'])
        source = (R / Q).read_text()
        negative = source.split('Theorem DCno_initializer:', 1)[1].split('Theorem DCinitialized_cpu_writable:', 1)[0]
        statement, proof = negative.split('Proof.', 1)
        for token in ['store Tint32(allocb DCmem 12%positive 0%Z 4)', 'curs DCbody', 'DCafter',
                      'load Tint8 Ma(11%positive,0%Z)=Some Vundef', 'V293_task_records Mf DLtasks',
                      'Vint32(Int.repr 99)', 'V293_bytes_writable Mf 13%positive 0%Z 4',
                      'load Tint32 Mf(13%positive,0%Z)=Some Vundef',
                      'load Tint32 Mf(13%positive,0%Z)<>Some(Vint32 Int.zero)']:
            self.assertIn(token, statement)
        self.assertIn('V293_dly_call_allocate', proof)
        self.assertIn('V293_dly_body_first_y', proof)
        self.assertNotIn('V293_dly_call_entry', proof)
        self.assertIn('split;[exact Raw|rewrite Raw;discriminate]', proof)

    def test_aux_sensitive_frame_not_transported_without_proof(self):
        source = (R / P).read_text()
        statement = source.split('Theorem V293_dly_body_first_y:', 1)[1].split('Proof.', 1)[0]
        self.assertIn('((ge,le,Mf),ir,(false,si,enabled::ci))', statement)
        self.assertIn('(ge,le,Mf,ir,(enabled,si,ci),O,op)|=', statement)
        probe = (R / Q).read_text().split('Theorem DCactual_critical_post:', 1)[1]
        self.assertIn('(false,nil,[enabled]),DCabs,spec_done None)', probe)
        self.assertIn('change(DCpost Mf enabled);exact Post', probe)
        boundary = read('function-boundary.json')
        self.assertFalse(boundary['full_api_proved'])
        self.assertFalse(boundary['whole_call_global_reachability_proved'])
        self.assertFalse(boundary['raw_entry_connected_to_blocking_switch'])
        self.assertTrue(all(x['located'] and not x['full_target_linked'] for x in boundary['stages'].values()))

    def test_recursive_trust_and_stable_compiles(self):
        roots = []
        for p in [P, Q]:
            source = (R / p).read_text()
            self.assertNotRegex(source, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', source, re.M)]
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
        doc = (R / 'audit/STAGE322_TIME_DELAY_CALL_ENTRY.md').read_text()
        for token in ['不是完整 API', '不是全局记录不变量', '不是全局 ProgSim', '未初始化',
                      '客户端堆', '优先级缓存', 'GOOD_OS', 'uCOS3', '入口辅助状态快照', '不重跑整个 body']:
            self.assertIn(token, doc)
        for name in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / name).read_bytes().endswith((D / (name + '.baseline')).read_bytes()))


if __name__ == '__main__':
    unittest.main()
