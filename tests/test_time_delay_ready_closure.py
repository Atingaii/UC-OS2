"""联合就绪闭合的身份/连线回归；语义由编译和递归 Coq 内核复核。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage326-time-delay-ready-closure'
OLD = R / 'audit/logs/stage325-time-delay-call-global'
P = 'certiucos/v293/proofs/V293TimeDlyReadyClosure.v'
Q = 'audit/probes/V293TimeDlyReadyClosureProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class TimeDelayReadyClosureTests(unittest.TestCase):
    def test_locked_source_replay(self):
        rows = read('source-identities.json')
        self.assertEqual(rows, json.loads((OLD / 'source-identities.json').read_text()))
        self.assertEqual({r['name'] for r in rows}, {'OSTimeDly', 'OS_Sched', 'OS_SchedNew'})
        inventory = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        for r in rows:
            self.assertIn(r, inventory['functions'])
            self.assertEqual(sha(D / (r['name'] + '.source.c.snapshot.txt')), r['source_lines_sha256'])
            self.assertEqual(hashlib.sha256((D / (r['name'] + '.configured.c.snapshot.txt')).read_bytes()[:-1]).hexdigest(),
                             r['preprocessed_definition_sha256'])
        self.assertEqual(read('source-replay.json')['exit'], 0)

    def test_stable_interface_constructs_execution_and_joint_resources(self):
        s = (R / P).read_text()
        statement, proof = s.split('Theorem V293_dly_global_call_ready:', 1)[1].split('Proof.', 1)
        inputs, outputs = statement.split('exists Mf,', 1)
        for token in ['V293_global_steps', 'V293_local_steps', 'cstepstar', 'store ', 'spec_step ', 'V293_ready_full']:
            self.assertNotIn(token, inputs)
        for token in ['get cles t=Some cle', 'fresh M ba', 'fresh M byloc', 'fresh M bs',
                      'V293_dly_call_cells', 'V293_priority_cells bp', 'q<>p', 'get ge OSTCBCur']:
            self.assertIn(token, inputs)
        for token in ['V293_global_steps(pc,(po,pi,ip))(cge,cles,CM)',
                      'scall f[econst32 duration]),(kenil,kstop)', 'scall sched nil',
                      'spec_step sd', 'V293_task_records Mf blocked',
                      'V293_ready_loads Mf', 'V293_ready_full br bg bp(bt,Int.repr base) **',
                      'V293_dly_local_frame']:
            self.assertIn(token, outputs)
        self.assertIn('V293_dly_global_call_to_sched_refines', proof)
        self.assertIn('V293_dly_ready_resources', proof)
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertNotRegex(s, r'Require Import CertiOS\.(?:ucos|os_code|os_proof)\.')

    def test_canonical_records_reuse_and_nonempty_correspondence(self):
        s = (R / P).read_text()
        resources = s.split('Lemma V293_dly_ready_resources', 1)[1].split('Lemma V293_dly_ready_rel_after', 1)[0]
        for token in ['V293_owned_task_records_reassemble', 'V293_ready_payload',
                      'V293_ready_full', 'V293_ready_loads_sub', 'V293_ready_cells_loads',
                      'apply sat_split in Reordered', 'exact Global', 'exact Rel']:
            self.assertIn(token, resources)
        self.assertNotIn('TcbMod.elements', s)
        relation = s.split('Lemma V293_dly_ready_rel_after', 1)[1].split('Theorem V293_dly_global_call_ready', 1)[0]
        for token in ['q<>p', 'V293_bitmap_ready lo hi q', 'V293_ready_clear_membership',
                      'V293_dly_bitmap_tasks', 'V293_tick_priority_table', 'V293_rekey_byte_arithmetic']:
            self.assertIn(token, relation)

    def test_frame_not_dropped_or_duplicated_priority_table(self):
        s = (R / P).read_text()
        frame = s.split('Definition V293_dly_local_frame', 1)[1].split('Lemma V293_dly_ready_resources', 1)[0]
        for token in ['byloc', 'ba', 'Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero)',
                      'V293_dly_guard_cells bi bl', '**R']:
            self.assertIn(token, frame)
        q = (R / Q).read_text()
        residual = q.split('Definition DRframe', 1)[1].split('Definition DRresources', 1)[0]
        self.assertNotIn('V293_priority_cells', residual)
        for token in ['90%positive', '81%positive', '82%positive', '84%positive', '85%positive']:
            self.assertIn(token, residual)
        entry = q.split('Lemma DRentry:', 1)[1].split('Theorem DRglobal_ready:', 1)[0]
        self.assertIn('DAentry false c enabled', entry)
        self.assertIn('OwnershipCellsAppend', entry)

    def test_same_global_call_both_interrupt_states_and_cpu_canary(self):
        s = (R / Q).read_text()
        for token in ['V293_global_steps DAprog DXclient(DXinitial c enabled)',
                      'Theorem DRglobal_ready:forall c enabled,exists Mf,',
                      'V293_dly_global_call_ready', '(DRentry c enabled)',
                      'V293_ready_loads Mf 30%positive 31%positive 83%positive 64 0 DLentries',
                      'Theorem DRboth_IE:', 'DRglobal_ready c false', 'DRglobal_ready c true',
                      'Lemma DRcanary_cpu:', 'V293_bytes_writable Mf 13%positive',
                      'V293_dly_local_frame in Held', 'DCraw_load']:
            self.assertIn(token, s)
        positive = s.split('Theorem DRglobal_ready:', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(positive.split('exists Mf,')[0], 'forall c enabled,')
        self.assertIn('V293_task_records Mf', positive)
        self.assertIn('DRpost c enabled Mf', positive)

    def test_prospective_late_single_factor_gate(self):
        protocol = read('protocol.json')
        self.assertTrue(protocol['prospective'])
        self.assertEqual(sha(D / 'protocol.json'), '60556d7cd8ea64e38bea8c5e0dadac093e4cdd5689cf5be97068204f5f3733b7')
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
        self.assertIn('physical execution/program/heap/resources unchanged', protocol['ablation']['factor'])
        self.assertIn('late abstract/physical correspondence gate only', protocol['ablation']['scope'])
        s = (R / Q).read_text()
        self.assertIn('if commit then DEblocked(Int.repr 3)else DLtasks', s)
        gate = s.split('Theorem DRlate_ablation:', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(gate.count('exists Mf,'), 1)
        for token in ['DRrun c enabled Mf', 'DRpost c enabled Mf', 'V293_ready_loads Mf',
                      'V293_task_records Mf', 'V293_bytes_writable Mf',
                      'V293_bitmap_tasks 64 0(DRchosen_tasks true)',
                      '~V293_bitmap_tasks 64 0(DRchosen_tasks false)']:
            self.assertIn(token, gate)
        negative = s.split('Lemma DRstale_bitmap:', 1)[1].split('Theorem DRlate_ablation:', 1)[0]
        self.assertIn('exists OwnershipReady;exists Vnull;reflexivity', negative)
        self.assertIn('proj2(Bitmap 4', negative)

    def test_recursive_kernel_trust_and_stable_sources(self):
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
        trust = read('trust.json')
        self.assertEqual(len(roots), 9)
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
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

    def test_history_and_precise_noncompletion_boundary(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in read('baseline.json')['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        for n in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / n).read_bytes().endswith((D / (n + '.baseline')).read_bytes()))
        self.assertEqual((R / '_CoqProject').read_bytes(), (D / '_CoqProject.baseline').read_bytes() + (P + '\n').encode())
        self.assertEqual({str(p.relative_to(R)): sha(p) for p in R.rglob('*.pyc')}, read('bytecode-baseline.json'))
        b = read('function-boundary.json')
        self.assertTrue(b['joint_ready_ownership_at_scheduler_entry'])
        self.assertTrue(b['physical_ready_loads_same_heap'])
        for n in ['joint_ownership_across_scheduler_switch', 'full_api_proved', 'priority_cache_synchronized',
                  'resumption_return_proved', 'global_ProgSim_proved', 'GOOD_OS_proved']:
            self.assertFalse(b[n])
        self.assertTrue(all(row['located'] and not any(v for k, v in row.items() if k != 'located')
                            for row in b['stages'].values()))
        doc = (R / 'audit/STAGE326_TIME_DELAY_READY_CLOSURE.md').read_text()
        for token in ['不是完整 API', '不是全局记录不变量', '不是全局 ProgSim', '不是 GOOD_OS',
                      '只在末端对应关系门', '不是修改程序后的完整执行', 'SWINVt', 'uCOS3']:
            self.assertIn(token, doc)


if __name__ == '__main__':
    unittest.main()
