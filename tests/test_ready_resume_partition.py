"""完整就绪资源分割及恢复后缀的接口/证据回归；语义另由 Coq 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage329-ready-resume-partition'
OLD = R / 'audit/logs/stage328-ready-owned-global-switch'
P = 'certiucos/v293/proofs/V293ReadyResumePartition.v'
Q = 'audit/probes/V293ReadyResumePartitionProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class ReadyResumePartitionTests(unittest.TestCase):
    def test_fixed_source_replayed(self):
        rows = read('source-identities.json')
        self.assertEqual(rows, json.loads((OLD / 'source-identities.json').read_text()))
        self.assertEqual(read('source-replay.json')['exit'], 0)
        inv = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        for row in rows:
            self.assertIn(row, inv['functions'])
            self.assertEqual(sha(D / (row['name'] + '.source.c.snapshot.txt')), row['source_lines_sha256'])
            self.assertEqual(hashlib.sha256((D / (row['name'] + '.configured.c.snapshot.txt')).read_bytes()[:-1]).hexdigest(),
                             row['preprocessed_definition_sha256'])

    def test_exact_full_ownership_partition_keeps_frame(self):
        s = (R / P).read_text()
        self.assertIn('V293_ready_full br bg bp t <==> C **CurTid t', s)
        st, pf = s.split('Theorem V293_ready_full_runtime_partition :', 1)[1].split('Proof.', 1)
        self.assertIn('V293_ready_full br bg bp t **R ->', st)
        self.assertIn('(INV G **RDYINV G t) **R', st)
        self.assertIn('enabled=false ->gettopis si<=INUM', st)
        self.assertIn('proj1(V293_ready_full_core_halves t st)', pf)
        self.assertIn('V293_ready_resume_invariants', pf)
        self.assertIn('Let G:=V293_ready_inv br bg bp.', s)
        self.assertNotIn('Definition', s)
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertNotRegex(s, r'Require Import CertiOS\.(?:ucos|os_code|os_proof)\.')

    def test_universal_restored_callback_without_execution_premise(self):
        s = (R / P).read_text()
        pending = s.split('Theorem V293_ready_full_pending_TaskSim :', 1)[1].split('Proof.', 1)[0]
        inputs, outputs = pending.split(' TaskSim', 1)
        for token in ['cstep', 'lpstep', 'V293_global_steps', 'TaskSim']:
            self.assertNotIn(token, inputs)
        for token in ['V293_skip_client_state', 'Amapsto(b,0%Z)Tint32 true v **V293_ready_full',
                      'po f=Some(tau,d1,d2,body)']:
            self.assertIn(token, inputs)
        self.assertIn('kseq(sprim excrit)(kseq sret(kcall f body caller tail))', outputs)
        callback, proof = s.split('Theorem V293_ready_full_resume_callback :', 1)[1].split('Proof.', 1)
        self.assertIn("forall Mc Oc o' O',", callback)
        self.assertIn('SWINVt G t', callback)
        self.assertIn("join Ol Oc O'", callback)
        self.assertIn('joinmem', callback)
        self.assertIn('V293_resume_high_done', proof)
        self.assertIn('V293_ready_full_pending_TaskSim', proof)
        self.assertIn('V293_invariant_pending_TaskSim', s)

    def test_original_global_heap_disjoint_pieces_and_satp(self):
        s = (R / Q).read_text()
        st, pf = s.split('Theorem DRglobal_partition_pieces:', 1)[1].split('Proof.', 1)
        self.assertEqual(st.split('exists bs')[0], 'forall c enabled,')
        for token in ['V293_global_steps DAprog DXclient', 'DGpost c bs M',
                      'join Mt Mr Mtail', 'join Ms Mtail M', 'join Ot Or Otail',
                      'join Os Otail DGabs', 'satp', '(INV DRG)',
                      '(RDYINV DRG OwnershipWaiting)', '~(Ms=(emp:mem) /\Os=(emp:osabst))']:
            self.assertIn(token, st)
        for token in ['INV_irrev_prop', 'V293_return_ready_all_operations',
                      'V293_ready_enabled_empty_rejected', 'DRglobal_partition c enabled']:
            self.assertIn(token, pf)
        self.assertIn('DGglobal_switch c enabled', s)
        self.assertIn('Theorem DRboth_IE:', s)

    def test_nonempty_suffix_fixture_has_explicit_context_boundary(self):
        s = (R / Q).read_text()
        st, pf = s.split('Theorem DRrestored_suffix:', 1)[1].split('Proof.', 1)
        self.assertEqual(st.split('exists bs')[0], 'forall c top,')
        for token in ['DXrun c top bs Mcut', 'DOpost c top bs Mcut', 'join Mt Mr Mcut',
                      'join Ot Or(DEfinalabs(Int.repr 3))', 'DRrest c', 'TaskSim DAprog',
                      'DCle kstop', 'DWhighprog', 'OwnershipReady']:
            self.assertIn(token, st)
        self.assertNotIn('DAcontinuation', st)
        self.assertIn('not the nested DAcontinuation', s)
        self.assertIn('DOglobal_sched c top', pf)
        self.assertIn('V293_ready_full_pending_TaskSim', pf)
        self.assertIn('V293_owned_record_cells(DOcells c)', s)

    def test_prospective_resource_placement_ablation_is_late(self):
        protocol = read('protocol.json')
        self.assertTrue(protocol['prospective'])
        self.assertEqual(sha(D / 'protocol.json'), '99f2f3a83df73f5eb627f1cc8178209b1a2d6d7d36f03139a3c4873ee8f0ca19')
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
        self.assertIn('leaving shared INV heap/abstract state empty', protocol['ablation']['factor'])
        self.assertIn('not a mutant execution', protocol['ablation']['scope'])
        s = (R / Q).read_text()
        st, pf = s.split('Theorem DRenabled_placement_ablation:', 1)[1].split('Proof.', 1)
        for token in ['V293_global_steps DAprog DXclient', 'DGpost c bs M', 'DRpartition c bs M',
                      'In(a,tp,v)(DOcells c)', 'V293_bytes_writable M bs 0%Z 4',
                      'V293_bytes_writable M 13%positive 0%Z 4', '(true,nil,nil)',
                      '(emp:mem)', '(emp:osabst)', '~((DWge']:
            self.assertIn(token, st)
        self.assertIn('DRglobal_partition c enabled', pf)
        self.assertIn('V293_ready_enabled_empty_rejected', pf)

    def test_recursive_trust_and_stable_sources(self):
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
        trust = read('trust.json')
        self.assertEqual(len(roots), 14)
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], 14)
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
        self.assertEqual({str(p.relative_to(R)): sha(p) for p in R.rglob('*.pyc')}, read('bytecode-baseline.json'))
        b = read('function-boundary.json')
        for n in ['selected_full_runtime_partition', 'same_actual_global_heap',
                  'universal_restored_suffix_TaskSim', 'both_saved_IE', 'unchanged_external_frame']:
            self.assertTrue(b[n])
        for n in ['full_api_proved', 'priority_cache_synchronized', 'actual_old_task_resumption_proved',
                  'actual_nested_OSTimeDly_return_proved', 'global_ProgSim_proved', 'GOOD_OS_proved']:
            self.assertFalse(b[n])
        self.assertTrue(all(row['located'] and not any(v for k, v in row.items() if k != 'located')
                            for row in b['stages'].values()))
        doc = (R / 'audit/STAGE329_READY_RESUME_PARTITION.md').read_text()
        for token in ['不是完整 API', '不是全局 ProgSim', '不是 GOOD_OS',
                      '不是旧任务恢复可达性', '不是实际嵌套返回', 'IE=true', 'kstop', 'uCOS3']:
            self.assertIn(token, doc)


if __name__ == '__main__':
    unittest.main()
