"""真实嵌套返回的接口和证据回归；执行语义由 Coq 内核检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage330-time-delay-nested-return'
OLD = R / 'audit/logs/stage329-ready-resume-partition'
P = 'certiucos/v293/proofs/V293TimeDlyNestedReturn.v'
Q = 'audit/probes/V293TimeDlyNestedReturnProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class TimeDelayNestedReturnTests(unittest.TestCase):
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

    def test_public_bridge_has_no_execution_or_simulation_input(self):
        s = (R / P).read_text()
        st, pf = s.split('Theorem V293_ready_nested_return_TaskSim :', 1)[1].split('Proof.', 1)
        inputs, output = st.split(' TaskSim', 1)
        for token in ['cstep', 'lpstep', 'V293_global_steps', 'TaskSim']:
            self.assertNotIn(token, inputs)
        for token in ['po f=Some(tau,d1,d2,body)', 'po fd=Some(taud,e1,e2,bodyd)',
                      'getaddr outer=V293_return_addresses cells', 'GoodInvAsrt F',
                      'V293_skip_client_state', 'V293_ready_full br bg bp t **F']:
            self.assertIn(token, inputs)
        self.assertIn('kcall f body outer(kseq sret(kcall fd bodyd client tail))', output)
        self.assertIn('RDYINV', output)
        self.assertIn('V293_nested_return_suffix', pf)
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertNotRegex(s, r'Require Import CertiOS\.(?:ucos|os_code|os_proof)\.')

    def test_generic_owned_cells_drive_actual_free(self):
        s = (R / P).read_text()
        for token in ['map(fun cell=>let', 'Lemma V293_nested_free_successor',
                      'Lemma V293_owned_frees_TaskSim', 'Lemma V293_owned_return_TaskSim',
                      'Lemma V293_owned_freels', 'Lemma V293_owned_return_execution',
                      'Lemma V293_nested_freels_removed', 'join_free', 'free_mono',
                      'sfree_step', 'sfreeend_step', 'sret_step']:
            self.assertIn(token, s)
        st = s.split('Lemma V293_nested_freels_removed :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('freels', st)
        self.assertIn('get Mf(b,Z.of_nat k)=None', st)
        self.assertIn('k<typelen tp', st)

    def test_nonempty_same_prefix_heap_exact_nested_context(self):
        s = (R / Q).read_text()
        st, pf = s.split('Theorem DNnested_TaskSim:', 1)[1].split('Proof.', 1)
        self.assertEqual(st.split('exists bs')[0], 'forall c top,')
        for token in ['DXrun c top bs M', 'DOpost c top bs M', 'DNowned c top bs M',
                      'TaskSim DAprog(SKIP,(kenil,DAcontinuation))', 'DNframe c', 'OwnershipReady']:
            self.assertIn(token, st)
        self.assertIn('V293_ready_nested_return_TaskSim', pf)
        self.assertIn('DOglobal_sched c top', s)
        self.assertIn('getaddr DCle=V293_return_addresses DNcells', s)
        self.assertIn('get(fst(fst(DXfinal top bs M)))OwnershipReady', s)
        for block in [11, 12, 13]:
            self.assertIn(f'(({block}%positive,0%Z)', s)

    def test_actual_release_preserves_frame_and_restores_client(self):
        s = (R / Q).read_text()
        st, pf = s.split('Theorem DNrelease:', 1)[1].split('Proof.', 1)
        self.assertEqual(st.split('exists Mi')[0], 'forall c top bs M,DNowned c top bs M ->')
        for token in ['free Tint32 bs M=Some Mi', 'freels(V293_return_addresses DNcells)Mi Mf',
                      'V293_local_steps DAprogram(SKIP,(kenil,DAcontinuation))',
                      '(SKIP,(kenil,kstop))', '(emp:env)', '(top,nil,nil)',
                      'V293_ready_full 30%positive 31%positive 83%positive OwnershipReady **DNframe c',
                      'load Tint32 Mi(12%positive,0%Z)=Some(Vint32(Int.repr 3))',
                      '((bs,Tint32)::V293_return_addresses DNcells)']:
            self.assertIn(token, st)
        self.assertIn('V293_owned_return_execution', pf)
        self.assertIn('V293_nested_freels_removed', pf)

    def test_prospective_outer_free_ablation_is_late(self):
        protocol = read('protocol.json')
        self.assertTrue(protocol['prospective'])
        self.assertEqual(sha(D / 'protocol.json'), '8b4b6fe4f51782b43140090f333dbd5d42db40c596bc766d4a62e212329c8555')
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
        self.assertIn('only outer return/free', protocol['ablation']['factor'])
        self.assertIn('not mutant global resumption', protocol['ablation']['scope'])
        st, pf = (R / Q).read_text().split('Theorem DNouter_free_ablation:', 1)[1].split('Proof.', 1)
        for token in ['DXrun c top bs M', 'DNowned c top bs M', 'free Tint32 bs M=Some Mi',
                      'freels(V293_return_addresses DNcells)Mi Mf', 'get Mf(b,Z.of_nat k)=None',
                      '~(forall b tp k', 'get Mi(b,Z.of_nat k)=None']:
            self.assertIn(token, st)
        self.assertIn('DNrelease c top bs M Owned', pf)
        self.assertIn('rewrite Empty in Late;discriminate', pf)

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
        for n in ['resource_conditional_actual_nested_return_TaskSim', 'same_actual_prefix_heap',
                  'actual_nested_local_return_execution', 'both_saved_IE', 'unchanged_external_frame']:
            self.assertTrue(b[n])
        for n in ['full_api_proved', 'priority_cache_synchronized', 'actual_old_task_resumption_proved',
                  'global_ProgSim_proved', 'GOOD_OS_proved']:
            self.assertFalse(b[n])
        self.assertTrue(all(row['located'] and not any(v for k, v in row.items() if k != 'located')
                            for row in b['stages'].values()))
        doc = (R / 'audit/STAGE330_TIME_DELAY_NESTED_RETURN.md').read_text()
        for token in ['不是完整 API', '不是全局 ProgSim', '不是 GOOD_OS',
                      '不是旧任务恢复可达性', 'DAcontinuation', 'DNframe', 'uCOS3']:
            self.assertIn(token, doc)


if __name__ == '__main__':
    unittest.main()
