"""真实切换的资源连线与身份回归；语义由 Coq 和递归 coqchk 验证。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage328-ready-owned-global-switch'
OLD = R / 'audit/logs/stage327-ready-owned-sched-call'
P = 'certiucos/v293/proofs/V293ReadyOwnedGlobalSwitch.v'
Q = 'audit/probes/V293ReadyOwnedGlobalSwitchProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class ReadyOwnedGlobalSwitchTests(unittest.TestCase):
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

    def test_owned_interface_constructs_store_and_actual_step(self):
        s = (R / P).read_text()
        st, pf = s.split('Theorem V293_owned_global_switch :', 1)[1].split('Proof.', 1)
        inputs, outputs = st.split('exists Mf,', 1)
        for token in ['lpstep', 'store(', 'V293_global_steps', 'cstepstar']:
            self.assertNotIn(token, inputs)
        for token in ['get les next=Some le\'', "get au next=Some(ie',is,cs')", 'GoodInvAsrt R',
                      'SWINVt(V293_ready_inv br bg bp)current **R']:
            self.assertIn(token, inputs)
        for token in ['lpstep', 'store(Tptr tp)M', 'V293_ready_full br bg bp next **R',
                      'set O curtid(oscurt next)', 'get Mf(c,i)=get M(c,i)']:
            self.assertIn(token, outputs)
        for token in ['V293_ready_switch_step', 'V293_owned_switch_active_view']:
            self.assertIn(token, pf)
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertNotRegex(s, r'Require Import CertiOS\.(?:ucos|os_code|os_proof)\.')

    def test_same_global_prefix_and_joint_heap(self):
        s = (R / Q).read_text()
        st, pf = s.split('Theorem DGglobal_switch:', 1)[1].split('Proof.', 1)
        self.assertEqual(st.split('exists bs')[0], 'forall c enabled,')
        for token in ['DXrun c enabled bs Mcut', 'DOpost c enabled bs Mcut',
                      'free Tint8 byblock My=Some Mh', 'get Mh(byblock,0%Z)=None',
                      'V293_global_steps DAprog DXclient', 'lpstep DAprog DAtasks DXclient',
                      'store(Tptr V293_tcb_type)Mcut', 'DGpost c bs Mf']:
            self.assertIn(token, st)
        for token in ['DOglobal_sched c enabled', 'V293_owned_global_switch',
                      'DGframe_good c bs', 'DXcut_exact', 'V293_global_trans', 'exact Switch']:
            self.assertIn(token, pf)
        self.assertNotIn('DXglobal_switch', pf)
        self.assertIn('exact(proj1 DXhigh_switch)', s)

    def test_active_aux_is_not_old_disabled_snapshot(self):
        p, q = (R / P).read_text(), (R / Q).read_text()
        self.assertIn('forall le\' ie\' cs\'', p)
        self.assertIn('good_inv_prop', p)
        self.assertIn('V293_owned_ready_good', p)
        post = q.split('Definition DGpost', 1)[1].split('Lemma DGframe_good', 1)[0]
        for token in ['DCle', '(true,nil,nil)', 'DGabs', 'V293_ready_full', 'OwnershipWaiting **DGframe c bs']:
            self.assertIn(token, post)
        self.assertNotIn('SWINVt', post)
        self.assertIn('Theorem DGactive_not_disabled:', q)
        self.assertIn('astar_l_aie_elim', q)

    def test_observations_both_ie_wrap_and_separate_heaps(self):
        q = (R / Q).read_text()
        for token in ['Lemma DGobserved:', 'Theorem DGboth_IE:', 'DGglobal_switch c false',
                      'DGglobal_switch c true', 'Theorem DGwrap:', 'DWcounter_wrap',
                      'V293_bytes_writable M bs 0%Z 4', 'V293_bytes_writable M 13%positive 0%Z 4',
                      'Theorem DGdistinct_heaps:', 'Vint32(Int.repr 3)', 'Vint32(Int.repr 99)',
                      'V293_tick_raw_owned_writable']:
            self.assertIn(token, q)

    def test_prospective_pointer_commit_fragment_ablation(self):
        protocol = read('protocol.json')
        self.assertTrue(protocol['prospective'])
        self.assertEqual(sha(D / 'protocol.json'), 'c75fb6579e422d30551e3e61ccdc8d64a811b2dd54b83bfa6d841274b3426b64')
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
        self.assertEqual(protocol['ablation']['factor'], 'neutralize only the physical current-pointer commit at the final switch fragment')
        self.assertIn('no claimed mutant global switch execution', protocol['ablation']['scope'])
        q = (R / Q).read_text()
        st, pf = q.split('Theorem DGpointer_commit_ablation:', 1)[1].split('Proof.', 1)
        for token in ['DXrun c enabled bs Mcut', 'DOpost c enabled bs Mcut', 'DGpost c bs Mf',
                      '~DGpost c bs Mcut', 'Some(Vptr OwnershipReady)', 'Some(Vptr OwnershipWaiting)',
                      'Vint32(Int.add c Int.one)', 'Vint32(Int.repr 99)', 'V293_bytes_writable Mcut bs',
                      'V293_bytes_writable Mf bs', 'free Tint8 byblock My=Some Mh']:
            self.assertIn(token, st)
        for token in ['DGcurrent', 'rewrite Before in Load;discriminate', 'DOobserved', 'DGobserved']:
            self.assertIn(token, pf)

    def test_recursive_trust_and_stable_sources(self):
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
        trust = read('trust.json')
        self.assertEqual(len(roots), 12)
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], 12)
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
        project = (R / '_CoqProject').read_bytes()
        self.assertTrue(project.startswith((D / '_CoqProject.baseline').read_bytes() + (P + '\n').encode()))
        self.assertEqual(project.splitlines().count(P.encode()), 1)
        self.assertEqual({str(p.relative_to(R)): sha(p) for p in R.rglob('*.pyc')}, read('bytecode-baseline.json'))
        b = read('function-boundary.json')
        for n in ['joint_ownership_across_actual_switch', 'active_selected_view', 'both_initial_IE', 'same_raw_global_client_call']:
            self.assertTrue(b[n])
        for n in ['full_api_proved', 'priority_cache_synchronized', 'resumption_return_proved',
                  'global_ProgSim_proved', 'GOOD_OS_proved', 'final_helper_block_fresh_proved']:
            self.assertFalse(b[n])
        self.assertTrue(all(row['located'] and not any(v for k, v in row.items() if k != 'located')
                            for row in b['stages'].values()))
        doc = (R / 'audit/STAGE328_READY_OWNED_GLOBAL_SWITCH.md').read_text()
        for token in ['不是完整 API', '不是全局记录不变量', '不是全局 ProgSim', '不是 GOOD_OS',
                      '不是突变程序的完整全局执行', 'GoodInvAsrt R', 'IE=true', 'Mh', 'uCOS3']:
            self.assertIn(token, doc)


if __name__ == '__main__':
    unittest.main()
