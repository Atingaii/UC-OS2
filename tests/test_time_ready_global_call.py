"""第339步接口回归；数学命题由 Coq 和递归 coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage339-time-ready-global-call'
P = 'certiucos/v293/proofs/V293TimeReadyGlobalCall.v'
Q = 'audit/probes/V293TimeReadyGlobalCallProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class TimeReadyGlobalCallTests(unittest.TestCase):
    def test_protocol_frozen_single_factor(self):
        self.assertEqual((D / 'protocol.sha256').read_text().split(),
                         [sha(D / 'protocol.json'), 'protocol.json'])
        p = read('protocol.json')
        self.assertTrue(p['prospective'])
        self.assertIn('only abstract current-task slot', p['ablation']['factor'])
        self.assertIn('not a mutant operational execution', p['ablation']['scope'])

    def test_real_switch_constructed_not_assumed(self):
        part = (R / P).read_text().split('Theorem V293_time_ready_global_switch :', 1)[1].split('\nQed.', 1)[0]
        pre = part.split('  exists Ms,', 1)[0]
        self.assertNotRegex(pre, r'\b(?:lpstep|store|V293_local_steps|freels)\b')
        self.assertIn('SWINVt(V293_time_ready_inv br bg bp bn)current', pre)
        self.assertIn('eapply pswitch_step', part)
        self.assertIn('destruct(V293_ready_current_write', part)
        self.assertIn('bc tp Held Current Store', part)

    def test_selected_maps_and_same_actual_switch_heap(self):
        p = (R / P).read_text()
        for mode in ['get', 'set']:
            part = p.split(f'Theorem V293_time_switch_source_{mode} :', 1)[1].split('\nQed.', 1)[0]
            pre = part.split('  exists Ms Mc Mf,', 1)[0]
            self.assertIn('current<>next', pre)
            self.assertIn('get T next=Some(curs(scall f ', pre)
            self.assertIn('get les next=Some selected', pre)
            self.assertIn('get au next=Some(enabled,si,ci)', pre)
            self.assertNotRegex(pre, r'\b(?:lpstep|store|V293_local_steps|freels|spec_step)\b')
            self.assertIn('((ge,selected,Ms),ir,(enabled,si,ci))', part)
            self.assertIn('Ms ir enabled si ci(set O curtid(oscurt next))', part)
            self.assertIn('rewrite map_get_set\' by congruence;exact NextCode', part)

    def test_not_claiming_true_IE_has_switch_flags(self):
        p = (R / P).read_text()
        self.assertIn('eapply V293_source_time_entry_core;exact Halves', p)
        for mode in ['get', 'set']:
            part = p.split(f'Theorem V293_time_switch_source_{mode} :', 1)[1].split('Proof.', 1)[0]
            self.assertIn('(ge,selected,Mf,ir,(enabled,si,ci)', part)
            self.assertIn('V293_time_ready_core br bg bp bn ** CurTid next', part)
            self.assertNotIn('SWINVt(V293_time_ready_inv br bg bp bn)next', part)

    def test_nonempty_records_alias_and_both_IE(self):
        q = (R / Q).read_text()
        self.assertIn('Theorem Gfixture_nonempty_canonical_records', q)
        self.assertIn('V293_highest_ready OwnershipTasks OwnershipReady', q)
        self.assertIn('nth 0 GRTentries Vnull=Vptr OwnershipReady', q)
        self.assertIn('nth 4 GRTentries Vnull=Vptr OwnershipReady', q)
        self.assertTrue(read('fixture-plan.json')['prospective'])
        for mode in ['get', 'set']:
            part = q.split(f'Theorem G{mode}_nonempty_both_IE :', 1)[1].split('\nQed.', 1)[0]
            self.assertIn('forall pc ip cst ks selected clock enabled', part)
            self.assertIn('pumerge SRprogram(fun _ => None)', part)
            self.assertIn('get Mf(160%positive,Z.of_nat k)=None /\\get Mf(161%positive,Z.of_nat k)=None', part)
            self.assertIn('eapply SRremoved;exact Freed', part)

    def test_late_current_control_same_real_switch_heap(self):
        q = (R / Q).read_text()
        part = q.split('Theorem Gswitch_stale_current_control :', 1)[1].split('\nQed.', 1)[0]
        self.assertIn('Gswitch pc ip cst ks selected clock enabled 203%Z [] Ms', part)
        self.assertIn('load(Tptr Tvoid)Ms(1%positive,0%Z)=Some(Vptr OwnershipReady)', part)
        self.assertIn('Gstate selected enabled Ms(Gafter clock)V293_time_get_action |= SRcore', part)
        self.assertIn('~ Gstate selected enabled Ms(GTRabstract OwnershipWaiting clock)V293_time_get_action |= SRcore', part)
        self.assertIn('V293_time_ready_current_owned', part)
        self.assertIn('Some(Vptr OwnershipWaiting))in Read.', part)
        self.assertIn('by exact(eq_trans(eq_sym Load)Read). discriminate Same.', part)

    def test_repeated_compile_recursive_trust(self):
        for label, source in [('proof', P), ('probe', Q)]:
            for i in [1, 2]:
                row = read(f'stable-{label}-{i}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / source))
                self.assertEqual(row['source_sha256'], sha(R / source))
        trust = read('trust.json')
        roots = [Path(p).stem + '.' + n for p in [P, Q] for n in
                 re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', (R / p).read_text(), re.M)]
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']),
                             {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        for p in [P, Q]:
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
        self.assertNotIn('Require Import CertiOS.audit.', (R / P).read_text())

    def test_old_inputs_and_append_only_project(self):
        self.assertEqual([p for p, h in read('baseline.json').items()
                          if not (R / p).is_file() or sha(R / p) != h], [])
        old = json.loads((R / 'audit/logs/stage338-time-source-ready-call/checkpoint-evidence-manifest.json').read_text())
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject'}
        self.assertEqual([p for p, row in old.items() if p not in mutable
                          and sha(R / p) != row['sha256']], [])
        self.assertEqual((R / '_CoqProject').read_bytes(),
                         (D / '_CoqProject.baseline').read_bytes() + (P + '\n').encode())
        for n in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / n).read_bytes().endswith((D / (n + '.baseline')).read_bytes()))

    def test_reused_source_connection_not_fresh_replay_claim(self):
        e = json.loads((R / 'audit/time-ready-global-call-evidence-stage339.json').read_text())
        self.assertFalse(e['full_target_linked'])
        self.assertEqual(e['source_correspondence']['mode'], 'reuse_frozen_not_fresh_replay')
        for p, h in e['inputs'].items():
            self.assertEqual(sha(R / p), h)

    def test_bounded_documentation_and_adversarial_findings(self):
        doc = (R / 'audit/STAGE339_TIME_READY_GLOBAL_CALL.md').read_text()
        for term in ['不是经验证C前端', 'ADR0005', '不是运行时突变程序', 'GOOD_OS', 'K1–K4',
                     'uCOS3', '两个CPU hook仍缺实现', '总目标保持active', '旧覆盖清单不改写',
                     '不是规范初始化表', '尚不是连续全局调用轨迹']:
            self.assertIn(term, doc)
        self.assertTrue(read('adversarial-review.json')['completed'])
