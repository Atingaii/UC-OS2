"""第340步连接边界回归；数学命题由Coq及递归coqchk检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage340-time-continuous-global'
P = 'certiucos/v293/proofs/V293TimeContinuousGlobal.v'
Q = 'audit/probes/V293TimeContinuousGlobalProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())
part = lambda s, n: s.split(n + ' :', 1)[1].split('\nQed.', 1)[0]


class TimeContinuousGlobalTests(unittest.TestCase):
    def test_prospective_single_client_binding_factor(self):
        self.assertEqual((D / 'protocol.sha256').read_text().split(),
                         [sha(D / 'protocol.json'), 'protocol.json'])
        protocol = read('protocol.json')
        self.assertTrue(protocol['prospective'])
        self.assertIn('only selected task binding', protocol['ablation']['factor'])
        self.assertIn('call-boundary rejection only', protocol['ablation']['scope'])

    def test_stable_interfaces_construct_full_global_calls(self):
        p = (R / P).read_text()
        for mode in ['get', 'set']:
            s = part(p, 'Theorem V293_time_switch_global_' + mode)
            pre = s.split('  exists Ms Mc Mf,', 1)[0]
            self.assertIn('get cles next=Some cle', pre)
            self.assertIn('SWINVt(V293_time_ready_inv br bg bp bn)current', pre)
            self.assertNotRegex(pre, r'\b(?:lpstep|store|freels|spec_step|V293_global_steps|V293_local_steps)\b')
            self.assertIn('(T,(ge,les,M,ir,au),current)', s)
            self.assertIn('(ge,les,Mf,ir,au),next)', s)
            self.assertIn('V293_source_time_' + mode + '_global', s)
            self.assertIn('eapply V293_time_global_switch_then', s)

    def test_real_client_and_os_boundaries(self):
        p = (R / P).read_text()
        self.assertIn('eapply V293_client_unchanged_global', p)
        self.assertIn('V293_client_no_os_context', p)
        for mode in ['get', 'set']:
            s = part(p, 'Lemma V293_time_' + mode + '_global_entry')
            self.assertIn('get cles t=Some cle', s)
            self.assertIn('sfexec_step', s)
            self.assertIn('kcall f', s)
        ret = part(p, 'Lemma V293_time_global_return')
        self.assertIn('eapply sfreeend_step', ret)
        self.assertIn('V293_time_freels_value', ret)
        self.assertIn('((ge,caller,Mf),ir,aux)', ret)

    def test_same_heap_critical_spec_and_free(self):
        p = (R / P).read_text()
        for mode in ['get', 'set']:
            s = part(p, 'Theorem V293_source_time_' + mode + '_global')
            self.assertIn("rewrite Zero in Zero';inversion Zero';subst Mz'", s)
            self.assertIn("rewrite Copy in Copy';inversion Copy';subst Mc'", s)
            self.assertIn('V293_time_' + mode + '_body_refinement', s)
            self.assertIn('V293_time_global_copy', s)
            self.assertIn('spec_step sd', s)
            self.assertIn('freels(getaddr(V293_time_call_locals ticks saved bt bs))Mc Mf', s)

    def test_actual_switch_maps_not_synthetic_enclosure(self):
        s = part((R / P).read_text(), 'Lemma V293_time_global_switch_then')
        for x in ['TasksMod.get_set_same', 'CltEnvMod.get_set_same', 'TaskLStMod.get_set_same',
                  'current<>next', 'get T next=Some C', 'get les next=Some selected',
                  'get au next=Some(enabled,si,ci)', 'eapply rt1n_trans with(y:=']:
            self.assertIn(x, s)
        self.assertIn('exact Switch | exact Call', s)

    def test_nonempty_separate_client_heap_and_both_IE(self):
        q = (R / Q).read_text()
        for mode in ['get', 'set']:
            s = part(q, 'Theorem CG' + mode + '_nonempty_both_IE')
            self.assertIn('forall pc ip cge cles CM cle selected clock enabled', s)
            self.assertIn('get cles OwnershipReady=Some cle', s)
            self.assertIn('CGtrace pc ip(cge,cles,CM)', s)
            self.assertIn('get Mf(160%positive,Z.of_nat k)=None /\\get Mf(161%positive,Z.of_nat k)=None', s)
        self.assertIn('Corollary CGget_set_client_witness', q)
        self.assertIn('cge,sig OwnershipReady (emp:env),CM', q)
        self.assertNotIn('cge,cles,GTRmemory', q)

    def test_single_factor_rejection_retains_identical_switch_heap(self):
        s = part((R / Q).read_text(), 'Theorem CGmissing_client_single_factor')
        self.assertIn('Gswitch pc ip(cge,cles,CM)', s)
        self.assertIn('Gswitch pc ip(cge,del cles OwnershipReady,CM)', s)
        self.assertIn("rewrite Store in Store';inversion Store';subst Ms'", s)
        self.assertIn('t<>OwnershipReady ->get(del cles OwnershipReady)t=get cles t', s)
        self.assertIn('~ltstep', s)
        self.assertIn('V293_time_missing_client_binding', s)
        self.assertNotIn('~lpstep', s)

    def test_repeated_compile_and_recursive_trust(self):
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
        self.assertEqual(trust['roots_printed'], 17)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']),
                             {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        for path in [P, Q]:
            self.assertEqual(read('trust-inputs.json')[path], sha(R / path))
            self.assertNotRegex((R / path).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
        self.assertNotIn('Require Import CertiOS.audit.', (R / P).read_text())

    def test_old_evidence_and_single_project_append(self):
        self.assertEqual([p for p, h in read('baseline.json').items()
                          if not (R / p).is_file() or sha(R / p) != h], [])
        previous = json.loads((R / 'audit/logs/stage339-time-ready-global-call/checkpoint-evidence-manifest.json').read_text())
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject'}
        self.assertEqual([p for p, row in previous.items() if p not in mutable
                          and sha(R / p) != row['sha256']], [])
        self.assertEqual((R / '_CoqProject').read_bytes(),
                         (D / '_CoqProject.baseline').read_bytes() + (P + '\n').encode())
        for n in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / n).read_bytes().endswith((D / (n + '.baseline')).read_bytes()))

    def test_bounded_claims_and_frozen_source_provenance(self):
        e = json.loads((R / 'audit/time-continuous-global-evidence-stage340.json').read_text())
        self.assertFalse(e['full_target_linked'])
        self.assertEqual(e['source_correspondence']['mode'], 'reuse_frozen_not_fresh_replay')
        for p, h in e['inputs'].items():
            self.assertEqual(sha(R / p), h)
        doc = (R / 'audit/STAGE340_TIME_CONTINUOUS_GLOBAL.md').read_text()
        for term in ['不是经验证C前端', 'ADR0005', '入口早拒绝', 'GOOD_OS', 'K1–K4',
                     'uCOS3', '两个CPU hook仍缺实现', '总目标保持active', '旧覆盖清单不改写',
                     '不是规范初始化表', '不是任意交错', '客户端内存CM']:
            self.assertIn(term, doc)
        self.assertTrue(read('adversarial-review.json')['completed'])
