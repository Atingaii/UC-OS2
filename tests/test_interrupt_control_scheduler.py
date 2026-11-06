"""局部控制/全局调度桥；文本检查仅护栏，证明结论以递归 Coq 复核为准。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage309-control-scheduler'
P = 'certiucos/v293/proofs/V293InterruptControlScheduler.v'
Q = 'audit/probes/V293InterruptControlSchedulerProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class ControlSchedulerTests(unittest.TestCase):
    def test_local_exact_and_explicit_original_scheduler(self):
        s = (R / P).read_text()
        for text in ['V293_control_run_local_exact', 'V293_control_run_legacy_exact',
                     'Some(old,next)', 'sd O next', 'get O curtid=Some(oscurt old)',
                     'V293_control_switch_target_exact', 'V293_control_switch_target_unique',
                     'V293_highest_unique']:
            self.assertIn(text, s)
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertNotIn('Definition V293_scheduler', s)

    def test_switch_projects_original_hpstep_and_frames(self):
        s = (R / P).read_text()
        bridge = s.split('Theorem V293_control_switch_hpstep :', 1)[1].split('Qed.', 1)[0]
        pre, proof = bridge.split('Proof.', 1)
        for text in ['eapply hswi_step', 'V293_control_run_switch_exact', 'map_get_set\'']:
            self.assertIn(text, proof)
        for text in ['c\'=c', 'key<>curtid', 'other<>old',
                     'get T old=Some(curs(hapi_code a),(ke,ks))']:
            self.assertIn(text, pre)
        self.assertNotIn('hpstep', pre.split(' ->')[0])

    def test_removal_control_and_same_fixed_handler(self):
        s = (R / P).read_text()
        for text in ['spec_step_tidsame', 'V293_control_without_switch_current',
                     'V293_control_handler_quiet', 'V293_control_handler_switch',
                     'V293_control_handler_self']:
            self.assertIn(text, s)
        q = (R / Q).read_text()
        for text in ['CSsame_handler_branches', 'CSwithout_switch_cannot_complete',
                     'CSwrong_target_rejected', 'SXnot_highest']:
            self.assertIn(text, q)
        self.assertNotRegex(q, r'CCspec|QCspec')

    def test_nonempty_actual_prefix_then_original_global_step(self):
        s = (R / Q).read_text()
        theorem = s.split('Theorem CScompleted_coupling :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('forall enabled ci cst,exists bs Mf', theorem)
        self.assertRegex(theorem, r'^\s*forall enabled ci cst,exists bs Mf,\s*CSsource_run')
        self.assertLess(theorem.index('SXcomplete_prefix'), theorem.index('V293_control_switch_hpstep'))
        for text in ['CSsource_capture', 'CSsource_run', 'Some(Vptr OwnershipReady)',
                     'Some(Vint32(Int.repr 20))', 'get CSTnext OwnershipReady=Some CSready',
                     'get CSTnext OwnershipWaiting=Some CSafter', 'CSquiet_actual_return',
                     'QEnonempty_execution', 'CSke:=keop1', 'CSks:=kseq',
                     'set(set emp OwnershipReady CSready)OwnershipWaiting CSbefore']:
            self.assertIn(text, s)
        self.assertNotIn('Definition SXprogram', s)

    def test_recursive_trust_and_stable_source_identity(self):
        t = read('trust.json')
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots.extend(Path(p).stem + '.' + n for n in
                         re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M))
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 19)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in t['commands']))
        self.assertLessEqual(set(t['assumptions']), {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})

    def test_single_completed_current_observation_factor(self):
        p = read('ablation-protocol.json')
        a = read('ablation-results.json')
        self.assertTrue(a['passed'] and a['not_program_deletion'])
        base = (D / 'observation-base-01.v.snapshot.txt').read_text()
        mutant = (D / 'observation-mutant-01.v.snapshot.txt').read_text()
        self.assertEqual(base.count(p['old']), 1)
        self.assertEqual(base.replace(p['old'], p['new']), mutant)
        self.assertEqual(read('observation-base-01.json')['exit'], 0)
        self.assertEqual(read('observation-mutant-01.json')['exit'], 1)
        log = (D / 'observation-mutant-01.log').read_text()
        for text in ['Exec : CSsource_run', 'Target : load', 'Captured :', 'Run :',
                     'Global : hpstep', 'OldCode :', 'ReadyCode :', 'The term "Observed" has type']:
            self.assertIn(text, log)
        self.assertEqual(p['production_sha256'], sha(R / P))
        self.assertEqual(p['probe_sha256'], sha(R / Q))

    def test_history_preserved_and_future_appends_allowed(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in read('baseline.json')['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        for name in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / name).read_bytes().endswith((D / (name + '.baseline')).read_bytes()))
        project = (R / '_CoqProject').read_bytes()
        self.assertTrue(project.startswith((D / '_CoqProject.baseline').read_bytes() + b'\n' + P.encode() + b'\n'))
        self.assertEqual(project.decode().splitlines().count(P), 1)
        self.assertEqual({str(p.relative_to(R)): sha(p) for p in R.rglob('*.pyc')}, read('bytecode-baseline.json'))
        for name in ['protocol', 'ablation-protocol']:
            self.assertEqual((D / (name + '.sha256')).read_text().split(), [sha(D / (name + '.json')), name + '.json'])


if __name__ == '__main__':
    unittest.main()
