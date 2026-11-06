"""quiet 精确调度连接；文本/算术回归不替代 Coq 与整核证明。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage299-quiet-sched-bridge'
P = 'certiucos/v293/proofs/V293InterruptQuietSched.v'
Q = 'audit/probes/V293InterruptQuietSchedProbe.v'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read(name):
    return json.loads((D / name).read_text())


class QuietSchedTests(unittest.TestCase):
    def test_actual_builder_and_exact_spec(self):
        s = (R / P).read_text()
        contract = s.split('Theorem V293_interrupt_quiet_sched_builder :', 1)[1].split('Proof.', 1)[0]
        for word in ['intspec i=Some(sched;;spec_done None)', 'BuildintPre', 'BuildintRet',
                     r'(pre //\\ filter) //\\ V293_irq_sched_self_guard',
                     'V293_irq_source_wrapper', 'Spec enter=Some(efp,efq', 'Spec exit=Some(xfp,xfq']:
            self.assertIn(word, contract)
        self.assertNotRegex(contract, r'\b(?:snapshot|cstep|TaskSim|forall j)\b')
        self.assertIn('V293_irq_quiet_builder_open', s)
        self.assertIn('V293_interrupt_quiet_partial_snapshot', s)
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertNotIn('spec_choice', s)

    def test_guard_is_same_state_not_extra_ownership(self):
        s = (R / P).read_text()
        for word in ['Lemma V293_irq_sched_self_guard_sound :',
                     'Lemma V293_irq_sched_self_guard_complete :',
                     'sched_self V293_scheduler(getabst st)',
                     'V293_highest_ready tasks ct', 'absinfer_sched\'',
                     'absinfer_seq\'', 'absinfer_seq_end\'']:
            self.assertIn(word, s)
        self.assertIn(r'(<||sched;;aop||> **P) //\\ V293_irq_sched_self_guard', s)
        self.assertNotIn('** V293_irq_sched_self_guard', s)

    def test_typed_nonempty_wrapper_and_negative_controls(self):
        s = (R / Q).read_text()
        for name in ['QSentry_nonempty', 'QSfiltered_nonempty', 'QStyped_pair',
                     'QSbuilders', 'QSactual_wrapper', 'QScommon_environment',
                     'QSnegative_nonempty', 'QSguard_ablation',
                     'QSabstract_current_only', 'QSprecise_steps']:
            self.assertIn('Theorem ' + name + ' :', s)
        self.assertIn('SCmemory 1 Int.zero Int.zero', s)
        self.assertIn('SCmemory 255 Int.zero Int.zero', s)
        self.assertIn('SCheap_data nest Int.zero Int.zero', s)
        self.assertIn('destruct(QJfiltered_nonempty nest Positive Bound)', s)
        self.assertIn('QCstate M O|=QJpre /\\~QCstate M O|=V293_irq_sched_self_guard', s)
        self.assertIn('InfRules BDspec V293_scheduler LDli RDinv arfalse BSret', s)
        self.assertNotRegex(s, re.compile(r'^Definition \w*(?:memory|heap)\w*', re.M))

    def test_small_scheduler_arithmetic_control(self):
        # 仅核对 no-op 决策条件；不是两条 C 执行轨迹或可达性证据。
        checks = 0
        for mask in range(1, 4):
            tasks = {0: (4, bool(mask & 1)), 1: (6, bool(mask & 2))}
            ready = [t for t, (_, is_ready) in tasks.items() if is_ready]
            selected = min(ready, key=lambda t: tasks[t][0])
            for current in tasks:
                sched_self = tasks[current][1] and all(
                    tasks[current][0] <= tasks[t][0] for t in ready)
                self.assertEqual(sched_self, selected == current)
                checks += 1
        self.assertEqual(checks, 6)
        # 固定实际探针的任务表，仅改变 current。
        tasks = {0: (4, True), 1: (6, False)}
        self.assertTrue(tasks[0][1])
        self.assertFalse(tasks[1][1])

    def test_protocol_fixed_source_and_project_append(self):
        baseline = (D / '_CoqProject.baseline').read_bytes()
        current = (R / '_CoqProject').read_bytes()
        self.assertTrue(current.startswith(baseline))
        self.assertEqual(current[len(baseline):].splitlines().count(P.encode()), 1)
        self.assertNotIn(Q.encode(), current)
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h, p)
            self.assertEqual(read('baseline.json')['files'][p], h, p)
        self.assertEqual((D / 'protocol.sha256').read_text().split(),
                         [sha(D / 'protocol.json'), 'protocol.json'])

    def test_all_roots_stable_and_recursively_checked(self):
        roots = []
        for p, prefix in [(P, 'production'), (Q, 'probe')]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            for i in [1, 2]:
                row = read('stable-compiles.json')[prefix + '-stable-' + str(i)]
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / p))
                self.assertEqual(row['source_sha256'], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(
                r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
        trust = read('trust.json')
        self.assertEqual(len(roots), 20)
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']),
                             {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})


if __name__ == '__main__':
    unittest.main()
