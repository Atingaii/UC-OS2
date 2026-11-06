"""控制保留回归；文本和算术检查不替代 Coq 或初始化可达性。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage300-control-retention'
P = 'certiucos/v293/proofs/V293InterruptControlRetention.v'
Q = 'audit/probes/V293InterruptControlRetentionProbe.v'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read(name):
    return json.loads((D / name).read_text())


class ControlRetentionTests(unittest.TestCase):
    def test_unfiltered_builder_capture(self):
        s = (R / P).read_text()
        contract = s.split('Theorem V293_control_builder_capture :', 1)[1].split('Proof.', 1)[0]
        for word in ['BuildintPre', 'st|=pre', 'exists c,V293_control_valid c',
                     'V293_control_capture brun bn bl st=Some(getabst st,c)']:
            self.assertIn(word, contract)
        self.assertNotRegex(contract, r'quiet_filter|sched_self|highest|TaskSim|snapshot')
        for word in ['V293_irq_bound_builder_open', 'V293_irq_bound_snapshot_controls',
                     'V293_control_capture_owned', 'V293_irq_controls_load',
                     'load Tint8 M(br,0%Z)', 'load Tint8 M(bn,0%Z)', 'load Tint8 M(bl,0%Z)']:
            self.assertIn(word, s)

    def test_deterministic_selector_and_local_source_connection(self):
        s = (R / P).read_text()
        self.assertIn('if V293_control_dispatch c then sched;;spec_done None else spec_done None', s)
        self.assertIn('(osabst*V293_irq_control)%type', s)
        self.assertIn('V293_control_capture_unique', s)
        self.assertIn('V293_OSIntExit_nesting_dispatch_hoare', s)
        self.assertIn('V293_OSIntExit_nesting_dispatch nesting lock dispatch', s)
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertNotRegex(s, r'spec_choice|\?\?|absinfer_choice')
        # 原 guard-body 前提明确保留，不能把局部 guard 证明称为整个 ISR。
        contract = s.split('Theorem V293_control_source_guards :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('InfRules Spec sd li I r ri', contract)
        self.assertIn(')dispatch q t)', contract)

    def test_lock_only_evidence_and_distinct_high_specs(self):
        s = (R / Q).read_text()
        contract = s.split('Theorem CRlock_only_pair :', 1)[1].split('Proof.', 1)[0]
        for word in ['n<=1', 'store Tint8(ACmemory n)(151%positive,0%Z)(V293_byteval 1)',
                     '(b,i)<>(151%positive,0%Z)', 'V293_exit_depth n=0',
                     'CRcall(ACmemory n)CCspec ip /\\ CRcall Ml QCspec ip',
                     'Some(V293_control 1 n 0)', 'Some(V293_control 1 n 1)']:
            self.assertIn(word, contract)
        for word in ['NDlock_single_factor_complete_call', 'DCchanged_nonempty_client_call',
                     'CRlock_only_pair 0 ip', 'CRlock_only_pair 1 ip', 'CRerasure_actual_heap',
                     '(RIabstract OwnershipWaiting)V293_shared_li ACinv']:
            self.assertIn(word, s)
        self.assertIn('not yet one uniform high program', s)

    def test_source_arithmetic_oracle(self):
        # 独立逐步执行 C guard 的算术影子，仅覆盖控制条件，不模拟内存/调度器。
        checks = 0
        for running in [0, 1, 2, 255]:
            for nesting in range(256):
                for locked in range(256):
                    depth = nesting
                    called = False
                    if running == 1:
                        if depth > 0:
                            depth -= 1
                        if depth == 0 and locked == 0:
                            called = True
                    selector = running == 1 and nesting <= 1 and locked == 0
                    self.assertEqual(called, selector)
                    self.assertEqual(depth, max(nesting - 1, 0) if running == 1 else nesting)
                    entered = nesting + 1 if running == 1 and nesting < 255 else nesting
                    pair_dispatch = running == 1 and entered <= 1 and locked == 0
                    self.assertEqual(pair_dispatch, running == 1 and nesting == 0 and locked == 0)
                    checks += 1
        self.assertEqual(checks, 262144)
        self.assertEqual(max(255 - 1, 0), 254)
        # 锁是唯一变化因素；n=0/1均越过 running/nesting 的提前拒绝。
        for nesting in [0, 1]:
            self.assertEqual(max(nesting - 1, 0), 0)
            self.assertEqual([nesting <= 1 and lock == 0 for lock in [0, 1]], [True, False])

    def test_erasure_and_nonhighest_are_bounded_claims(self):
        s = (R / P).read_text()
        contract = s.split('Theorem V293_control_erasure_obstruction :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('(osabst->bool)', contract)
        self.assertIn('V293_control 1 1 0', contract)
        self.assertIn('V293_control 1 1 1', contract)
        q = (R / Q).read_text()
        self.assertIn('~spec_step V293_scheduler sched(RIabstract OwnershipWaiting)', q)
        self.assertIn('stronger current-is-running invariant are deliberately not asserted', q)

    def test_protocol_source_identity_and_append_only_project(self):
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
