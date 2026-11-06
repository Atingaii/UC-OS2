"""源码控制片段的同轨迹连接；不把局部前缀当成整函数健全性。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage302-control-execution'
P = 'certiucos/v293/proofs/V293InterruptControlExecution.v'
Q = 'audit/probes/V293InterruptControlExecutionProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class ControlExecutionTests(unittest.TestCase):
    def test_concrete_bridge_constructs_trace_not_assumes_it(self):
        s = (R / P).read_text()
        for root in ['V293_control_enter_execution_bridge', 'V293_control_exit_execution_bridge']:
            contract = s.split('Theorem ' + root + ' :', 1)[1].split('Proof.', 1)[0]
            pre, post = contract.split('exists Mf,', 1)
            self.assertNotRegex(pre, r'cstepstar|TaskSim|store Tint8|InfRules')
            self.assertIn('exists v,get M(bn,0%Z)=Some(true,v)', pre)
            self.assertIn('cstepstar P', post)
            self.assertIn('V293_control_read br bn bl Mf=', post)
            self.assertIn('V293_control_step sd', post)
            self.assertIn('get Mf a=get M a', post)
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertIn('Enabled dispatch is NOT evaluated or simulated', s)

    def test_source_execution_uses_real_evaluation_assignment_and_guards(self):
        s = (R / P).read_text()
        for text in ['V293_control_enter_eval', 'V293_rekey_if_execution',
                     'V293_assign_byte_execution', 'V293_put_byte_store',
                     'V293_exit_one_decrement_execution', 'V293_exit_physical_decrement_eval',
                     'V293_success_global_byte_eq', 'V293_control_guards_execution',
                     'V293_control_exit_residual_exact', 'Nat.pred n']:
            self.assertIn(text, s)
        self.assertIn('(m2:=(ge,le,V293_control_decrement_memory bn n M))', s)
        self.assertIn('then V293_put_byte M(bn,0%Z)(S(V293_control_nesting c)) else M', s)
        self.assertIn('match n with 0=>M | S _=>V293_put_byte', s)

    def test_nonempty_concrete_fixture_and_same_program_lock_pair(self):
        s = (R / Q).read_text()
        self.assertIn('(904%positive,7%Z)77', s)
        self.assertIn('Theorem CEenter_case', s)
        self.assertIn('Theorem CEexit_case', s)
        c = s.split('Theorem CElock_pair :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(c.count('cstepstar P'), 2)
        self.assertEqual(c.count('V293_OSIntExit_nesting_dispatch 802%Z 803%Z dispatch'), 2)
        self.assertIn('(curs dispatch,(kenil,ks))', c)
        self.assertIn('(curs(sskip None),(kenil,ks))', c)
        self.assertIn('get(CEmemory 1 n 1)a=get(CEmemory 1 n 0)a', c)
        self.assertIn('Some(V293_control 1 0 1)', c)
        for text in ['V293_control 1 255 0', 'V293_control 0 254 0',
                     'V293_control 2 0 0', 'V293_control_exit_residual 2 0',
                     'V293_control_exit_residual 1 255']:
            self.assertIn(text, s)

    def test_single_factor_definition_controls_are_independent(self):
        protocol = read('ablation-protocol.json')
        report = read('ablation-results.json')
        self.assertTrue(report['passed'] and report['production_unchanged'])
        self.assertEqual(protocol['production_sha256'], sha(R / P))
        self.assertEqual((D / 'ablation-protocol.sha256').read_text().split(),
                         [sha(D / 'ablation-protocol.json'), 'ablation-protocol.json'])
        self.assertEqual(len(report['results']), 6)
        for case in protocol['cases']:
            name = 'ablation3-' + case['name']
            old = (D / (name + '-baseline.v.snapshot.txt')).read_text()
            new = (D / (name + '-mutant.v.snapshot.txt')).read_text()
            self.assertEqual(old.replace(case['old'], case['new'], 1), new)
            self.assertEqual(read(name + '-baseline.json')['exit'], 0)
            self.assertNotEqual(read(name + '-mutant.json')['exit'], 0)
            self.assertEqual(old.count('Theorem discriminate_case'), 1)
        self.assertIn('不是完整执行模拟消融', protocol['scope'])

    def test_source_and_previous_evidence_identity(self):
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h, p)
        b = read('baseline.json')
        self.assertEqual(sha(R / b['previous_manifest']), b['previous_manifest_sha256'])
        base = (D / '_CoqProject.baseline').read_bytes()
        current = (R / '_CoqProject').read_bytes()
        self.assertTrue(current.startswith(base + b'\n' + P.encode() + b'\n'))
        self.assertEqual(current[len(base):].splitlines().count(P.encode()), 1)
        self.assertNotIn(Q.encode(), current)
        self.assertEqual((D / 'protocol.sha256').read_text().split(),
                         [sha(D / 'protocol.json'), 'protocol.json'])

    def test_no_holes_and_all_roots_recursively_checked(self):
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(
                r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
        trust = read('trust.json')
        self.assertEqual(len(roots), 16)
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']),
                             {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})

    def test_stable_recompilation_matches_current_source(self):
        for p, prefix in [(P, 'production'), (Q, 'probe')]:
            for i in [1, 2]:
                row = read('stable-compiles.json')[prefix + '-stable-' + str(i)]
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / p))
                self.assertEqual(row['source_sha256'], sha(R / p))


if __name__ == '__main__':
    unittest.main()
