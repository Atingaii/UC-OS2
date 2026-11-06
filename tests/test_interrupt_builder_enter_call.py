"""builder 到完整 Enter 的证据与接口边界；不替代 Coq 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage304-builder-enter-call'
P = 'certiucos/v293/proofs/V293InterruptBuilderEnterCall.v'
Q = 'audit/probes/V293InterruptBuilderEnterCallProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class BuilderEnterCallTests(unittest.TestCase):
    def test_builder_contract_has_no_memory_or_trace_oracle(self):
        s = (R / P).read_text()
        c = s.split('Theorem V293_builder_enter_call :', 1)[1].split('Proof.', 1)[0]
        pre, post = c.split('exists c Mf,', 1)
        self.assertIn('Some pre=BuildintPre', pre)
        self.assertIn('st|=pre', pre)
        self.assertIn('P f=Some(V293_OSIntEnter_function running nesting)', pre)
        self.assertNotRegex(pre, r'load Tint8|store Tint8|cstepstar|TaskSim|brun<>bn|bl<>bn|V293_control_valid|exists byte')
        self.assertEqual(c.count('cstepstar'), 1)
        self.assertIn('V293_control_read brun bn bl Mf=Some(V293_control_enter c)', post)
        self.assertIn('get Mf a=get(getmem st)a', post)
        self.assertIn('V293_control_enter_call_bridge', s)

    def test_same_builder_captures_abstract_state_and_resources(self):
        s = (R / P).read_text()
        c = s.split('Theorem V293_builder_enter_call :', 1)[1].split('Proof.', 1)[0]
        self.assertNotRegex(c.split('exists c Mf,', 1)[0], r'\bO\b')
        self.assertIn('Some(getabst st,c)', c)
        self.assertIn('V293_control_Enter(getabst st,c)', c)
        self.assertIn('(getabst st,V293_control_enter c)', c)
        for name in ['V293_irq_bound_builder_open', 'V293_irq_controls_load',
                     'V293_star_env_l', 'agvarenv_elim', 'V293_builder_byte_writable',
                     'V293_builder_bytes_separate', 'HalfPermMap.map_join_getp_some']:
            self.assertIn(name, s)
        self.assertNotIn('Require Import CertiOS.audit.', s)

    def test_nonempty_actual_builder_and_boundary_calls(self):
        s = (R / Q).read_text()
        for name in ['QJentry_nonempty n Bound', 'QJsnapshot_to_builder', 'BQpre_pack',
                     'V293_builder_enter_call', 'join M frame(JBmemory n Int.zero Int.zero)',
                     'QCstate M O|=BQpre', 'cstepstar RDprogram', 'BEcall 0 ks',
                     'BEcall 254 ks', 'BEcall 255 ks', 'forall n ks,n<256 ->BEcall n ks']:
            self.assertIn(name, s)
        self.assertIn('Some(O,V293_control 1 n 0)', s)
        self.assertIn('rewrite Capture in Captured;inversion Captured;subst c.', s)
        self.assertNotIn('TaskSim', s)

    def test_all_roots_machine_checked_with_bounded_trust(self):
        expected = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            expected += [Path(p).stem + '.' + n for n in
                         re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
        t = read('trust.json')
        self.assertEqual(t['roots'], expected)
        self.assertEqual(t['roots_printed'], 7)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in t['commands']))
        self.assertLessEqual(set(t['assumptions']), {'Classical_Prop.classic',
                             'FunctionalExtensionality.functional_extensionality_dep'})
        identity = read('trust-inputs.json')
        for p in [P, Q]:
            self.assertEqual(identity[p], sha(R / p))

    def test_permission_ablation_reaches_write_after_same_successful_read(self):
        p = read('ablation-protocol.json')
        a = read('ablation-results.json')
        self.assertTrue(a['passed'] and a['both_actual_reads_completed'] and a['only_permission_changed'])
        self.assertIn('不是完整执行模拟消融', p['scope'])
        self.assertEqual(p['production_sha256'], sha(R / P))
        self.assertEqual(p['probe_sha256'], sha(R / Q))
        base, mutant = a['accepted_runs']
        s = (D / (base + '.v.snapshot.txt')).read_text()
        m = (D / (mutant + '.v.snapshot.txt')).read_text()
        case = p['cases'][0]
        self.assertEqual(s.count(case['old']), 1)
        self.assertEqual(s.replace(case['old'], case['new']), m)
        self.assertEqual(read(base + '.json')['exit'], 0)
        self.assertEqual(read(mutant + '.json')['exit'], 1)
        for label in [base, mutant]:
            self.assertIn('[Qed.]', (D / (label + '.log')).read_text())
        self.assertIn('Unable to unify "Some ?Mf" with "None"', (D / (mutant + '.log')).read_text())
        self.assertEqual(len(a['initial_fixture_failures_preserved']), 4)

    def test_append_only_registration_and_old_sources_unchanged(self):
        original = (D / '_CoqProject.baseline').read_bytes()
        current = (R / '_CoqProject').read_bytes()
        self.assertTrue(current.startswith(original + b'\n' + P.encode() + b'\n'))
        self.assertEqual(current.decode().splitlines().count(P), 1)
        b = read('baseline.json')
        for p, h in b['files'].items():
            if p.endswith(('.v', '.c', '.h', '.py')):
                self.assertEqual(sha(R / p), h, p)


if __name__ == '__main__':
    unittest.main()
