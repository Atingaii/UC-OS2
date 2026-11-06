"""同一 builder 的实际 EOI/Enter 前缀与后继资源；这些守卫不替代 Coq。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage305-builder-enter-resources'
P = 'certiucos/v293/proofs/V293InterruptBuilderEnterResources.v'
Q = 'audit/probes/V293InterruptBuilderEnterResourcesProbe.v'


def read(n):
    return json.loads((D / n).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class BuilderEnterResourcesTests(unittest.TestCase):
    def test_builder_is_only_resource_oracle(self):
        s = (R / P).read_text()
        c = s.split('Theorem V293_builder_enter_prefix :', 1)[1].split('Proof.', 1)[0]
        pre, post = c.split('exists c Mf,', 1)
        self.assertIn('Some pre=BuildintPre', pre)
        self.assertIn('st|=pre', pre)
        self.assertNotRegex(pre, r'load Tint8|store Tint8|V293_local_steps|TaskSim|ir i=false|getlenv st=emp|V293_control_valid|exists byte|\bO\b')
        self.assertIn('(gettaskst st)', post)
        self.assertIn('isrupd(isrupd ir i true)i false', post)
        self.assertIn('(getgenv st,emp,Mf,', post)
        self.assertIn('Some(getabst st,V293_control_enter c)', post)
        self.assertIn('get Mf a=get(getmem st)a', post)

    def test_resources_follow_same_actual_write(self):
        s = (R / P).read_text()
        for n in ['V293_builder_snapshot_context', 'V293_builder_snapshot_isr',
                  'V293_builder_snapshot_enter_memory', 'V293_irq_bound_physical_good',
                  'goodfrm_prop', 'V293_tick_raw_slot_update', 'V293_put_byte_store',
                  'subst Mf', 'V293_control_enter_memory bn', 'eapply eoi_step',
                  'V293_control_enter_full_call', 'exact After', 'exact Frame']:
            self.assertIn(n, s)
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertIn('destruct(Nat.eqb run 1 && Nat.ltb nest 255)', s)

    def test_nonempty_same_successor_and_three_boundaries(self):
        s = (R / Q).read_text()
        for n in ['QJentry_nonempty n Bound', 'QJsnapshot_to_builder', 'BQpre_pack',
                  'V293_builder_enter_prefix', 'join M frame(JBmemory n Int.zero Int.zero)',
                  'BRrun 0 /\\BRrun 254 /\\BRrun 255',
                  'BRstate Mf O|=BRsnapshot(V293_interrupt_nest_after 1 n)',
                  '(gettaskst(BRstate Mf O))', 'V293_control_capture 99%positive 96%positive 97%positive(BRstate Mf O)',
                  'rewrite Capture in Captured;inversion Captured;subst c.']:
            self.assertIn(n, s)
        self.assertNotIn('TaskSim', s)

    def test_recursive_trust_and_current_input_identity(self):
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in
                      re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
        t = read('trust.json')
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 7)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in t['commands']))
        self.assertLessEqual(set(t['assumptions']), {'Classical_Prop.classic',
                             'FunctionalExtensionality.functional_extensionality_dep'})
        identity = read('trust-inputs.json')
        for p in [P, Q]:
            self.assertEqual(identity[p], sha(R / p))

    def test_post_observation_pair_not_program_deletion(self):
        p = read('ablation-protocol-02.json')
        a = read('ablation-results.json')
        self.assertTrue(a['passed'] and a['both_completed_full_prefix_resource_witness'] and a['only_expected_bit_changed'])
        self.assertIn('不是移除 EOI', p['scope'])
        self.assertEqual(p['production_sha256'], sha(R / P))
        self.assertEqual(p['probe_sha256'], sha(R / Q))
        base, mutant = a['accepted_runs']
        s = (D / (base + '.v.snapshot.txt')).read_text()
        m = (D / (mutant + '.v.snapshot.txt')).read_text()
        c = p['cases'][0]
        self.assertEqual(s.count(c['old']), 1)
        self.assertEqual(s.replace(c['old'], c['new']), m)
        self.assertEqual(read(base + '.json')['exit'], 0)
        self.assertEqual(read(mutant + '.json')['exit'], 1)
        log = (D / (mutant + '.log')).read_text()
        self.assertIn('After : BRstate Mf O |= BRsnapshot', log)
        self.assertIn('Trace : V293_local_steps RDprogram', log)
        self.assertIn(f'line {c["expected_failure_line"]},', log)
        self.assertIn('Unable to unify "ExpectedEOI"', log)

    def test_frozen_history_and_append_only_project(self):
        base = read('baseline.json')
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in base['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / p).read_bytes().endswith((D / (p + '.baseline')).read_bytes()))
        self.assertEqual((R / '_CoqProject').read_bytes(), (D / '_CoqProject.baseline').read_bytes() + b'\n' + P.encode() + b'\n')
        self.assertEqual({str(p.relative_to(R)): sha(p) for p in R.rglob('*.pyc')}, read('bytecode-baseline.json'))
        for n in ['protocol', 'ablation-protocol', 'ablation-protocol-02']:
            self.assertEqual((D / (n + '.sha256')).read_text().split(), [sha(D / (n + '.json')), n + '.json'])


if __name__ == '__main__':
    unittest.main()
