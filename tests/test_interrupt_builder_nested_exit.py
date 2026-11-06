"""同一 builder 驱动归一化 Exit 嵌套分支；文本守卫不替代 Coq。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage306-builder-nested-exit'
P = 'certiucos/v293/proofs/V293InterruptBuilderNestedExit.v'
Q = 'audit/probes/V293InterruptBuilderNestedExitProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class BuilderNestedExitTests(unittest.TestCase):
    def test_full_call_has_exact_heap_and_no_execution_oracle(self):
        s = (R / P).read_text()
        statement = s.split('Theorem V293_nested_call_exact :', 1)[1].split('Proof.', 1)[0]
        pre, post = statement.split(' V293_local_steps', 1)
        self.assertNotIn('exists bs Mf', statement)
        self.assertNotRegex(pre, r'V293_local_steps|cstepstar|free Tint32|store Tint32')
        self.assertIn('caller,V293_put_byte M(bn,0%Z)(Nat.pred n)', post)
        for term in ['HalfPermMap.extensionality', 'V293_freeb_outside',
                     'V293_freeb_removed', 'V293_success_fresh_none',
                     'sret_step', 'sfree_step', 'sfreeend_step', 'salloclv_step',
                     'apply encrit_step', 'apply excrit_step', 'V293_nested_saved_free']:
            self.assertIn(term, s)

    def test_builder_resources_drive_both_calls_in_one_program(self):
        s = (R / P).read_text()
        c = s.split('Theorem V293_builder_nested_prefix :', 1)[1].split('Proof.', 1)[0]
        pre, post = c.split(' exists Mf,', 1)
        for term in ['Some pre=BuildintPre', 'st|=pre', 'V293_control_capture brun bn bl st',
                     '1<=n ->n<255', 'P entry=Some', 'P exit=Some']:
            self.assertIn(term, pre)
        self.assertNotRegex(pre, r'load Tint8|store Tint8|V293_local_steps|snapshot 1|TaskSim')
        for term in ['(gettaskst st)', '(curs(sprim exint),(kenil,kstop))',
                     'snapshot 1 n locked', 'Some(getabst st,V293_control 1 n locked)',
                     'get Mf a=get(getmem st)a']:
            self.assertIn(term, post)
        self.assertIn('exact Prefix', s)
        self.assertIn('exact ExitTrace', s)
        self.assertIn('exact Returned', s)
        self.assertNotIn('Require Import CertiOS.audit.', s)

    def test_nonempty_boundaries_use_the_new_program(self):
        s = (R / Q).read_text()
        self.assertIn('BNrun 1 /\\BNrun 254', s)
        self.assertIn('QJentry_nonempty n', s)
        self.assertIn('V293_builder_nested_prefix', s)
        self.assertIn('BNprogram V293_scheduler 301%Z 300%Z', s)
        self.assertIn('BRstate Mf O|=BRsnapshot n', s)
        self.assertIn('BNcompleted_observation', s)
        self.assertIn('This is not RDprogram', s)

    def test_recursive_kernel_check_and_input_identity(self):
        t = read('trust.json')
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots.extend(Path(p).stem + '.' + name for name in
                         re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M))
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 9)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in t['commands']))
        self.assertLessEqual(set(t['assumptions']), {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})

    def test_single_factor_changes_only_completed_post_observation(self):
        p = read('ablation-protocol-02.json')
        a = read('ablation-results.json')
        self.assertTrue(a['passed'])
        base = (D / 'observation-base-02.v.snapshot.txt').read_text()
        mutant = (D / 'observation-mutant-02.v.snapshot.txt').read_text()
        self.assertEqual(base.count(p['old']), 1)
        self.assertEqual(base.replace(p['old'], p['new']), mutant)
        self.assertEqual(read('observation-base-02.json')['exit'], 0)
        self.assertEqual(read('observation-mutant-02.json')['exit'], 1)
        log = (D / 'observation-mutant-02.log').read_text()
        for term in ['Trace : V293_local_steps BNprogram', 'After : BRstate Mf O |= BRsnapshot 254',
                     'The term "Loads" has type', 'V293_byteval ExpectedNest']:
            self.assertIn(term, log)
        self.assertEqual(p['production_sha256'], sha(R / P))
        self.assertEqual(p['probe_sha256'], sha(R / Q))

    def test_preserves_frozen_history_and_allows_future_appends(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in read('baseline.json')['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        for name in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / name).read_bytes().endswith((D / (name + '.baseline')).read_bytes()))
        project = (R / '_CoqProject').read_bytes()
        self.assertTrue(project.startswith((D / '_CoqProject.baseline').read_bytes() + b'\n' + P.encode() + b'\n'))
        self.assertEqual(project.decode().splitlines().count(P), 1)
        self.assertEqual({str(p.relative_to(R)): sha(p) for p in R.rglob('*.pyc')}, read('bytecode-baseline.json'))
        for name in ['protocol', 'ablation-protocol', 'ablation-protocol-02']:
            self.assertEqual((D / (name + '.sha256')).read_text().split(), [sha(D / (name + '.json')), name + '.json'])


if __name__ == '__main__':
    unittest.main()
