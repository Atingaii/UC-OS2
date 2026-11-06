"""实际 pint/body/exint 与同堆返回切点；文本守卫不替代 Coq。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage307-builder-nested-return'
P = 'certiucos/v293/proofs/V293InterruptBuilderNestedReturn.v'
Q = 'audit/probes/V293InterruptBuilderNestedReturnProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class BuilderNestedReturnTests(unittest.TestCase):
    def test_whole_heap_identity_comes_from_owned_bytes_and_frame(self):
        s = (R / P).read_text()
        c = s.split('Theorem V293_builder_nested_identity :', 1)[1].split('Proof.', 1)[0]
        pre, post = c.split(' V293_local_steps', 1)
        for term in ['Some pre=BuildintPre', 'st|=pre', '1<=n ->n<255',
                     'P entry=Some', 'P exit=Some']:
            self.assertIn(term, pre)
        self.assertNotRegex(pre, r'V293_local_steps|cstepstar|load Tint8|store Tint8|Mf=')
        self.assertNotIn('exists Mf', post)
        self.assertIn('((getgenv st,emp,getmem st)', post)
        for term in ['V293_nested_owned_byte_get', 'HalfPermMap.extensionality',
                     'apply Frame', 'subst Mf;split;assumption', 'join_get_get_l_true']:
            self.assertIn(term, s)

    def test_nonzero_global_execution_and_same_return_builder(self):
        s = (R / P).read_text()
        c = s.split('Theorem V293_builder_nested_global_roundtrip :', 1)[1].split('Proof.', 1)[0]
        pre, post = c.split(' let entered:=', 1)
        self.assertNotRegex(pre, r'V293_global_steps|V293_local_steps|cstepstar|lpstep|forall j')
        for term in ['Some pre=BuildintPre', 'Some ret=BuildintRet', 'intspec i=Some(spec_done None)',
                     '(ge,emp,M,isrupd ir i true', 'higherint ir i']:
            self.assertIn(term, pre)
        self.assertEqual(post.count('=>lpstep'), 2)
        self.assertIn('V293_global_steps(pc,(po,pi,ip))cst entered returning', post)
        self.assertIn('Tr cst Sr tr T cst(ge,les,M,ir,aus)t', post)
        for term in ['V293_interrupt_source_enter', 'eapply exint_step',
                     'V293_irq_builder_lower_clear', 'V293_bound_quiet_partial_return',
                     'V293_interrupt_local_steps_global', 'V293_exint_kstop_blocked']:
            self.assertIn(term, s)
        self.assertNotIn('Require Import CertiOS.audit.', s)

    def test_nonempty_same_program_boundaries_and_context(self):
        s = (R / Q).read_text()
        for term in ['Same two-function BNprogram, no RDprogram substitution',
                     'QJentry_nonempty n', 'QKsnapshot_change_isr',
                     'V293_builder_nested_global_roundtrip', 'NGempty BNprogram NGempty NGip',
                     'NGnonempty_roundtrip 1', 'NGnonempty_roundtrip 254',
                     'NGone(NGstart M)(NGentered M)', 'NGone(NGreturning M)(NGstart M)',
                     'keop1 negation Tint32 kenil', 'NGcontext_and_other_ISR',
                     'get NGcaller 112%Z<>get(emp:env)112%Z',
                     'QKstate(isrupd QKother 0 false)M O|=NGret']:
            self.assertIn(term, s)

    def test_recursive_kernel_check_and_frozen_source_identity(self):
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

    def test_single_completed_caller_observation_factor(self):
        p = read('ablation-protocol-02.json')
        a = read('ablation-results.json')
        self.assertTrue(a['passed'] and a['not_program_deletion'])
        base = (D / 'observation-base-02.v.snapshot.txt').read_text()
        mutant = (D / 'observation-mutant-02.v.snapshot.txt').read_text()
        self.assertEqual(base.count(p['old']), 1)
        self.assertEqual(base.replace(p['old'], p['new']), mutant)
        self.assertEqual(read('observation-base-02.json')['exit'], 0)
        self.assertEqual(read('observation-mutant-02.json')['exit'], 1)
        log = (D / 'observation-mutant-02.log').read_text()
        for term in ['Entry : NGone', 'Body : V293_global_steps', 'Return : NGone',
                     'The term "Observed" has type', 'Some ExpectedCaller']:
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
