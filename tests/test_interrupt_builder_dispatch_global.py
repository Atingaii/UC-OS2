"""Coq证明负责语义；此处保护全局连接、证据身份和原历史字节。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage312-builder-dispatch-global'
P = 'certiucos/v293/proofs/V293InterruptBuilderDispatchGlobal.v'
Q = 'audit/probes/V293InterruptBuilderDispatchGlobalProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class BuilderDispatchGlobalTests(unittest.TestCase):
    def test_actual_entry_unfiltered_builder_and_no_trace_premise(self):
        s = (R / P).read_text()
        pre, proof = s.split('Theorem V293_builder_dispatch_global_prefix :', 1)[1].split('Proof.', 1)
        inputs, outputs = pre.split('exists bs next nh Mf,', 1)
        for text in ['Some pre=BuildintPre', 'higherint(fun _=>false)i',
                     'get T t=Some(interrupted,(ike,ks))', 'get les t=Some caller',
                     'get aus t=Some((true,si,nil):localst)',
                     'ip i=Some(V293_irq_source_wrapper entry exit vector)',
                     'load Tint8 M(bc,0%Z)', 'load Tint8 M(bt,Z.of_nat n)']:
            self.assertIn(text, inputs)
        self.assertNotRegex(inputs, r'V293_(?:local|global)_steps|lpstep|hpstep|irq_quiet_filter')
        for text in ['V293_builder_dispatch_prefix', 'V293_interrupt_local_steps_global',
                     'V293_interrupt_source_enter']:
            self.assertIn(text, proof)
        self.assertIn('V293_global_steps(pc,(po,pi,ip))cst entered cut', outputs)
        self.assertIn('kint interrupted ike caller ks', outputs)
        self.assertNotIn('Require Import CertiOS.audit.', s)

    def test_original_semantics_and_same_program(self):
        s = (R / P).read_text()
        self.assertNotRegex(s, r'Inductive\s+\w*step|Definition\s+\w*step')
        for text in ['(pumerge po pi)entry', '(pumerge po pi)exit', '(pumerge po pi)sched_id',
                     '(pumerge po pi)sd', 'SWINVt', 'V293_irq_controls brun bn bl 1 0 0']:
            self.assertIn(text, s)
        q = (R / Q).read_text()
        self.assertIn('Definition BGglobal:lprog:=(GXempty,(RDprogram,GXempty,BGip))', q)
        self.assertIn('rewrite BGprogram_merge', q)

    def test_nonempty_instance_calls_production_not_assumed_trace(self):
        s = (R / Q).read_text()
        body = s.split('Theorem BGprepare :', 1)[1].split('Qed.', 1)[0]
        for text in ['QJentry_nonempty', 'BQpre_pack', 'BDsubheap_read', 'BDcanonical_reads',
                     'BDstorage_focus', 'BDarray_member', 'V293_builder_dispatch_global_prefix',
                     'V293_highest_unique', 'subst nh']:
            self.assertIn(text, body)
        self.assertNotIn('destruct BDprepare', body)
        self.assertLess(body.index('BDsubheap_read'), body.index('V293_builder_dispatch_global_prefix'))
        self.assertIn('Definition BGcaller:env:=set emp 108%Z(999%positive,Tint32)', s)
        self.assertIn('Definition BGint:=kint BGinterrupted CSke BGcaller CSks', s)

    def test_switch_uses_global_prefix_endpoint_and_retains_context(self):
        s = (R / Q).read_text()
        body = s.split('Theorem BGcompleted_match :', 1)[1].split('Qed.', 1)[0]
        for text in ['BGprepare cst', 'V293_control_switch_forward', 'BGcutS bs Ms',
                     'BGcutS bs Mf', 'V293_global_steps BGglobal cst', 'exact Entry',
                     'exact Prefix', 'exact Low', 'get BGnextT OwnershipWaiting=Some(SKIP,(kenil,BGtail))',
                     'get BGnextT OwnershipReady=Some CSready', '~lpstepabt',
                     "T'=BGnextT /\\cst'=cst", 'Some(V293_byteval 4)',
                     'get BGcaller 108%Z=Some(999%positive,Tint32)']:
            self.assertIn(text, body)
        self.assertLess(body.index('destruct(BGprepare'), body.index('V293_control_switch_forward'))
        self.assertIn('BDK ## kint BGinterrupted CSke BGcaller CSks', s)

    def test_recursive_trust_and_stable_source_identity(self):
        t = read('trust.json')
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 5)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in t['commands']))
        self.assertLessEqual(set(t['assumptions']), {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        for stem, path in [('production', P), ('probe', Q)]:
            for i in [1, 2]:
                row = read(f'{stem}-stable-{i:02d}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / path))
                self.assertEqual(row['source_sha256'], sha(R / path))

    def test_saved_caller_single_observation_after_completed_global_trace(self):
        p = read('ablation-protocol.json')
        a = read('ablation-results.json')
        self.assertTrue(p['prospective'] and a['passed'] and a['not_program_deletion'])
        base = (D / 'observation-base-01.v.snapshot.txt').read_text()
        mutant = (D / 'observation-mutant-01.v.snapshot.txt').read_text()
        self.assertEqual(base.count(p['old']), 1)
        self.assertEqual(base.replace(p['old'], p['new']), mutant)
        self.assertEqual(read('observation-base-01.json')['exit'], 0)
        self.assertEqual(read('observation-mutant-01.json')['exit'], 1)
        log = (D / 'observation-mutant-01.log').read_text()
        for text in ['The term "Saved" has type', 'Entry :', 'Prefix :', 'Full :',
                     'Low : lpstep', 'High : hpstep', 'Physical : load', 'Observed :', 'Saved :']:
            self.assertIn(text, log)
        self.assertEqual(a['protocol_sha256'], sha(D / 'ablation-protocol.json'))
        self.assertEqual(a['production_sha256'], sha(R / P))
        self.assertEqual(a['probe_sha256'], sha(R / Q))

    def test_history_preserved_and_future_appends_allowed(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in read('baseline.json')['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        for name in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / name).read_bytes().endswith((D / (name + '.baseline')).read_bytes()))
        project = (R / '_CoqProject').read_bytes()
        self.assertTrue(project.startswith((D / '_CoqProject.baseline').read_bytes() + P.encode() + b'\n'))
        self.assertEqual(project.decode().splitlines().count(P), 1)
        self.assertEqual({str(p.relative_to(R)): sha(p) for p in R.rglob('*.pyc')}, read('bytecode-baseline.json'))
        for name in ['protocol', 'ablation-protocol']:
            self.assertEqual((D / (name + '.sha256')).read_text().split(), [sha(D / (name + '.json')), name + '.json'])


if __name__ == '__main__':
    unittest.main()
