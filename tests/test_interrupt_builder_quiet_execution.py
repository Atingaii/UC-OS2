"""全部不调度分支共用实际 heap/program；文本检查不替代 Coq 内核。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage308-builder-quiet-execution'
P = 'certiucos/v293/proofs/V293InterruptBuilderQuietExecution.v'
Q = 'audit/probes/V293InterruptBuilderQuietExecutionProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class BuilderQuietExecutionTests(unittest.TestCase):
    def test_call_constructs_allocation_body_and_exact_free(self):
        s = (R / P).read_text()
        c = s.split('Theorem V293_quiet_call_exact :', 1)[1].split('Proof.', 1)[0]
        pre = c.split(' V293_local_steps', 1)[0]
        self.assertNotRegex(pre, r'cstepstar|alloc|free|V293_local_steps')
        for term in ['V293_control_dispatch(V293_control run nest locked)=false',
                     'saved<>running ->saved<>nesting ->saved<>lock', 'run<256 ->nest<256 ->locked<256']:
            self.assertIn(term, pre)
        for term in ['V293_success_scheduler_storage', 'V293_nested_saved_free',
                     'V293_nested_void_return_exact', 'V293_control_decrement_execution',
                     'V293_control_guards_execution', 'sfexec_step', 'sallocend_step']:
            self.assertIn(term, s)

    def test_builder_same_heap_snapshot_capture_and_control_trace(self):
        s = (R / P).read_text()
        c = s.split('Theorem V293_builder_quiet_execution :', 1)[1].split('Proof.', 1)[0]
        pre, post = c.split(' let final:=', 1)
        for term in ['Some pre=BuildintPre', 'st|=pre', 'V293_control_capture',
                     'V293_control_dispatch(V293_control_enter c)=false', 'P entry=Some', 'P exit=Some']:
            self.assertIn(term, pre)
        self.assertNotRegex(pre, r'cstepstar|V293_local_steps|load Tint8|store Tint8|quiet_filter|1<=|<255')
        for term in ['let Mf:=V293_put_byte(getmem st)', 'snapshot(V293_control_running final)',
                     'Some(getabst st,final)', 'V293_control_steps sd V293_fixed_control_handler']:
            self.assertIn(term, post)
        for term in ['HalfPermMap.extensionality', 'V293_nested_owned_byte_get',
                     'V293_builder_snapshot_exit_memory', 'apply Frame']:
            self.assertIn(term, s)
        self.assertNotIn('Require Import CertiOS.audit.', s)

    def test_explicit_global_entry_return_and_saturated_memory(self):
        s = (R / P).read_text()
        c = s.split('Theorem V293_builder_quiet_global_return :', 1)[1].split('Proof.', 1)[0]
        pre, post = c.split(' let final:=', 1)
        self.assertNotRegex(pre, r'lpstep|V293_global_steps|V293_local_steps|cstepstar')
        self.assertEqual(post.count('=>lpstep'), 2)
        for term in ['(ge,set les t emp,Mf,ir', 'Tr cst Sr tr T cst(ge,les,Mf,ir,aus)t',
                     'V293_global_steps(pc,(po,pi,ip))cst entered returning',
                     'V293_control_steps sd V293_fixed_control_handler(O,c)']:
            self.assertIn(term, post)
        for term in ['V293_interrupt_source_enter', 'V293_interrupt_local_steps_global',
                     'eapply exint_step', 'V293_irq_builder_lower_clear', 'V293_bound_quiet_partial_return']:
            self.assertIn(term, s)

    def test_nonempty_same_program_all_quiet_boundaries(self):
        s = (R / Q).read_text()
        for term in ['QJentry_nonempty n', 'QEreplace_controls', 'QEbyte_update',
                     'V293_builder_quiet_global_return', 'NGempty BNprogram NGempty NGip',
                     'QEcase 0 0 0', 'QEcase 2 255 0', 'QEcase 1 1 0', 'QEcase 1 254 0',
                     'QEcase 1 255 0', 'QEcase 1 0 1', 'Mf<>M',
                     'QEcompleted_saturated_observation', 'Some(V293_byteval 254)']:
            self.assertIn(term, s)
        self.assertNotIn('RDprogram', s)

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
        self.assertEqual(t['roots_printed'], 10)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in t['commands']))
        self.assertLessEqual(set(t['assumptions']), {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})

    def test_single_completed_saturated_observation_factor(self):
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
        for term in ['Entry : NGone', 'Body : V293_global_steps', 'Return : NGone',
                     'The term "Observed" has type', 'V293_byteval ExpectedDepth']:
            self.assertIn(term, log)
        self.assertEqual(p['production_sha256'], sha(R / P))
        self.assertEqual(p['probe_sha256'], sha(R / Q))

    def test_preserves_history_and_allows_future_appends(self):
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
