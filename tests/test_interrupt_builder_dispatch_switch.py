"""同一 builder 堆的调度分支；结论来自 Coq，文本仅保护连接接口。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage311-builder-dispatch-switch'
P = 'certiucos/v293/proofs/V293InterruptBuilderDispatchSwitch.v'
Q = 'audit/probes/V293InterruptBuilderDispatchSwitchProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class BuilderDispatchSwitchTests(unittest.TestCase):
    def test_unfiltered_builder_same_program_and_input_coherence(self):
        s = (R / P).read_text()
        theorem = s.split('Theorem V293_builder_dispatch_prefix :', 1)[1]
        pre, proof = theorem.split('Proof.', 1)
        for text in ['Some pre=BuildintPre', 'st|=pre',
                     'V293_control_capture brun bn bl st=Some(getabst st,V293_control 1 0 0)',
                     'load Tint8(getmem st)(bc,0%Z)',
                     'load Tint8(getmem st)(bt,Z.of_nat n)',
                     'V293_local_steps P', 'gettaskst st']:
            self.assertIn(text, pre)
        self.assertNotIn('irq_quiet_filter', pre)
        self.assertNotRegex(pre, r'->\s*(?:lpstep|hpstep|V293_local_steps|store)')
        for text in ['V293_builder_enter_prefix', 'apply V293_load_block_frame',
                     'V293_exit_boundary_entry_local', 'V293_handoff_copy_execution',
                     'V293_local_trans', 'V293_switch_owned_capture']:
            self.assertIn(text, proof)
        self.assertNotIn('Require Import CertiOS.audit.', s)

    def test_real_storage_resources_not_an_assumed_transition(self):
        s = (R / P).read_text()
        body = s.split('Lemma V293_builder_dispatch_resources :', 1)[1].split('Qed.', 1)[0]
        for text in ['V293_builder_named_cell_address', 'V293_ready_switch_close',
                     'V293_record_star_load_l', 'V293_owned_record_cell', 'V293_builder_dispatch_frame']:
            self.assertIn(text, body)
        self.assertNotRegex(s, r'Inductive\s+\w*step|Definition V293_scheduler')

    def test_owned_subheap_reads_and_nonempty_builder_execution(self):
        s = (R / Q).read_text()
        body = s.split('Theorem BDprepare :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('exists M frame bs Mf', body)
        for text in ['QJentry_nonempty', 'QJsnapshot_to_builder', 'BDsubheap_read',
                     'BDcanonical_reads', 'BDstorage_focus', 'BDarray_member',
                     'V293_builder_dispatch_prefix', 'SXnot_highest', 'subst nh']:
            self.assertIn(text, body)
        self.assertLess(body.index('BDsubheap_read'), body.index('V293_builder_dispatch_prefix'))
        self.assertIn('load_mem_mono', s)
        self.assertIn('FullRead:load tp whole a=Some x', s)
        self.assertIn('Definition BDglobal:lprog:=(GXempty,(RDprogram,GXempty', s)
        self.assertIn('V293_local_steps RDprogram', s)
        self.assertNotIn('SMprepare', body)

    def test_final_original_switch_matches_same_prefix_heap(self):
        s = (R / Q).read_text()
        body = s.split('Theorem BDcompleted_match :', 1)[1].split('Qed.', 1)[0]
        self.assertLess(body.index('destruct BDprepare'), body.index('V293_control_switch_forward'))
        for text in ['BDprefix M bs Ms', 'BDS bs Ms', 'BDS bs Mf',
                     'hpstep BDhigh CST', 'Some(V293_byteval 4)',
                     'Some(CSnext,V293_control 1 0 0)', "T'=BDTnext /\\cst'=cst",
                     '~lpstepabt', 'Some(SKIP,(kenil,BDK))', 'Some CSready',
                     'Some(false,[0],[false])']:
            self.assertIn(text, body)
        self.assertIn('kcall 300%Z', s)
        self.assertIn('kseq(sprim exint)kstop', s)

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
        self.assertEqual(t['roots_printed'], 11)
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

    def test_single_final_observation_after_completed_execution(self):
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
        for text in ['Prefix : BDprefix', 'Low : lpstep', 'High : hpstep', 'Captured :',
                     'Physical : load', 'Cache : load', 'All : forall', 'The term "Observed" has type']:
            self.assertIn(text, log)
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
