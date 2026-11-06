"""原切换切点的局部模拟；文本只保护接口，结论以 Coq 递归复核为准。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage310-control-switch-simulation'
P = 'certiucos/v293/proofs/V293InterruptControlSwitchSimulation.v'
Q = 'audit/probes/V293InterruptControlSwitchSimulationProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class ControlSwitchSimulationTests(unittest.TestCase):
    def test_ownership_constructs_original_low_and_high_steps(self):
        s = (R / P).read_text()
        hypotheses = s.split('Theorem V293_control_switch_forward :', 1)[0]
        self.assertNotRegex(hypotheses, r'Hypothesis\s+\w+\s*:\s*(?:lpstep|hpstep|store)')
        for text in ['V293_ready_switch_step', 'V293_control_switch_hpstep',
                     'V293_switch_owned_capture', 'Some(current,next)',
                     'get O curtid=Some(oscurt current)', 'Selected:sd O next']:
            self.assertIn(text, s)
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertNotRegex(s, r'Inductive\s+\w*step|Definition V293_scheduler')

    def test_all_low_successors_output_abort_and_frames(self):
        s = (R / P).read_text()
        for text in ['forall T\' cst\' S\' t\',lpstep', "T'=Tf /\\cst'=cst",
                     'V293_switch_all_successors', 'V293_switch_no_output',
                     'V293_switch_no_abort', 'other<>current', 'key<>curtid',
                     'get Mf(b,i)=get M(b,i)', 'get Of curtid=Some(oscurt next)',
                     'Some(Of,c)', 'Some(Vptr next)']:
            self.assertIn(text, s)

    def test_original_progsim_keeps_independent_continuation(self):
        s = (R / P).read_text().split('Theorem V293_control_switch_progsim :', 1)[1]
        pre, proof = s.split('Proof.', 1)
        for text in ['forall Mf,store', 'ProgSim P Tf', 'Some(Of,c)',
                     'ProgSim P T S Ph Th O cst current']:
            self.assertIn(text, pre)
        self.assertIn('eapply V293_switch_progsim', proof)
        self.assertIn('eapply hp_stepS', proof)
        self.assertNotIn('GOOD_OS', pre)

    def test_nonempty_actual_prefix_copy_switch_and_saved_context(self):
        s = (R / Q).read_text()
        pre, proof = s.split('Lemma SMprepare :', 1)[1].split('Qed.', 1)[0].split('Proof.', 1)
        self.assertRegex(pre, r'^\s*forall enabled ci cst,exists bs Ms,\s*SMsource')
        self.assertLess(proof.index('V293_exit_boundary_entry_global'), proof.index('V293_handoff_copy_execution'))
        for text in ['V293_csteps_global', 'V293_global_trans']:
            self.assertIn(text, proof)
        body = s.split('Theorem SMcompleted_match :', 1)[1].split('Qed.', 1)[0]
        self.assertLess(body.index('SMprepare'), body.index('V293_control_switch_forward'))
        for text in ['BXglobal true', 'GXtasks CSready', 'SMsaved_context',
                     'Some(false,nil,enabled::ci)', 'get CSTnext OwnershipWaiting=Some CSafter',
                     'get SMTf OwnershipReady=Some CSready', 'Some(V293_byteval 4)',
                     "T'=SMTf /\\cst'=cst", 'Some(Vptr OwnershipReady)']:
            self.assertIn(text, s)
        self.assertNotIn('Definition BXprogram', s)

    def test_recursive_trust_and_stable_identity(self):
        t = read('trust.json')
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots.extend(Path(p).stem + '.' + n for n in
                         re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M))
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 6)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in t['commands']))
        self.assertLessEqual(set(t['assumptions']), {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        for stem, path in [('production', P), ('probe', Q)]:
            for i in [1, 2]:
                row = read(f'{stem}-stable-{i}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / path))
                self.assertEqual(row['source_sha256'], sha(R / path))

    def test_single_completed_current_observation_factor(self):
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
        for text in ['Exec : SMsource', 'Low : lpstep', 'High : hpstep', 'Captured :',
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
        self.assertTrue(project.startswith((D / '_CoqProject.baseline').read_bytes() + b'\n' + P.encode() + b'\n'))
        self.assertEqual(project.decode().splitlines().count(P), 1)
        self.assertEqual({str(p.relative_to(R)): sha(p) for p in R.rglob('*.pyc')}, read('bytecode-baseline.json'))
        for name in ['protocol', 'ablation-protocol']:
            self.assertEqual((D / (name + '.sha256')).read_text().split(), [sha(D / (name + '.json')), name + '.json'])


if __name__ == '__main__':
    unittest.main()
