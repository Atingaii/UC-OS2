"""语义由原Coq规则证明；本文件保护连接、边界和冻结证据。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage313-selected-client-simulation'
P = 'certiucos/v293/proofs/V293SelectedScalarTaskSim.v'
Q = 'audit/probes/V293SelectedScalarTaskSimProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class SelectedScalarTaskSimTests(unittest.TestCase):
    def test_original_task_sim_constructed_without_saved_simulation_premise(self):
        s = (R / P).read_text()
        pre, body = s.split('Theorem V293_scalar_client_TaskSim :', 1)[1].split('Proof.', 1)
        self.assertEqual(pre.count('TaskSim('), 1)
        self.assertIn('V293_scalar_client_state C ->satp o O(CurLINV li t) ->P(o,O) ->', pre)
        for text in ['cofix CIH', 'apply task_sim.', 'V293_scalar_client_match_low',
                     'V293_scalar_client_no_low_event', 'V293_scalar_client_match_abort']:
            self.assertIn(text, body)
        self.assertEqual(body.split('Qed.', 1)[0].count('\n - intros'), 7)
        self.assertIn('forall pu\',cstep pu\' C m C\' m', s)
        self.assertNotRegex(s, r'Inductive\s+\w*step|Definition\s+\w*step')
        self.assertNotIn('Require Import CertiOS.audit.', s)

    def test_shared_task_and_external_resources_cover_same_input(self):
        s = (R / P).read_text().split('Theorem V293_scalar_current_TaskSim :', 1)[1]
        for text in ['join Mt Mf Mtail /\\join Ms Mtail M', 'join Ot Of Otail /\\join Os Otail O',
                     'satp(ge,le,Ms,ir,(enabled,si,ci))Os(INV G)',
                     'satp(ge,le,Mt,ir,(enabled,si,ci))Ot(RDYINV G t **LINV li t lg)',
                     '(ge,le,Mf,ir,(enabled,si,ci),Of,op)|=R',
                     'V293_current_return_invariants', 'V293_scalar_client_TaskSim']:
            self.assertIn(text, s)
        self.assertNotIn('LINV li t lg **R)', s.split('TaskSim(', 1)[1].split('Proof.', 1)[0])

    def test_original_builder_switch_after_heap_provides_packet(self):
        s = (R / Q).read_text()
        body = s.split('Theorem SCcompleted_simulation :', 1)[1].split('Qed.', 1)[0]
        for text in ['BGprepare cst', 'V293_control_switch_forward',
                     'assert(Packet:SCpacket Mf)by(apply SCpartition;apply SCafter_core with(bs:=bs);exact After)',
                     'exact Entry', 'exact Prefix', 'exact Low']:
            self.assertIn(text, body)
        self.assertLess(body.index('BGprepare cst'), body.index('V293_control_switch_forward'))
        for text in ['V293_ready_switch_open', 'V293_dispatch_cell 106%Z',
                     'V293_current_core_highest_frame', 'V293_scalar_current_TaskSim',
                     'join Ms Mtail M', 'join Os Otail CSnext', 'INV SCinv']:
            self.assertIn(text, s)

    def test_selected_real_environment_and_external_frame_are_distinct(self):
        s = (R / Q).read_text()
        for text in ['get(BGcutL bs)OwnershipReady=Some emp',
                     'TaskLStMap BGcutA OwnershipReady=Some(true,nil,nil)',
                     'BDK ## kint BGinterrupted CSke BGcaller CSks',
                     'Definition SCframe:=V293_irq_controls',
                     '(JBge,emp,Mf,(fun _=>false),(true,nil,nil),Of,spec_done None)|=SCframe',
                     'V293_current_core_aux', 'get SCT3 OwnershipReady=Some SCend']:
            self.assertIn(text, s)
        self.assertNotIn('TaskSim BGglobal CSready(JBge,emp,M,', s)

    def test_three_nonstuttering_original_steps_and_corrected_unary_semantics(self):
        s = (R / Q).read_text()
        body = s.split('Theorem SCthree_steps :', 1)[1].split('Qed.', 1)[0]
        self.assertEqual(body.split('Proof.', 1)[0].count('lpstep BGglobal'), 3)
        self.assertEqual(body.split('Proof.', 1)[0].count('hpstep BDhigh'), 3)
        for text in ['CSready<>SCone /\\SCone<>SCtwo /\\SCtwo<>SCend',
                     'apply ec32_step', 'apply evuop_step', 'apply svseq_step']:
            self.assertIn(text, body)
        self.assertIn('Definition SCclient:clientst:=(JBge,SCcenvs,emp)', s)
        self.assertIn('Vint32(Int.not(Int.repr 7))', s)
        full = s.split('Theorem SCfull_client_run :', 1)[1]
        for text in ['SCcompleted_simulation SCclient', 'SCthree_steps bs Mf',
                     'exact L1', 'exact L2', 'exact L3', 'SCpacket Mf']:
            self.assertIn(text, full)
        correction = read('semantic-correction.json')
        self.assertTrue(correction['prospective_before_corrected_run'])
        self.assertIn('注释内', correction['correction'])
        self.assertEqual(correction['original_protocol_sha256'], sha(D / 'protocol.json'))
        self.assertEqual(read('probe-15.json')['exit'], 1)
        self.assertIn('Unable to unify', (D / 'probe-15.log').read_text())

    def test_recursive_trust_and_stable_source_identity(self):
        t = read('trust.json')
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 18)
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

    def test_late_single_observation_after_simulation_partition_and_execution(self):
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
        for text in ['The term "Saved" has type', 'Full :', 'Low : lpstep', 'High : hpstep',
                     'Task : TaskSim', 'Shared : satp', 'External :', 'L1 : lpstep', 'H1 : hpstep']:
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
