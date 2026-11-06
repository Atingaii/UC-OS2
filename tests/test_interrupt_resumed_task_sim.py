"""Coq 检查原语义；回归保护非空 ISR 返回接口、晚拒绝与证据身份。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage315-interrupt-resumed-task-sim'
P = 'certiucos/v293/proofs/V293InterruptResumedTaskSim.v'
Q = 'audit/probes/V293InterruptResumedTaskSimProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def theorem(name):
    s = (R / P).read_text().split(name + ' :', 1)[1].split('Qed.', 1)[0]
    return s.split('Proof.', 1)


class InterruptResumedTaskSimTests(unittest.TestCase):
    def test_original_step_interfaces_keep_arbitrary_isr_stack(self):
        pre, body = theorem('V293_interrupt_cstep_TaskSim')
        self.assertIn('ie si ci', pre)
        self.assertIn('(ie,si,ci)', pre)
        self.assertNotIn('(ie,nil,ci)', pre)
        self.assertIn('forall Mf Mall,join M Mf Mall', pre)
        self.assertIn('cstep_idmove', (R / P).read_text())
        self.assertIn('apply task_sim.', body)
        self.assertIn('inv_ncare_le', body)
        pre, body = theorem('V293_interrupt_internal_TaskSim')
        self.assertIn('gettopis si<=INUM', pre)
        self.assertIn('V293_interrupt_shared_empty', body)
        self.assertIn('V293_return_disabled_INV_empty', body)

    def test_iret_restores_saved_context_and_constructs_successor_from_resources(self):
        pre, body = theorem('V293_interrupt_iret_successor')
        for text in ['int c ke caller ks', '(ie,i::si,ci)',
                     'Cf=(c,(ke,ks))', '(ge,caller,M,ir,(true,si,ci))']:
            self.assertIn(text, pre)
        self.assertIn('V293_cstep_not_primitive', body)
        pre, body = theorem('V293_interrupt_iret_TaskSim')
        self.assertEqual(pre.count('TaskSim('), 1)
        for text in ['V293_scalar_client_state', '(false,i::si,ci)', 'Core **CurTid t']:
            self.assertIn(text, pre)
        for text in ['V293_current_core_aux', 'V293_scalar_current_TaskSim',
                     'V293_interrupt_iret_successor', 'eapply exint_step', 'apply task_sim.']:
            self.assertIn(text, body)

    def test_pending_return_has_owned_cpu_not_free_or_successor_as_input(self):
        pre, body = theorem('V293_interrupt_pending_return_TaskSim')
        inputs, output = pre.split('TaskSim(', 1)
        for text in ['po f=Some(tau,d1,d2,body)', 'i<INUM',
                     'V293_scalar_client_state', 'Amapsto(b,0%Z)Tint32 true v',
                     '(false,i::si,false::ci)', 'kint c ke interrupted_env ks']:
            self.assertIn(text, inputs)
        self.assertNotIn('free ', inputs)
        self.assertNotIn('TaskSim', inputs)
        self.assertIn('(pc,A)(c,(ke,ks))', output)
        for text in ['V293_tick_free_owned', 'V293_interrupt_iret_TaskSim',
                     'V293_free_end_successor', 'V293_free_cell_successor',
                     'V293_cpu_layout', 'V293_interrupt_internal_TaskSim',
                     'eapply good_inv_prop;[exact Good|exact Rest]']:
            self.assertIn(text, body)

    def test_actual_suffix_executes_free_and_iret_on_every_heap_frame(self):
        pre, body = theorem('V293_interrupt_pending_return_execution')
        for text in ['exists Mr,free Tint32 b M=Some Mr',
                     'forall Mf Mall,join M Mf Mall', 'join Mr Mf Mall\'',
                     'V293_local_steps P', '(ge,interrupted_env,Mall\',ir,(true,si,ci))']:
            self.assertIn(text, pre)
        self.assertEqual(body.count('eapply V293_local_cons;'), 8)
        for text in ['V293_tick_free_owned', 'free_mono', 'join_free', 'apply excrit_step',
                     'eapply sret_step', 'eapply sfree_step', 'eapply sfreeend_step',
                     'eapply exint_step']:
            self.assertIn(text, body)

    def test_same_program_nonempty_fixture_distinguishes_resource_from_reachability(self):
        s = (R / Q).read_text()
        for text in ['RDprogram 300%Z=Some(Tvoid,dnil,dcons 120%Z Tint32 dnil,RSbody)',
                     'V293_interrupt_pending_return_TaskSim',
                     'V293_interrupt_pending_return_execution',
                     '(OCcompleted_owned SCclient)', 'RSowned bs **SCframe',
                     'apply RSrecontext in Owned', 'pose proof(RSclosed bs M O Owned)',
                     'get Mr(bs,Z.of_nat k)=None', 'join M frame Whole',
                     'NOT reachability', 'cons 0 nil', 'cons false nil']:
            self.assertIn(text, s)
        self.assertNotIn('ProgSim', s)
        self.assertNotIn('Require Import CertiOS.audit.', (R / P).read_text())

    def test_single_deleted_iret_is_rejected_after_the_same_seven_steps(self):
        protocol = read('ablation-protocol.json')
        result = read('ablation-results.json')
        self.assertTrue(protocol['prospective'] and result['passed'])
        self.assertTrue(result['not_early_lookup_rejection'])
        attempt = result['successful_attempt']
        base = (D / f'return-base-{attempt}.v.snapshot.txt').read_text()
        mutant = (D / f'return-mutant-{attempt}.v.snapshot.txt').read_text()
        self.assertEqual(base.count(protocol['old']), 1)
        self.assertEqual(base.replace(protocol['old'], protocol['new']), mutant)
        self.assertEqual(base.count('eapply V293_local_cons;'), 7)
        self.assertEqual(read(f'return-base-{attempt}.json')['exit'], 0)
        self.assertEqual(read(f'return-mutant-{attempt}.json')['exit'], 1)
        log = (D / f'return-mutant-{attempt}.log').read_text()
        for text in ['Prefix : V293_local_steps', 'Sim : RSsimulation', 'Free : free',
                     'FreeAll : free', 'Rest :', 'Unable to unify', 'curs (sprim exint)', 'SKIP']:
            self.assertIn(text, log)
        for key, path in [('protocol_sha256', D / 'ablation-protocol.json'),
                          ('production_sha256', R / P), ('probe_sha256', R / Q)]:
            self.assertEqual(result[key], sha(path))

    def test_recursive_trust_and_two_stable_compilations(self):
        trust = read('trust.json')
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], 13)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']), {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        for stem, p in [('production', P), ('probe', Q)]:
            for i in [1, 2]:
                row = read(f'{stem}-stable-{i:02d}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / p))
                self.assertEqual(row['source_sha256'], sha(R / p))

    def test_frozen_history_and_bytecode_preserved(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in read('baseline.json')['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        for name in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / name).read_bytes().endswith((D / (name + '.baseline')).read_bytes()))
        self.assertEqual((R / '_CoqProject').read_bytes(),
                         (D / '_CoqProject.baseline').read_bytes() + P.encode() + b'\n')
        self.assertEqual({str(p.relative_to(R)): sha(p) for p in R.rglob('*.pyc')}, read('bytecode-baseline.json'))
        for name in ['protocol', 'ablation-protocol']:
            self.assertEqual((D / (name + '.sha256')).read_text().split(),
                             [sha(D / (name + '.json')), name + '.json'])


if __name__ == '__main__':
    unittest.main()
