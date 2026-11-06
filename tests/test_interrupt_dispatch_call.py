"""完整同任务中断退出调用；结构回归不替代 Coq 执行证明。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage197-interrupt-dispatch-call'
PROD = 'certiucos/v293/proofs/V293OSIntExitDispatchCall.v'
PROBE = 'audit/probes/V293OSIntExitDispatchCallProbe.v'


def read(name):
    return json.loads((D / name).read_text())


class InterruptDispatchCallTests(unittest.TestCase):
    def test_exact_sources_and_frozen_protocol(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        self.assertEqual([f['function']['name'] for f in source['functions']], ['OSIntExit', 'OS_SchedNew'])
        for f in source['functions']:
            self.assertTrue(f['reconstructed_repaired_source_matches'])
            self.assertTrue(f['temporary_source_removed_on_context_exit'])
            self.assertEqual(hashlib.sha256((D / (f['function']['name'] + '.configured.c.txt')).read_bytes()).hexdigest(),
                             f['function']['preprocessed_definition_sha256'])
        for p, h in source['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
            self.assertEqual(h, read('baseline.json')['files'][p])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(), read('protocol-identity.json')['protocol.json'])
        old = R / 'audit/logs/stage196-interrupt-dispatch-execution/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_primary_has_no_execution_or_allocation_oracle(self):
        src = (R / PROD).read_text()
        stmt = src.split('Theorem V293_OSIntExit_same_task_call_execution :', 1)[1].split('Proof.', 1)[0]
        pre = stmt.split('exists bs Mf,', 1)[0]
        for token in ('cstepstar', 'V293_local_steps', 'fresh M', 'store ', 'free ', 'callcont', 'evalval', 'InfRules'):
            self.assertNotIn(token, pre)
        for token in ('P f=Some(V293_OSIntExit_abstract_function', 'P sched_id=Some(V293_OSSchedNew_function',
                      'V293_current_task tasks ct nc', 'V293_highest_ready tasks ct', '(false,si,ci)',
                      '(enabled,si,ci)', 'forall k,k<4', 'c<>bs', 'c<>bo', '(c,i)<>(bh,0%Z)', '(c,i)<>(bn,0%Z)'):
            self.assertIn(token, stmt)
        for token in ('V293_success_scheduler_storage', 'V293_cpu_initialized_frame',
                      'V293_OSIntExit_dispatch_prefix_execution', 'V293_highest_unique',
                      'V293_OSSched_current_target', 'V293_exit_same_priority_skip', 'apply encrit_step',
                      'apply excrit_step', 'eapply sfexec_step', 'eapply salloclv_step',
                      'V293_cpu_release', 'V293_sched_call_return'):
            self.assertIn(token, src)
        self.assertNotIn('CertiOS.audit.', src)

    def test_independent_nonempty_resources_and_complete_IE_controls(self):
        src = (R / PROBE).read_text()
        for token in ('Lemma FXentry :', 'apply OwnershipCellsSpatial.', 'apply FXold_entry.',
                      'Lemma FXcurrent :', 'Lemma FXhighest :', 'Lemma FXindependent_entry :',
                      'Theorem FXcomplete_call :', 'V293_OSIntExit_same_task_call_execution',
                      'FXcomplete_call false ci kstop', 'FXcomplete_call true ci kstop',
                      'Theorem FXboth_IE_complete :', 'FXmemory 1 4', 'Some(Vptr OwnershipReady)'):
            self.assertIn(token, src)
        stmt = src.split('Theorem FXboth_IE_complete :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(stmt.count('V293_local_steps FXprogram'), 2)
        self.assertEqual(stmt.count('((FXge,FXcaller,FXmemory 1 4)'), 2)
        self.assertIn('(false,nil,ci)', stmt)
        self.assertIn('(true,nil,ci)', stmt)
        self.assertIn('(curs(sskip None),(kenil,kstop))', stmt)
        complete = src.split('Theorem FXcomplete_call :', 1)[1].split('Proof.', 1)[0]
        self.assertNotIn('->', complete.split('(forall k,', 1)[0])

    def test_shadow_restoration_and_single_lookup_deletion_boundary(self):
        src = (R / PROBE).read_text()
        for token in ('get FXcaller 601%Z=Some(99%positive,Tint8)',
                      'get FXcaller 113%Z=Some(100%positive,Tint8)',
                      'get FXge 113%Z=Some(98%positive,Tint8)', 'V293_byteval 23',
                      'Theorem FXonly_callee_deleted :', 'f<>107%Z ->FXnoSched f=FXprogram f',
                      'Theorem FXmissing_scheduler_no_step :', 'curs(sfexec 107%Z nil nil)',
                      'apply V293_missing_port_has_no_step'):
            self.assertIn(token, src)
        both = src.split('Theorem FXboth_IE_complete :', 1)[1].split('Proof.', 1)[0]
        for b in (99, 100):
            self.assertIn(f'load Tint8 M0({b}%positive,0%Z)', both)
            self.assertIn(f'load Tint8 M1({b}%positive,0%Z)', both)
        self.assertIn('load Tint32 M0(97%positive,0%Z)=Some(Vint32(Int.repr 19))', both)
        self.assertIn('load Tint32 M1(97%positive,0%Z)=Some(Vint32(Int.repr 19))', both)

    def test_stable_compiles_trust_and_no_new_holes(self):
        stable = read('stable-compiles.json')
        for kind, p in (('body', PROD), ('probe', PROBE)):
            row = read(stable[kind] + '.json')
            h = hashlib.sha256((R / p).read_bytes()).hexdigest()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(h, row['initial_source_sha256'])
            self.assertEqual(h, row['source_sha256'])
            self.assertEqual(h, hashlib.sha256((D / (stable[kind] + '.v.snapshot.txt')).read_bytes()).hexdigest())
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
        trust = read('trust.json')
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(trust['roots_printed'], len(trust['roots']))
        self.assertEqual(trust['roots_printed'], 19)
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))
