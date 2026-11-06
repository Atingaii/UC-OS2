"""结构回归；实际语义来自 Coq 定理与内核，不是语义 TDD。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage217-ready-exit-handoff'
SOURCES = {'body': 'certiucos/v293/proofs/V293OSIntExitReadyHandoff.v',
           'dispatch': 'certiucos/v293/proofs/V293OSIntExitReadyDispatch.v',
           'probe': 'audit/probes/V293OSIntExitReadyHandoffProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return re.split(r'\b' + re.escape(name) + r'\s*:', src, maxsplit=1)[1].split('Proof.', 1)[0]


class ReadyExitHandoffTests(unittest.TestCase):
    def test_source_identity_and_protocol(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        self.assertEqual([x['function']['name'] for x in source['functions']],
                         ['OSIntEnter', 'OSIntExit', 'OS_SchedNew', 'OS_Sched'])
        for row in source['functions']:
            self.assertEqual(hashlib.sha256((D / (row['function']['name'] + '.configured.c.txt')).read_bytes()).hexdigest(),
                             row['function']['preprocessed_definition_sha256'])
        for p, h in source['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])

    def test_actual_rules_and_closed_shared_resources(self):
        src = (R / SOURCES['body']).read_text()
        self.assertIn('Let inv := V293_ready_storage_inv br bg bp target tp cells', src)
        for name in ['V293_ready_exit_increment', 'V293_ready_exit_copy',
                     'V293_ready_exit_handoff', 'V293_ready_exit_changed_tail']:
            self.assertIn('InfRules Spec V293_scheduler V293_shared_li inv', statement(src, name))
        for token in ['apply V293_ready_storage_switch_close', 'apply V293_OSSched_counter_increment',
                      'apply V293_handoff_byte_copy', 'eapply switch_rule', 'apply skip_rule']:
            self.assertIn(token, src)
        resumed = src.split('Definition V293_ready_exit_resumed :=', 1)[1].split('.', 1)[0]
        self.assertIn('SWINVt inv tid', resumed)
        self.assertNotIn('tasks', resumed)
        private = src.split('Let private :=', 1)[1].split('.', 1)[0]
        self.assertNotIn('V293_owned_task_records', private)

    def test_actual_dispatch_not_body_oracle(self):
        src = (R / SOURCES['dispatch']).read_text()
        stmt = statement(src, 'V293_OSIntExit_ready_dispatch')
        self.assertEqual(stmt.count('InfRules'), 1)
        self.assertIn('V293_exit_boundary_dispatch', stmt)
        self.assertIn('Spec sched_id=Some', stmt)
        self.assertIn('apply V293_retained_OSSched_storage_prefix_returned', src)
        self.assertIn('apply V293_retained_arrays_ready', src)
        self.assertIn('apply V293_ready_exit_changed_tail', src)
        self.assertIn('V293_ready_rel lo hi entries tasks', statement(src, 'V293_retained_arrays_ready'))

    def test_independent_entry_and_same_heap_copy_control(self):
        src = (R / SOURCES['probe']).read_text()
        self.assertIn('exists M events now', statement(src, 'JHtail_nonempty'))
        self.assertIn('CGlocal_ready true enabled ci', src)
        stmt = statement(src, 'JHcopy_ablation')
        for token in ['cstepstar CGprogram', 'V293_interrupt_handoff 103%Z 108%Z 106%Z',
                      'store Tint8 M(94%positive,0%Z)', 'get Mc(b,i)=get M(b,i)',
                      'JHswitch_result M', 'JHswitch_result Mc', 'Some(V293_byteval 4)',
                      'Some(V293_byteval 6)']:
            self.assertIn(token, stmt)
        self.assertIn('V293_handoff_copy_execution', src)
        self.assertIn('V293_ready_storage_switch_step', src)
        self.assertIn('SWINVt JHinv OwnershipReady ** JHprivate', src)

    def test_stable_compiles_and_recursive_trust(self):
        roots = []
        for kind, p in SOURCES.items():
            src = (R / p).read_text()
            label = read('stable-compiles.json')[kind]
            row = read(label + '.json')
            h = hashlib.sha256((R / p).read_bytes()).hexdigest()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(h, row['initial_source_sha256'])
            self.assertEqual(h, row['source_sha256'])
            self.assertEqual(h, hashlib.sha256((D / (label + '.v.snapshot.txt')).read_bytes()).hexdigest())
            self.assertNotRegex(src, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            if kind != 'probe':
                self.assertNotIn('CertiOS.audit.', src)
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', src, re.M)]
        trust = read('trust.json')
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(roots, trust['roots'])
        self.assertEqual(len(roots), trust['roots_printed'])
        self.assertTrue(set(trust['assumptions']) <= set(trust['allowed']))
