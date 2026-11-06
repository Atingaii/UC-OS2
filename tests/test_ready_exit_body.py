"""完整退出本体的结构回归；语义证据是 Coq 定理，不声称语义 TDD。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage218-ready-exit-body'
SOURCES = {'body': 'certiucos/v293/proofs/V293OSIntExitReadyBody.v',
           'probe': 'audit/probes/V293OSIntExitReadyBodyProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return re.split(r'\b' + re.escape(name) + r'\s*:', src, maxsplit=1)[1].split('Proof.', 1)[0]


class ReadyExitBodyTests(unittest.TestCase):
    def test_source_identity_and_prospective_protocol(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        self.assertEqual([x['function']['name'] for x in source['functions']],
                         ['OSIntEnter', 'OSIntExit', 'OS_SchedNew', 'OS_Sched'])
        for row in source['functions']:
            p = D / (row['function']['name'] + '.configured.c.txt')
            self.assertEqual(hashlib.sha256(p.read_bytes()).hexdigest(),
                             row['function']['preprocessed_definition_sha256'])
        for p, h in source['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])

    def test_complete_actual_body_not_hoare_oracle(self):
        src = (R / SOURCES['body']).read_text()
        stmt = statement(src, 'V293_OSIntExit_ready_body')
        self.assertEqual(stmt.count('InfRules'), 1)
        self.assertIn('InfRules Spec V293_scheduler V293_shared_li inv', stmt)
        self.assertIn('V293_exit_boundary_body running nesting lock saved', stmt)
        self.assertIn('Spec sched_id=Some', stmt)
        for token in ['V293_time_zero Spec', 'V293_tick_known_ift_hoare',
                      'apply encrit2_rule', 'V293_OSIntExit_nesting_dispatch_hoare',
                      'apply V293OSIntExitReadyDispatch.V293_OSIntExit_ready_dispatch',
                      'apply V293_ready_storage_resumed_excrit', 'apply ret_rule']:
            self.assertIn(token, src)
        self.assertIn('nest<=1', stmt)
        self.assertIn('OS[(fun _:hid=>false),false,si,ci]', stmt)

    def test_same_inv_reopened_excrit_no_shared_snapshot(self):
        src = (R / SOURCES['body']).read_text()
        self.assertIn('Let inv:=V293_ready_storage_inv br bg bp target tp cells', src)
        excrit = src.split('Lemma V293_ready_storage_resumed_excrit', 1)[1].split('Section ReadyBody.', 1)[0]
        for token in ['apply V293_ready_storage_full_open',
                      'apply V293_ready_storage_full_close', 'apply excrit2_rule']:
            self.assertIn(token, excrit)
        resumed = src.split('Definition V293_exit_ready_body_resumed critical:=', 1)[1].split('.', 1)[0]
        self.assertIn('V293_ready_dispatch_resumed', resumed)
        for token in ['tasks', 'events', ' now']:
            self.assertNotIn(token, resumed)
        private = src.split('Let dispatchpx:=', 1)[1].split('.', 1)[0]
        self.assertNotIn('V293_owned_task_records', private)
        self.assertIn('controls++rest', src)
        self.assertIn('V293_storage returned', statement(src, 'V293_exit_ready_body_lend') +
                      src.split('Lemma V293_exit_ready_body_lend', 1)[1].split('Theorem V293_OSIntExit_ready_body', 1)[0])

    def test_typed_full_entry_actual_instantiation_and_local_control(self):
        src = (R / SOURCES['probe']).read_text()
        self.assertIn('OSTCBCur(1%positive,Tptr V293_tcb_type)', src)
        self.assertIn('V293_full_array_memory', src)
        self.assertIn('V293_owned_task_records OwnershipTasks', statement(src, 'JBphysical'))
        self.assertIn('forall nest c old ci aop', statement(src, 'JBentry'))
        self.assertIn('nest<=1 ->exists s', statement(src, 'JBentry_nonempty'))
        self.assertIn('V293_highest_ready OwnershipTasks OwnershipReady', statement(src, 'JBentry_nonempty'))
        self.assertIn('apply V293_OSIntExit_ready_body', src)
        stmt = statement(src, 'JBactual_body')
        self.assertEqual(stmt.count('InfRules'), 1)
        self.assertIn('V293_exit_boundary_body', stmt)
        control = statement(src, 'JBexcrit_control')
        self.assertIn('loststep P(curs(sprim excrit)', control)
        self.assertIn('((ge,le,M),ir,(false,si,ci))', control)
        self.assertIn('~((ge,le,M,ir,(false,si,false::ci),O,aop)|=Acs ci ** Atrue)', control)
        self.assertNotIn('cstepstar', control)

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
