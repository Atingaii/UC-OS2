"""真实 builders 的结构回归；语义证据来自 Coq，不声称语义 TDD。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage219-ready-exit-builders'
SOURCES = {'internal': 'certiucos/v293/proofs/V293OSIntExitReadyInternal.v',
           'probe': 'audit/probes/V293OSIntExitReadyInternalProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return re.split(r'\b' + re.escape(name) + r'\s*:', src, maxsplit=1)[1].split('Proof.', 1)[0]


class ReadyExitBuildersTests(unittest.TestCase):
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

    def test_real_builders_actual_body_not_hoare_oracle(self):
        src = (R / SOURCES['internal']).read_text()
        stmt = statement(src, 'V293_OSIntExit_ready_builder_contract')
        self.assertEqual(stmt.count('InfRules'), 1)
        for token in ['InfRules Spec V293_scheduler V293_shared_li V293_ready_builder_inv',
                      'Some pre=BuildPreI', 'Some post=BuildRetI',
                      'V293_exit_boundary_function running nesting lock saved',
                      'V293_exit_boundary_body running nesting lock saved',
                      'Spec sched_id=Some', 'running<>saved']:
            self.assertIn(token, stmt)
        for token in ['unfold BuildPreI in Pre', 'unfold BuildRetI in Post',
                      'apply V293_ready_builder_unpack', 'apply V293_ready_builder_pack',
                      'apply V293_OSIntExit_ready_body']:
            self.assertIn(token, src)
        self.assertNotIn('Invtransport', src)

    def test_external_good_fun_names_derived_and_no_shared_post_snapshot(self):
        src = (R / SOURCES['internal']).read_text()
        self.assertIn('Let tp:=V293_tcb_type', src)
        self.assertIn('V293_ready_storage_inv br bg bp target tp', src)
        memory = src.split('Definition V293_ready_builder_memory t:=', 1)[1].split('Definition V293_ready_builder_external', 1)[0]
        self.assertIn('V293_owned_task_records tasks', memory)
        for token in ['V293_ready_builder_memory_good', 'V293_ready_builder_external_good',
                      'V293_ready_builder_post_good', 'apply V293_exit_builder_names',
                      'apply V293_exit_builder_forget_names']:
            self.assertIn(token, src)
        external = src.split('Definition V293_ready_builder_external t:=', 1)[1].split('Lemma V293_ready_builder_memory_good', 1)[0]
        self.assertNotIn('A_notin_lenv', external)
        self.assertNotIn('Alvarenv', external)
        post = src.split('Definition V293_ready_builder_post t(result:option val):=', 1)[1].split('Lemma V293_ready_builder_memory_good', 1)[0]
        for token in ['tasks', 'events', ' now', 'entries', 'nest', 'saved']:
            self.assertNotIn(token, post)
        self.assertIn('SWINVt V293_ready_builder_inv t', post)

    def test_typed_full_entry_actual_instantiation_and_name_control(self):
        src = (R / SOURCES['probe']).read_text()
        self.assertIn('pose proof(JBentry nest c old ci aop', src)
        self.assertIn('V293_tcb_type 16 0 6 nest RTentries OwnershipTasks', statement(src, 'RBvalid'))
        self.assertIn('forall nest c old ci aop', statement(src, 'RBpre_owned'))
        self.assertIn('nest<=1 ->exists st', statement(src, 'RBentry_nonempty'))
        self.assertIn('V293_highest_ready OwnershipTasks OwnershipReady', statement(src, 'RBentry_nonempty'))
        self.assertIn('Int.repr Int.max_unsigned', statement(src, 'RBzero_max_entry'))
        self.assertIn('eapply V293_OSIntExit_ready_builder_contract', src)
        stmt = statement(src, 'RBactual_contract')
        self.assertEqual(stmt.count('InfRules'), 1)
        self.assertIn('V293_ready_storage_inv', stmt)
        self.assertIn('V293_exit_boundary_body', stmt)
        control = statement(src, 'RBshadow_control')
        self.assertIn('getmem(JBstate', control)
        self.assertIn('=getmem(RBrenamed_state', control)
        self.assertIn('RBpre 120%Z nest c aop nil', control)
        self.assertIn('RBpre 112%Z nest c aop nil', control)
        self.assertIn('~(RBrenamed_state', control)
        self.assertNotIn('cstepstar', control)
        self.assertIn('=None', statement(src, 'RBarity_control'))
        self.assertIn('=Some(RBpost', statement(src, 'RBreturn_arity_observation'))

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
