"""再入口接口回归；文本检查不替代27个Coq根和独立coqchk。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage157-tick-reentry'
SOURCES = ('certiucos/v293/proofs/V293TimeTickReentry.v',
           'certiucos/v293/proofs/V293TimeTickReentryReturn.v',
           'audit/probes/V293TimeTickReentryProbe.v')


class TickReentryTests(unittest.TestCase):
    def setUp(self):
        self.reentry, self.returned, self.probe = [(R / p).read_text() for p in SOURCES]

    def test_fixed_source_original_suffix_and_real_free(self):
        identity = json.loads((D / 'source-identity.json').read_text())
        self.assertEqual(identity, json.loads((D.parent / 'stage156-tick-lossless-fields/source-identity.json').read_text()))
        raw = (R / identity['current_upstream_file']).read_bytes()
        self.assertEqual(hashlib.sha256(raw).hexdigest(), identity['current_upstream_file_sha256'])
        i = identity['identity']
        self.assertEqual(hashlib.sha256(b''.join(raw.splitlines(keepends=True)[i['first_line'] - 1:i['last_line']])).hexdigest(), i['source_lines_sha256'])
        self.assertFalse(identity['new_AST'])
        for term in ('V293_tick_uninitialized_suffix_execution (map fst bindings)',
                     'apply V293_tick_post_hook_transition', 'V293_tick_release_locals'):
            self.assertIn(term, self.returned)

    def test_deterministic_next_binding_and_explicit_orphan(self):
        for root in ('V293_tick_reentry_binding_valid', 'V293_tick_reentry_record_map',
                     'V293_tick_reentry_keys', 'V293_tick_reentry_extra',
                     'V293_tick_reentry_extras_permutation', 'V293_tick_reentry_valid'):
            self.assertRegex(self.reentry, r'(?:Lemma|Theorem) ' + root + r'\s*:')
        self.assertIn('V293_tick_task_after (fst binding)', self.reentry)
        self.assertIn('V293_tick_binding_status true binding', self.reentry)
        self.assertIn('skipn 2 (V293_tick_binding_extra binding)', self.reentry)
        self.assertIn('Permutation', self.reentry)
        self.assertIn('V293_tick_wait_node_valid', self.reentry)

    def test_same_heap_payload_no_disposal_or_permission_duplicate(self):
        payload = self.returned.split('Definition V293_tick_reentry_payload', 1)[1].split('Lemma ', 1)[0]
        self.assertEqual(payload.count('CurTid current'), 1)
        self.assertEqual(payload.count('V293_shared_fields'), 1)
        self.assertNotIn('Atrue', payload)
        self.assertNotIn('V293_owned_task_records', payload)
        self.assertIn('V293_tick_chain_cells (map fst bindings)', payload)
        self.assertIn('concat (map V293_tick_binding_extra bindings)', payload)
        statement = self.returned.split('Theorem V293_tick_raw_reentry_return :', 1)[1].split('Proof.', 1)[0]
        entry, result = statement.split('exists Ms Mf,', 1)
        self.assertIn('true Vundef', entry)
        self.assertNotIn('V293_local_steps', entry)
        self.assertIn('concat (map V293_tick_reentry_orphan bindings) ++ cells', result)
        self.assertIn('((ge,caller,Mf),ir,(enabled,si,ci))', result)
        self.assertIn('get Mf (bc,Z.of_nat k)=None', result)
        self.assertIn('V293_tick_reentry_payload_context', self.returned)

    def test_second_allocation_and_execution_constructed_from_first_result(self):
        proof = self.probe.split('Theorem RPtwice :', 1)[1]
        statement = proof.split('Proof.', 1)[0]
        self.assertNotIn('fresh ', statement)
        self.assertNotIn('-> LRexecution', statement)
        for term in ('LRallocated_entry', 'RPpayload_fresh', 'After1', 'V293_tick_call_to_hook',
                     'FreshScan FreshSaved Callee', 'Raw2', 'RPstep sd P ks RPbindings1'):
            self.assertIn(term, proof)
        for term in ('RPprefix P ks Mf1 M2', 'LRexecution P ks M2 Mf2', 'Some Vundef',
                     'Int.repr 38', 'Int.repr 39'):
            self.assertIn(term, statement)
        self.assertIn('RPbytes_outside', self.probe)
        self.assertIn('RPcurrent_outside', self.probe)

    def test_actual_second_result_observations_and_all_reason_cases(self):
        for root in ('RPobservations', 'RPbinding_cases', 'RPorphan_not_lost'):
            self.assertIn('Theorem ' + root + ' :', self.probe)
        statement = self.probe.split('Theorem RPobservations :', 1)[1].split('Proof.', 1)[0]
        for term in ('Mf1 (101%positive,0%Z)', 'Mf2 (101%positive,0%Z)',
                     'Mf1 (81%positive,172%Z)', 'Mf2 (81%positive,172%Z)',
                     'Mf1 (81%positive,36%Z)', 'Mf2 (81%positive,36%Z)', 'Mf2 (90%positive,0%Z)'):
            self.assertIn(term, statement)
        self.assertIn('[0%Z;1%Z;3%Z]', self.probe)
        self.assertIn('intro reason. destruct reason;', self.probe)
        self.assertIn('RPcells1=RPcells2', self.probe)

    def test_single_permission_control_preserves_complement_and_abstract_state(self):
        statement = self.probe.split('Theorem RPnext_control :', 1)[1].split('Proof.', 1)[0]
        for term in ('join mn mr Mf', 'join onext orest RPstate1', 'onext=emp', 'orest=RPstate1',
                     'RPwithout_next mr orest', 'get mr ((81%positive,28%Z):addr)=None',
                     '~ (LRstate LRcaller mr orest |= RPpayload'):
            self.assertIn(term, statement)
        self.assertNotIn('del Mf', self.probe)
        self.assertNotIn('store ', statement)
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertEqual(len(protocol['controls']), 3)
        self.assertIn('CPU hook remains enabled and open', protocol['unchanged'])

    def test_stable_compiles_roots_project_and_old_frozen_sources(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        roots = []
        for kind, path in zip(('reentry', 'returned', 'probe'), SOURCES):
            raw = (R / path).read_bytes()
            self.assertNotRegex(raw.decode(), r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show|idtac)\b')
            self.assertNotRegex(raw.decode(), re.compile(r'^Inductive ', re.M))
            if kind != 'probe':
                self.assertNotIn('CertiOS.audit.', raw.decode())
                self.assertEqual((R / '_CoqProject').read_text().splitlines().count(path), 1)
            row = json.loads((D / (stable[kind] + '.json')).read_text())
            self.assertEqual(row['exit'], 0)
            self.assertEqual(hashlib.sha256(raw).hexdigest(), row['source_sha256'])
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(raw, (D / (stable[kind] + '.v.snapshot.txt')).read_bytes())
            roots += re.findall(r'^(?:Local )?(?:Lemma|Theorem) (\w+)\s*:', raw.decode(), re.M)
        self.assertEqual(len(roots), 27)
        for name, digest in json.loads((D / 'baseline.json').read_text())['files'].items():
            if name.endswith('.v') or name.startswith(('csrc/', 'framework/', 'tactics/', 'audit/logs/', 'tests/')):
                self.assertEqual(hashlib.sha256((R / name).read_bytes()).hexdigest(), digest, name)


if __name__ == '__main__':
    unittest.main()
