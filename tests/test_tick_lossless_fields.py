"""无损字段与返回接口回归；字符串检查不替代Coq语义验收。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage156-tick-lossless-fields'
FIELDS = 'certiucos/v293/proofs/V293TimeTickLosslessFields.v'
RETURN = 'certiucos/v293/proofs/V293TimeTickLosslessReturn.v'
PROBE = 'audit/probes/V293TimeTickLosslessReturnProbe.v'


class TickLosslessFieldsTests(unittest.TestCase):
    def setUp(self):
        self.fields, self.returned, self.probe = [(R / p).read_text() for p in (FIELDS, RETURN, PROBE)]

    def test_fixed_source_original_execution_and_open_hook(self):
        identity = json.loads((D / 'source-identity.json').read_text())
        self.assertEqual(identity, json.loads((D.parent / 'stage155-tick-raw-ready-return/source-identity.json').read_text()))
        raw = (R / identity['current_upstream_file']).read_bytes()
        self.assertEqual(hashlib.sha256(raw).hexdigest(), identity['current_upstream_file_sha256'])
        i = identity['identity']
        self.assertEqual(hashlib.sha256(b''.join(raw.splitlines(keepends=True)[i['first_line'] - 1:i['last_line']])).hexdigest(), i['source_lines_sha256'])
        for term in ('V293_tick_uninitialized_suffix_execution (map fst bindings)',
                     'apply V293_tick_post_hook_transition', 'V293_tick_release_locals'):
            self.assertIn(term, self.returned)
        self.assertFalse(identity['new_AST'])
        self.assertNotIn('sfree_step', self.probe)

    def test_exact_round_trip_and_no_residual_disposal(self):
        for root in ('V293_tick_node_fields_round_trip', 'V293_tick_chain_fields_round_trip',
                     'V293_tick_chain_records_lossless'):
            self.assertIn('Theorem ' + root + ' :', self.fields)
        self.assertIn('<->', self.fields)
        self.assertIn('Permutation before after', self.fields)
        self.assertNotIn('Atrue', re.sub(r'\(\*.*?\*\)', '', self.fields, flags=re.S))
        self.assertIn('skipn 2 (V293_tick_binding_extra binding)', self.fields)
        statement = self.fields.split('Theorem V293_tick_chain_records_lossless :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('V293_owned_record_cells (V293_tick_chain_residual bindings idle) ** R', statement)

    def test_return_owns_one_current_pointer_and_one_abstract_core(self):
        payload = self.returned.split('Definition V293_tick_lossless_return_payload', 1)[1].split('Lemma ', 1)[0]
        self.assertEqual(payload.count('CurTid current'), 1)
        self.assertEqual(payload.count('V293_shared_fields'), 1)
        self.assertIn('V293_owned_record_cells residual', payload)
        statement = self.returned.split('Theorem V293_tick_raw_lossless_return :', 1)[1].split('Proof.', 1)[0]
        entry, result = statement.split('exists Ms Mf,', 1)
        self.assertEqual(entry.count('CurTid current'), 1)
        self.assertIn('bc Vundef (map fst bindings)', entry)
        self.assertNotIn('V293_owned_task_records', entry)
        self.assertIn('((ge,caller,Mf),ir,(enabled,si,ci))', result)
        self.assertIn('get Mf (bc,Z.of_nat k)=None', result)
        self.assertIn('V293_tick_lossless_return_ready_core', self.returned)
        self.assertIn('V293_ready_core br bg bp', self.returned)
        self.assertIn('V293_ready_payload_context', self.returned)
        self.assertIn('V293_shared_fields_rebase', self.returned)

    def test_constructed_nonempty_entry_with_real_owned_caller(self):
        for term in ('OwnershipCellsSpatial', 'Lemma LRpointer_spatial :', 'Lemma LRbase_join :',
                     'Lemma LRfresh :', 'V293_tick_call_to_hook', 'Theorem LRallocated_entry :',
                     'Some Vundef', 'Theorem LRliteral :', 'Theorem LRnonvacuous :'):
            self.assertIn(term, self.probe)
        self.assertIn('set emp 9999%Z (90%positive,Tint32)', self.probe)
        self.assertIn('set PHglobal OSTCBCur (105%positive,Tptr Tvoid)', self.probe)
        self.assertIn('V293_encoded_memory 105%positive 0%Z false', self.probe)
        self.assertIn(':: tl RCcells', self.probe)
        self.assertNotIn('999%positive', self.probe)

    def test_actual_residual_loads_counts_and_permission_ablation(self):
        for root in ('LRresidual_layout', 'LRall_reason_counts', 'LRreturned_core',
                     'LRreturned_residual_loads', 'LRnext_ownership_control'):
            self.assertIn('Theorem ' + root + ' :', self.probe)
        self.assertIn('length (V293_tick_chain_layouts WhileBindings)=22', self.probe)
        self.assertIn('))=31', self.probe)
        self.assertIn('[0%Z;1%Z;3%Z]', self.probe)
        control = self.probe.split('Theorem LRnext_ownership_control :', 1)[1].split('Proof.', 1)[0]
        for term in ('LRexecution P ks M Mf', 'LRresult Mf', 'join mn mr Mf',
                     'LRrest mr orest', 'onext=emp', 'orest=PHnew',
                     'get mr ((81%positive,28%Z):addr)=None'):
            self.assertIn(term, control)
        self.assertNotIn('del Mf', self.probe)
        self.assertNotIn('store ', control)

    def test_stable_compiles_project_and_no_new_assumptions(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('fields', FIELDS), ('return', RETURN), ('probe', PROBE)]:
            raw = (R / path).read_bytes()
            self.assertNotRegex(raw.decode(), r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show|idtac)\b')
            self.assertNotRegex(raw.decode(), re.compile(r'^Inductive ', re.M))
            if kind != 'probe':
                self.assertNotIn('CertiOS.audit.', raw.decode())
            row = json.loads((D / (stable[kind] + '.json')).read_text())
            self.assertEqual(row['exit'], 0)
            self.assertEqual(hashlib.sha256(raw).hexdigest(), row['source_sha256'])
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(raw, (D / (stable[kind] + '.v.snapshot.txt')).read_bytes())
        for p in (FIELDS, RETURN):
            self.assertEqual((R / '_CoqProject').read_text().splitlines().count(p), 1)

    def test_old_sources_tests_and_frozen_evidence_unchanged(self):
        for name, digest in json.loads((D / 'baseline.json').read_text())['files'].items():
            if name.endswith('.v') or name.startswith(('csrc/', 'framework/', 'tactics/', 'audit/logs/', 'tests/')):
                self.assertEqual(hashlib.sha256((R / name).read_bytes()).hexdigest(), digest, name)


if __name__ == '__main__':
    unittest.main()
