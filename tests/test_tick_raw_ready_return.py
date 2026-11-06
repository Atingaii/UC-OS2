"""入口、返回和证据保持回归；语义由真实Coq证明和coqchk检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage155-tick-raw-ready-return'
PRODUCTION = 'certiucos/v293/proofs/V293TimeTickRawReadyReturn.v'
PROBE = 'audit/probes/V293TimeTickRawReadyReturnProbe.v'


class TickRawReadyReturnTests(unittest.TestCase):
    def setUp(self):
        self.production = (R / PRODUCTION).read_text()
        self.probe = (R / PROBE).read_text()

    def test_fixed_source_and_existing_execution(self):
        identity = json.loads((D / 'source-identity.json').read_text())
        raw = (R / identity['current_upstream_file']).read_bytes()
        self.assertEqual(hashlib.sha256(raw).hexdigest(), identity['current_upstream_file_sha256'])
        i = identity['identity']
        self.assertEqual(hashlib.sha256(b''.join(raw.splitlines(keepends=True)[i['first_line'] - 1:i['last_line']])).hexdigest(), i['source_lines_sha256'])
        self.assertFalse(identity['new_AST'])
        for term in ('V293_tick_uninitialized_suffix_execution (map fst bindings)',
                     'apply V293_tick_post_hook_transition', 'V293_tick_chain_records_after',
                     'V293_tick_record_chain_ready_rel bindings'):
            self.assertIn(term, self.production)
        self.assertNotIn('CertiOS.audit.', self.production)

    def test_raw_Vundef_entry_not_typed_or_preinitialized(self):
        statement = self.production.split('Theorem V293_tick_raw_ready_return :', 1)[1].split('Proof.', 1)[0]
        entry, result = statement.split('exists Ms Mf,', 1)
        self.assertIn('bc Vundef (map fst bindings)', entry)
        self.assertEqual(entry.count('V293_priority_cells bp 0%Z entries'), 1)
        self.assertIn('Vint32 Int.zero', entry)
        self.assertNotIn('V293_owned_task_records', entry)
        self.assertIn('((ge,caller,Mf),ir,(enabled,si,ci))', result)
        self.assertIn('V293_tick_return_payload', result)
        self.assertIn('get Mf (bc,Z.of_nat k)=None', result)

    def test_exact_spatial_release_not_successful_free_premise(self):
        helper = self.production.split('Lemma V293_tick_release_slot :', 1)[1].split('Qed.', 1)[0]
        self.assertIn("apply free_locality2'", helper)
        self.assertIn('exists Mf, free tp b M=Some Mf', helper)
        self.assertIn('(ge,le,Mf,ir,aux,O,op) |= R', helper)
        for rule in ('sret_step', 'sfree_step', 'sfreeend_step', 'V293_tick_return_payload_context'):
            self.assertIn(rule, self.production)
        self.assertIn('V293_owned_cells_context', self.production)
        self.assertIn('V293_shared_fields_rebase', self.production)

    def test_nonempty_actual_two_allocations_and_caller(self):
        for term in ('OwnershipCellsSpatial', 'Lemma RRbase_raw :', 'Lemma RRfresh :',
                     'V293_tick_call_to_hook', 'Theorem RRallocated_entry :',
                     'Some Vundef', 'RRcaller', '9999%Z', 'Theorem RRliteral :'):
            self.assertIn(term, self.probe)
        self.assertIn(':: tl RCcells', self.probe)
        self.assertNotIn('V293_tick_pointer_cell 70%positive WhileIdle ::', self.probe)

    def test_same_returned_heap_controls_and_observations(self):
        for name in ('RRomitted_clock_control', 'RRfreed_pointer_control', 'RRobservations'):
            self.assertIn('Theorem ' + name + ' :', self.probe)
        self.assertIn('get ChainNew ostmid=Some (ostm (Int.repr 37))', self.probe)
        self.assertIn('forall id, id<>ostmid -> get PHnew id=get ChainNew id', self.probe)
        self.assertIn('V293_table_loads V293_tcb_type Mf 94%positive RCentries', self.probe)
        self.assertIn('V293_task_record Mf WhileSecond', self.probe)
        self.assertNotIn('del Mf', self.probe)

    def test_stable_compiles_project_and_no_holes(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('production', PRODUCTION), ('probe', PROBE)]:
            raw = (R / path).read_bytes()
            self.assertNotRegex(raw.decode(), r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show|idtac)\b')
            self.assertNotRegex(raw.decode(), re.compile(r'^Inductive ', re.M))
            row = json.loads((D / (stable[kind] + '.json')).read_text())
            self.assertEqual(row['exit'], 0)
            self.assertEqual(hashlib.sha256(raw).hexdigest(), row['source_sha256'])
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(raw, (D / (stable[kind] + '.v.snapshot.txt')).read_bytes())
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(PRODUCTION), 1)

    def test_old_sources_tests_and_evidence_unchanged(self):
        for name, digest in json.loads((D / 'baseline.json').read_text())['files'].items():
            if name.endswith('.v') or name.startswith(('csrc/', 'framework/', 'tactics/', 'audit/logs/', 'tests/')):
                self.assertEqual(hashlib.sha256((R / name).read_bytes()).hexdigest(), digest, name)


if __name__ == '__main__':
    unittest.main()
