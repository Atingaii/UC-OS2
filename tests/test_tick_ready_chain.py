"""固定身份与接线回归；语义事实由实际 Coq 编译和独立内核检查提供。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage153-tick-ready-chain'
PRODUCTION = 'certiucos/v293/proofs/V293TimeTickReadyChain.v'
PROBE = 'audit/probes/V293TimeTickReadyChainProbe.v'


class TickReadyChainTests(unittest.TestCase):
    def setUp(self):
        self.production = (R / PRODUCTION).read_text()
        self.probe = (R / PROBE).read_text()

    def test_fixed_source_and_reused_original_execution(self):
        identity = json.loads((D / 'source-identity.json').read_text())
        raw = (R / identity['current_upstream_file']).read_bytes()
        self.assertEqual(hashlib.sha256(raw).hexdigest(), identity['current_upstream_file_sha256'])
        i = identity['identity']
        body = b''.join(raw.splitlines(keepends=True)[i['first_line'] - 1:i['last_line']])
        self.assertEqual(hashlib.sha256(body).hexdigest(), i['source_lines_sha256'])
        self.assertFalse(identity['new_AST'])
        self.assertIn('V293_tick_while_shared_records bindings', self.production)
        self.assertNotIn('CertiOS.audit.', self.production)
        self.assertNotRegex(self.production, r'(?m)^Inductive ')

    def test_existing_ready_relation_not_parallel_oracle(self):
        for term in ('V293_tick_wait_bitmap_values', 'V293_tick_wait_bitmap_tasks',
                     'V293_tick_priority_table', 'V293_ready_set_membership',
                     'V293_ready_payload br bg bp', 'V293_ready_rel lof hif entries'):
            self.assertIn(term, self.production)
        self.assertNotRegex(self.production, r'(?m)^Definition .*inv')
        for name in ('V293_tick_chain_ready_rel', 'V293_tick_record_chain_ready_rel'):
            statement = self.production.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]
            self.assertIn('V293_tick_chain_bitmap (map fst bindings)', statement)
            self.assertIn('NoDup (V293_tick_record_keys bindings idle)', statement)
            self.assertNotIn('newtasks', statement)
        self.assertIn('induction bindings as', self.production)

    def test_single_output_memory_and_priority_frame_once(self):
        statement = self.production.split('Theorem V293_tick_while_ready_payload :', 1)[1].split('Proof.', 1)[0]
        before, after = statement.split('exists Mf,', 1)
        self.assertNotIn('exists Mf,', after)
        self.assertEqual(before.count('V293_priority_cells bp 0%Z entries'), 1)
        self.assertNotIn('V293_owned_task_records', before)
        self.assertIn('spec_stepstar sd (V293_tick_chain_code bindings)', before)
        for term in ('V293_local_steps P', 'swhile (V293_tick_guard ptcb)',
                     'V293_task_records Mf', 'V293_ready_loads Mf br bg bp',
                     'V293_ready_payload br bg bp', '(ge,le,Mf,',
                     'V293_shared_fields current (V293_tick_record_map true'):
            self.assertIn(term, after)
        self.assertIn('V293_ready_cells_loads br bg bp', self.production)
        self.assertIn('eapply V293_ready_loads_sub', self.production)

    def test_nonempty_entry_and_actual_thirteen_entry_table(self):
        for term in ('Lemma RCold_rel :', 'Lemma RCraw_entry :', 'Theorem RCentry :',
                     'Theorem RCliteral :', 'Theorem RCslots_ready_idle_frame :',
                     'OwnershipCellsSeparated RCcells', 'OwnershipCellsSpatial',
                     'V293_table_loads V293_tcb_type Mf 94%positive RCentries',
                     'V293_task_record Mf WhileIdle', 'ostm (Int.repr 37)', 'Int.repr 99'):
            self.assertIn(term, self.probe)
        entries = self.probe.split('Definition RCentries : list val :=', 1)[1].split('.', 1)[0]
        self.assertEqual(entries.count(';'), 12)
        for name in ('WhileSecond', 'WhileReady', 'WhileHead', 'WhileIdle'):
            self.assertIn('Vptr ' + name, entries)
        self.assertIn('V293_priority_cells 94%positive 0%Z RCentries ++ WhileFrameCells', self.probe)

    def test_same_executed_Mf_two_independent_bitmap_controls(self):
        for name in ('RCold_bitmap_control', 'RComitted_ready_control'):
            statement = self.probe.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]
            self.assertIn('exists Mf,', statement)
            self.assertIn('RCexecution P ks Mf /\\ RCresult Mf', statement)
            self.assertNotIn('del Mf', statement)
        self.assertIn('load Tint8 Mf (93%positive,1%Z)=Some (V293_byteval 20)', self.probe)
        self.assertIn('Lemma RCsingle_omitted_bit :', self.probe)
        self.assertIn('p=10 \\/ V293_bitmap_ready 16 16 p', self.probe)
        self.assertIn('~ V293_bitmap_tasks 16 16 WhileNewTasks', self.probe)
        self.assertIn('eq_trans (eq_sym High) Bad', self.probe)

    def test_stable_compilation_and_no_holes(self):
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
        baseline = json.loads((D / 'baseline.json').read_text())['files']
        for name, digest in baseline.items():
            if name.endswith('.v') or name.startswith(('csrc/', 'framework/', 'tactics/', 'audit/logs/', 'tests/')):
                self.assertEqual(hashlib.sha256((R / name).read_bytes()).hexdigest(), digest, name)


if __name__ == '__main__':
    unittest.main()
