"""身份与接线回归；执行、联合权限及负例由真实 Coq 证明检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage151-tick-while-records'
PRODUCTION = 'certiucos/v293/proofs/V293TimeTickWhileRecords.v'
PROBE = 'audit/probes/V293TimeTickWhileRecordsProbe.v'


class TickWhileRecordsTests(unittest.TestCase):
    def setUp(self):
        self.production = (R / PRODUCTION).read_text()
        self.probe = (R / PROBE).read_text()

    def test_fixed_source_and_original_while(self):
        identity = json.loads((D / 'source-identity.json').read_text())
        raw = (R / identity['current_upstream_file']).read_bytes()
        self.assertEqual(hashlib.sha256(raw).hexdigest(), identity['current_upstream_file_sha256'])
        i = identity['identity']
        body = b''.join(raw.splitlines(keepends=True)[i['first_line'] - 1:i['last_line']])
        self.assertEqual(hashlib.sha256(body).hexdigest(), i['source_lines_sha256'])
        self.assertFalse(identity['new_AST'])
        self.assertIn('V293_tick_while_owned_execution (map fst bindings) P ks', self.production)
        self.assertNotIn('Definition V293_tick_iteration', self.production)
        self.assertNotIn('CertiOS.audit.', self.production)

    def test_joint_chain_and_idle_owned_once(self):
        statement = self.production.split('Theorem V293_tick_chain_records_after :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('NoDup (V293_tick_record_keys bindings idle)', statement)
        self.assertIn('V293_tick_chain_cells (map V293_tick_task_after (map fst bindings)) idle', statement)
        self.assertEqual(statement.count('V293_owned_record_cell (V293_tick_idle_cell idle)'), 1)
        self.assertIn('V293_tick_idle_extra idle message', statement)
        self.assertIn('tl (V293_record_layout idle 12 rdy message 0)', self.production)
        self.assertIn('V293_owned_task_records_reassemble', self.production)
        self.assertNotIn('load ', statement)

    def test_same_Mf_and_unassumed_execution(self):
        statement = self.production.split('Theorem V293_tick_while_owned_records :', 1)[1].split('Proof.', 1)[0]
        inputs, outputs = statement.split('exists Mf,', 1)
        self.assertNotIn('V293_task_records', inputs)
        for term in ('V293_local_steps P', 'swhile (V293_tick_guard ptcb)',
                     'load (Tptr V293_tcb_type) Mf', 'V293_task_records Mf',
                     'V293_owned_task_records (V293_tick_record_map true bindings idle message) **',
                     'V293_tick_bitmap_cells bg br gf lof hif', '** R'):
            self.assertIn(term, outputs)
        for oracle in ('evalval', 'store ', 'cstepstar', 'spec_step', 'b<>'):
            self.assertNotIn(oracle, statement)
        for claim in ('Theorem GOOD_OS', 'Theorem WFIFun', 'verified_os'):
            self.assertNotIn(claim, self.production)

    def test_nonempty_entry_and_independent_controls(self):
        for term in ('Theorem WhileEntry :', 'OwnershipCellsSpatial',
                     'Theorem WhileLiteral :', 'Theorem WhileOmitSecondControl :',
                     'Theorem WhileReadyIdleAndFrame :', 'Theorem WhileNoDuplicateIdlePriority :',
                     'Theorem WhileInitialData :', 'WhileOldTasks', 'WhileSecond',
                     '81%positive,Int.repr 248', '81%positive,Int.repr 368'):
            self.assertIn(term, self.probe)
        negative = self.probe.split('Theorem WhileOmitSecondControl :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('exists Mf,', negative)
        self.assertIn('WhileExecution P ks Mf', negative)
        self.assertIn('~ V293_task_records Mf WhileOmitSecond', negative)
        self.assertNotIn('del Mf', negative)

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
        baseline = json.loads((D / 'baseline.json').read_text())
        for name, row in baseline.items():
            if name.endswith('.v') or name.startswith(('csrc/', 'framework/', 'tactics/', 'audit/logs/', 'tests/')):
                self.assertEqual(hashlib.sha256((R / name).read_bytes()).hexdigest(), row['sha256'], name)


if __name__ == '__main__':
    unittest.main()
