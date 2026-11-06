"""身份及接线回归；空间权限和反例由 Coq 检查，不由字符串测试替代。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage150-tick-record-reassembly'
PRODUCTION = 'certiucos/v293/proofs/V293TimeTickRecordReassembly.v'
PROBE = 'audit/probes/V293TimeTickRecordReassemblyProbe.v'


class TickRecordReassemblyTests(unittest.TestCase):
    def setUp(self):
        self.production = (R / PRODUCTION).read_text()
        self.probe = (R / PROBE).read_text()

    def test_original_source_identity(self):
        identity = json.loads((D / 'source-identity.json').read_text())
        raw = (R / identity['current_upstream_file']).read_bytes()
        self.assertEqual(hashlib.sha256(raw).hexdigest(), identity['current_upstream_file_sha256'])
        i = identity['identity']
        lines = b''.join(raw.splitlines(keepends=True)[i['first_line'] - 1:i['last_line']])
        self.assertEqual(hashlib.sha256(lines).hexdigest(), i['source_lines_sha256'])
        self.assertFalse(identity['new_AST'])
        self.assertNotIn('Definition V293_tick_iteration', self.production)
        self.assertIn('V293_tick_wait_iteration_refines P', self.production)

    def test_joint_ownership_and_inverse_focus(self):
        statement = self.production.split('Theorem V293_owned_task_records_reassemble :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('V293_owned_task_record t priority status message **', statement)
        self.assertIn('(V293_owned_task_records (del tasks t) ** R)', statement)
        self.assertNotIn('Atrue', statement)
        self.assertNotIn('load ', statement)
        self.assertIn('Permutation ((t,value)::TcbMod.lst (del tasks t))', self.production)
        self.assertIn('Theorem V293_owned_task_records_focus :', self.production)
        self.assertNotIn('Lemma V293_task_list_member_lookup :', self.production)

    def test_same_execution_result_and_frame(self):
        statement = self.production.split('Theorem V293_tick_wait_iteration_owned_records :', 1)[1].split('Proof.', 1)[0]
        for term in ('exists Mf,', 'spec_step sd', 'V293_local_steps P',
                     'V293_task_records Mf tasks\'', 'V293_owned_task_records tasks\' **',
                     'V293_priority_table entries tasks\'', 'V293_shared_fields current tasks\' events now ** R',
                     'V293_tick_pointer_cell bc next'):
            self.assertIn(term, statement)
        for oracle in ('evalval', 'store ', 'cstepstar', 'b<>'):
            self.assertNotIn(oracle, statement)
        for claim in ('CertiOS.audit.', 'Theorem GOOD_OS', 'Theorem WFIFun', 'verified_os'):
            self.assertNotIn(claim, self.production)

    def test_nonempty_same_block_controls_and_nonhead_focus(self):
        for term in ('Theorem ReassemblyEntry :', 'OwnershipCellsSpatial',
                     'Theorem ReassemblyLiteral :', 'Theorem ReassemblyMissingByteControl :',
                     'Theorem ReassemblyFrameAndPointer :', 'Theorem ReassemblyNoDuplicateByte :',
                     'Theorem ReassemblyFocusNext :', 'V293_owned_task_records_focus',
                     '172%Z', 'ReassemblyOther'):
            self.assertIn(term, self.probe)
        self.assertGreaterEqual(self.probe.count('81%positive'), 2)
        negative = self.probe.split('Theorem ReassemblyMissingByteControl :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('exists Mf', negative)
        self.assertIn('del Mf', negative)
        self.assertIn('~', negative)
        self.assertIn('V293_owned_task_records', negative)

    def test_stable_compiles_and_no_holes(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('production', PRODUCTION), ('probe', PROBE)]:
            raw = (R / path).read_bytes()
            self.assertNotRegex(raw.decode(), r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show|idtac)\b')
            self.assertNotRegex(raw.decode(), re.compile(r'^Inductive ', re.M))
            row = json.loads((D / (stable[kind] + '.json')).read_text())
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(hashlib.sha256(raw).hexdigest(), row['source_sha256'])
            self.assertEqual(raw, (D / (stable[kind] + '.v.snapshot.txt')).read_bytes())
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(PRODUCTION), 1)

    def test_old_sources_tests_and_evidence_unchanged(self):
        baseline = json.loads((D / 'baseline.json').read_text())
        for name, row in baseline.items():
            if name.endswith('.v') or name.startswith(('csrc/', 'framework/', 'tactics/', 'audit/logs/', 'tests/')):
                self.assertEqual(hashlib.sha256((R / name).read_bytes()).hexdigest(), row['sha256'], name)


if __name__ == '__main__':
    unittest.main()
