"""Structural companions only; actual Coq execution is the semantic oracle."""
import importlib.util
import json
from pathlib import Path
import re
import unittest
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('guard_local_check', ROOT / 'scripts/check-v293-task-prio-rekey.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


class TaskPrioGuardTests(unittest.TestCase):
    def setUp(self):
        self.code = (ROOT / CHECK.CODE).read_text()
        self.proof = (ROOT / CHECK.PROOF).read_text()
        self.probe = (ROOT / 'audit/probes/V293TaskPrioGuardProbe.v').read_text()

    def header(self, name):
        return self.proof.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]

    def test_actual_source_promotions_unsigned_zero_and_following_independent_events(self):
        folder = ROOT / 'audit/logs/stage26-task-prio-guard'
        node = json.loads((folder / 'configured-ready-condition.json').read_text())
        self.assertEqual((node['kind'], node['opcode']), ('BinaryOperator', '!='))
        left, right = node['inner']
        self.assertEqual((left['castKind'], left['type']['qualType']), ('IntegralCast', 'unsigned int'))
        band = left['inner'][0]['inner'][0]
        self.assertEqual((band['opcode'], band['type']['qualType']), ('&', 'int'))
        for operand in band['inner']:
            self.assertEqual((operand['castKind'], operand['type']['qualType']), ('IntegralCast', 'int'))
        self.assertEqual((right['kind'], right['value'], right['type']['qualType']),
                         ('IntegerLiteral', '0', 'unsigned int'))
        identity = json.loads((folder / 'source-identity.json').read_text())
        self.assertTrue(identity['source_hashes_match_frozen'])
        record = json.loads((folder / 'configured-function-identity.json').read_text())
        inventory = json.loads((ROOT / 'audit/repaired-source-inventory.json').read_text())
        self.assertEqual(record, next(f for f in inventory['functions'] if f['name'] == 'OSTaskChangePrio'))
        snippet = (folder / 'source-lines-119-141.txt').read_text()
        self.assertIn('135:     pevent = ptcb->OSTCBEventPtr;', snippet)
        self.assertNotIn('else', snippet)

    def test_literal_condition_and_program_do_not_alias_candidate(self):
        test = self.probe.split('Definition checked_test', 1)[1].split('Definition checked_branch', 1)[0]
        self.assertIn('eunop oppsite (ebinop oeq', test)
        self.assertIn('ebinop obitand', test)
        self.assertEqual(test.count('Tint32'), 2)
        for alias in ['V293_task_prio_ready_test', 'V293_task_prio_ready_branch',
                      'V293_task_prio_read_ready', 'V293_ready_branch_memory',
                      'V293_tcb_read_memory', 'V293_read_ready_fixture_mem', 'V293_read_ready_fixture_le']:
            self.assertNotRegex(self.probe, r'\b' + re.escape(alias) + r'\b')
        program = self.probe.split('Definition checked_read_ready', 1)[1].split('Definition checked_flag', 1)[0]
        self.assertIn('sseq (checked_reads p yo byo xo)', program)
        self.assertIn('checked_branch rows group yo yn xo xn byo byn', program)

    def test_full_byte_and_bit_domain_is_checked_in_kernel(self):
        body = self.proof.split('Lemma V293_ready_test_checked :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('(seq 0 8)) (seq 0 256)', body)
        self.assertIn('vm_compute. reflexivity.', body)
        h = self.header('V293_ready_test_arithmetic')
        self.assertIn('row < 256 -> bit < 8 ->', h)
        self.assertIn('= Nat.testbit row bit', h)

    def test_continuous_entry_requires_only_new_locals_not_old_exit_reads(self):
        before, after = self.header('V293_task_prio_read_ready_execution').split('let Mr :=', 1)
        self.assertIn('V293_tcb_old_loads M', before)
        self.assertIn('V293_rekey_new_bindings yn xn byn new', before)
        self.assertNotIn('V293_rekey_ready_bindings', before)
        self.assertNotIn('cstepstar', before)
        self.assertNotIn('evalval', before)
        self.assertNotIn('store ', before)
        self.assertIn('b <> dy /\\ b <> dby /\\ b <> dx', before)
        self.assertIn('V293_task_prio_read_ready', after)
        self.assertIn('(ge,le,Mr)', after)

    def test_same_state_witness_covers_pointer_fields_bitmap_permissions_and_new_locals(self):
        h = self.header('V293_read_ready_entry_witness')
        for part in ['load (Tptr V293_tcb_type) M', 'V293_tcb_old_loads M',
                     'V293_rekey_bitmap_loads M', 'V293_rekey_bitmap_writable M',
                     'V293_rekey_new_bindings']:
            self.assertIn(part, h)
        self.assertEqual(h.count('(exists v, get M'), 3)
        fixture = self.proof.split('Definition V293_read_ready_fixture_mem', 1)[1].split('Local Ltac', 1)[0]
        for dest in [32, 36, 34]:
            self.assertIn(f'({dest}%positive,0%Z) 255', fixture)
        self.assertIn('8%Z', h)

    def test_true_false_control_changes_only_old_ready_bit(self):
        h = self.header('V293_read_ready_physical_controls')
        self.assertIn('V293_read_ready_observes 20 0 2 6 true 80 0 1', h)
        self.assertIn('V293_read_ready_observes 16 0 2 6 false 16 0 1', h)
        self.assertEqual(20 ^ 16, 1 << 2)
        observe = self.proof.split('Definition V293_read_ready_observes', 1)[1].split('Theorem V293_read_ready_physical_controls', 1)[0]
        self.assertIn('cstepstar', observe)
        self.assertIn('evalval', observe)
        self.assertIn('V293_rekey_bitmap_loads Mf', observe)

    def test_four_single_header_controls_preserve_proof_suffixes(self):
        cases = CHECK.mutations(self.proof, guard=True)
        self.assertEqual(len(cases), 4)
        for label, (candidate, declaration) in cases.items():
            with self.subTest(label=label):
                start = self.proof.index(declaration)
                end = self.proof.index('Proof.', start)
                ce = candidate.index('Proof.', start)
                self.assertEqual(candidate[:start], self.proof[:start])
                self.assertEqual(candidate[ce:], self.proof[end:])
                self.assertNotEqual(candidate[start:ce], self.proof[start:end])

    def test_actual_assumption_count_and_unknown_axioms_fail_closed(self):
        self.assertEqual(self.probe.count('Print Assumptions checked_'), 7)
        self.assertEqual(CHECK.checked_assumptions('Closed under the global context\n' * 7, 7), [])
        with self.assertRaises(ValueError):
            CHECK.checked_assumptions('Closed under the global context\n' * 6, 7)
        with self.assertRaises(ValueError):
            CHECK.checked_assumptions('Axioms:\nInjected : False\n' * 7, 7)


if __name__ == '__main__':
    unittest.main()
