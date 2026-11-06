"""Source-structure checks, not a replacement for Coq kernel validation."""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
PROOF = ROOT / 'certiucos/v293/proofs/V293TCBFieldsHoare.v'
PROBE = ROOT / 'audit/probes/V293TCBFieldsHoareProbe.v'

class TCBFieldsHoareTests(unittest.TestCase):
    def test_no_new_assumptions_or_old_probe_imports(self):
        for path in [PROOF, PROBE]:
            text = path.read_text()
            self.assertIsNone(re.search(r'\b(Axiom|Parameter|Conjecture|Admitted|admit)\b', text))
            self.assertNotRegex(text, r'Require Import CertiOS\.audit\.probes\.')

    def test_stable_interfaces_use_actual_segment_without_execution_oracle(self):
        text = PROOF.read_text()
        for name in ['V293_OS_TCBInit_fields_hoare', 'V293_OS_TCBInit_fields_semantics',
                     'V293_OS_TCBInit_fields_records_hoare']:
            tail = text[text.index('Theorem ' + name):]
            statement = tail[:tail.index('Proof.')]
            self.assertIn('(V293_TCBInit_fields ptcb prio ptos pbos id stk_size pext opt)', statement)
            self.assertIn('V293_tcb_init_old_fields bt base old', statement)
            self.assertIn('(R ==> CurLINV li tid)', statement)
            self.assertNotRegex(statement, r'\b(evalval|evaladdr|exec|sfexec|V293_exec|V293_stmt_exec)\b')
        self.assertIn('apply RuleSound', text)

    def test_all_real_stores_derive_assignments(self):
        text = PROOF.read_text()
        self.assertEqual([int(n) for n in re.findall(r'^ V293_tcb_fields_store (\d+)', text, re.M)], list(range(18)))
        self.assertIn('eapply assign_rule', text)
        self.assertIn('eapply seq_rule', text)
        self.assertIn('apply V293_rdy_cell_in', text)

    def test_masks_read_just_written_coordinates(self):
        text = PROOF.read_text()
        for index in [13, 14]:
            start = text.index(' V293_tcb_fields_store ' + str(index))
            end = text.index(' V293_tcb_fields_store ' + str(index + 1))
            part = text[start:end]
            self.assertIn('V293_tcb_init_read Owned', part)
            self.assertIn('V293_tcb_init_mask_eval', part)

    def test_records_and_independent_nonempty_joint_entries(self):
        text = PROOF.read_text()
        self.assertIn('get tasks (bt,Int.repr base)=None', text)
        self.assertIn('apply V293_initialized_ready_record', text)
        self.assertIn('V293_task_records_insert tasks', text)
        probe = PROBE.read_text()
        for name in ['FieldsLiteralEntry', 'FieldsPriorityRead', 'FieldsWrongPriorityRead',
                     'RecordsLiteralEntry', 'RecordsFresh']:
            self.assertIn('Theorem ' + name, probe)
        for name in ['FieldsChecked', 'RecordsChecked']:
            self.assertIn('Definition ' + name, probe)
        self.assertIn('Definition RecordsExisting', probe)
        self.assertIn('Definition FieldsSentinel', probe)

    def test_exactly_once_in_active_build(self):
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(str(PROOF.relative_to(ROOT))), 1)

if __name__ == '__main__':
    unittest.main()
