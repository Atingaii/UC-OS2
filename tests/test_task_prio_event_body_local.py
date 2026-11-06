"""Structure checks only; real coqc/coqchk gate is --event-body."""
import importlib.util
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('event_body_check', ROOT/'scripts/check-v293-task-prio-rekey.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


class EventBodyLocalTests(unittest.TestCase):
    def setUp(self):
        self.proof = (ROOT/CHECK.PROOF).read_text()
        self.probe = (ROOT/'audit/probes/V293TaskPrioEventBodyProbe.v').read_text()

    def header(self, name):
        return re.split(r'(?:Theorem|Lemma) '+name+r' :', self.proof, maxsplit=1)[1].split('Proof.', 1)[0]

    def test_frozen_source_actual_fields_and_same_function(self):
        out = ROOT/'audit/logs/stage26-task-prio-event-body'
        identity = json.loads((out/'source-identity.json').read_text())
        self.assertTrue(identity['function_record_matches_frozen'])
        ast = json.loads((out/'configured-event-ast.json').read_text())
        self.assertEqual(ast['read_field']['name'], 'OSTCBEventPtr')
        self.assertEqual(ast['independent_if']['inner'][0]['opcode'], '!=')
        fields = json.loads((out/'configured-event-record.json').read_text())['inner']
        self.assertEqual([x['name'] for x in fields if x.get('kind') == 'FieldDecl'],
                         ['OSEventType', 'OSEventPtr', 'OSEventCnt', 'OSEventGrp', 'OSEventTbl'])

    def test_row_address_is_real_nonzero_base_field_array(self):
        h = self.header('V293_event_row_eval')
        self.assertIn('efield (ederef (evar pevent)) 5%Z', h)
        self.assertIn('Int.repr (base+11+Z.of_nat y)', h)
        self.assertIn('evaladdr', h)
        h = self.header('V293_event_group_eval')
        self.assertIn('efield (ederef (evar pevent)) 4%Z', h)
        self.assertIn('Int.repr (base+10)', h)

    def test_body_no_intermediate_store_execution_oracle(self):
        h = self.header('V293_task_prio_event_then_execution')
        entry, out = h.split("let M' :=", 1)
        for oracle in ['store ', 'cstepstar', 'evalval', 'evaladdr']:
            self.assertNotIn(oracle, entry)
        self.assertIn('V293_event_bitmap_writable M be base', entry)
        self.assertIn('V293_task_prio_event_then pevent', out)
        self.assertIn("V293_event_bitmap_loads M'", out)
        self.assertIn('i < base+10', out)
        self.assertIn('base+12 < i', out)

    def test_read_if_body_one_memory_chain(self):
        h = self.header('V293_task_prio_event_nonnull_execution')
        entry, out = h.split('exists Me,', 1)
        for oracle in ['store ', 'cstepstar', 'evalval', 'Mf', 'Me']:
            self.assertNotIn(oracle, entry)
        for needed in ['V293_bytes_writable M bp', 'V293_event_bitmap_writable M be',
                       'c <> bp', 'load (Tcom_ptr 411%Z) M']:
            self.assertIn(needed, entry)
        self.assertIn('V293_event_rekey_memory Me', out)
        self.assertIn('V293_task_prio_event ptcb pevent', out)
        self.assertIn('get Mf (c,i) = get M (c,i)', out)

    def test_simultaneous_actual_entry_and_execution_not_just_computed_bitmap(self):
        h = self.header('V293_event_body_fixture_entry')
        self.assertIn('Some (Vptr (71%positive,Int.repr 3))', h)
        self.assertIn('Some (Vptr (72%positive,Int.repr 5))', h)
        self.assertIn('V293_rekey_locals', h)
        obs = self.proof.split('Definition V293_event_nonnull_observes', 1)[1].split('Theorem ', 1)[0]
        self.assertIn('cstepstar', obs)
        self.assertIn('V293_rekey_bitmap_loads Mf 30%positive 31%positive 16 0 1', obs)
        controls = self.header('V293_event_nonnull_physical_controls')
        for case in ['0 1 8 6 64 0 1', '0 1 8 10 0 4 2', '20 0 2 6 80 0 1', '0 129 8 6 64 128 3']:
            self.assertIn(case, controls)
        self.assertNotIn('->', controls)

    def test_static_literal_probe_does_not_use_candidate_aliases_in_expected_types(self):
        for alias in ['V293_event_type', 'V293_event_fields', 'V293_task_prio_event_then',
                      'V293_task_prio_event', 'V293_event_rekey_memory', 'V293_event_bitmap_loads',
                      'V293_event_body_fixture_mem', 'V293_event_body_fixture_le',
                      'V293_ready_rekey_rows', 'V293_rekey_locals', 'V293_event_nonnull_observes']:
            self.assertNotRegex(self.probe, r'\b'+alias+r'\b')
        self.assertIn('Definition checked_event_then', self.probe)
        self.assertIn('Definition checked_body_mem', self.probe)
        self.assertIn('Definition checked_event_memory', self.probe)

    def test_four_single_header_controls_keep_original_suffix(self):
        cases = CHECK.mutations(self.proof, event_body=True)
        self.assertEqual(len(cases), 4)
        for label, (candidate, declaration) in cases.items():
            a = self.proof.index(declaration)
            b = self.proof.index('Proof.', a)
            c = candidate.index('Proof.', a)
            self.assertEqual(self.proof[:a], candidate[:a], label)
            self.assertEqual(self.proof[b:], candidate[c:], label)
            self.assertNotEqual(self.proof[a:b], candidate[a:c], label)

    def test_seven_real_assumptions_prints_unknown_axioms_rejected(self):
        self.assertEqual(self.probe.count('Print Assumptions checked_'), 7)
        self.assertEqual(CHECK.checked_assumptions('Closed under the global context\n'*7, 7), [])
        for output in ['Closed under the global context\n'*6, 'Axioms:\nInjected : False\n'*7]:
            with self.assertRaises(ValueError):
                CHECK.checked_assumptions(output, 7)


if __name__ == '__main__':
    unittest.main()
