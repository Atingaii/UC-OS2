"""Static regression checks; Coq execution/assumptions gate is --tcb-update."""
import importlib.util
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT/'audit/logs/stage26-task-prio-tcb-update'
spec = importlib.util.spec_from_file_location('tcb_update_gate', ROOT/'scripts/check-v293-task-prio-rekey.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


class TCBUpdateLocalTests(unittest.TestCase):
    def setUp(self):
        self.proof = (ROOT/CHECK.PROOF).read_text()
        self.code = (ROOT/CHECK.CODE).read_text()
        self.probe = (ROOT/'audit/probes/V293TaskPrioTCBUpdateProbe.v').read_text()

    def header(self, name):
        return self.proof.split('Theorem '+name+' :', 1)[1].split('Proof.', 1)[0]

    def test_same_frozen_source_and_exact_five_assignment_order(self):
        self.assertTrue(json.loads((LOG/'source-identity.json').read_text())['source_hashes_match_frozen'])
        self.assertEqual((LOG/'configured-function-identity.json').read_bytes(),
                         (ROOT/'audit/logs/stage26-task-prio-event-prefix/configured-function-identity.json').read_bytes())
        ast = json.loads((LOG/'configured-tcb-update-ast.json').read_text())
        self.assertEqual([n['inner'][0]['name'] for n in ast],
                         ['OSTCBPrio', 'OSTCBY', 'OSTCBX', 'OSTCBBitY', 'OSTCBBitX'])
        layout = (LOG/'clang-source-record-layouts.log').read_text()
        for offset, name in [(50, 'OSTCBPrio'), (52, 'OSTCBY'), (51, 'OSTCBX'),
                             (54, 'OSTCBBitY'), (53, 'OSTCBBitX')]:
            self.assertRegex(layout, rf'\b{offset} \|[^\n]*\b{name}\b')

    def test_old_code_and_proof_prefixes_remain_byte_identical(self):
        for source in [CHECK.CODE, CHECK.PROOF]:
            self.assertTrue((ROOT/source).read_bytes().startswith((LOG/(Path(source).name+'.before.txt')).read_bytes()))

    def test_real_five_statements_use_index_not_mask_for_x(self):
        body = self.code.split('Definition V293_task_prio_tcb_update', 1)[1].split('Definition ', 1)[0]
        self.assertEqual(re.findall(r'efield \(ederef \(evar ptcb\)\) (\d+)%Z', body), ['16','18','17','20','19'])
        for field, rhs in [(16,'newprio'), (18,'yn'), (17,'xi'), (20,'byn'), (19,'xn')]:
            self.assertIn(f'{field}%Z) (evar {rhs})', body)
        self.assertIn('sseq (V293_task_prio_prefix_event table', self.code)

    def test_entry_has_resources_not_execution_store_or_poststate_oracles(self):
        for name, split in [('V293_task_prio_tcb_update_execution', "let M' :="),
                            ('V293_task_prio_prefix_event_update_execution', 'exists Mg,')]:
            entry, out = self.header(name).split(split, 1)
            for oracle in ['cstepstar', 'store ', 'evalval', 'V293_tcb_updated_loads', ' Mh ', ' Mg ']:
                self.assertNotIn(oracle, entry)
            self.assertIn('V293_tcb_update_writable M bt base', entry)
            self.assertIn('V293_tcb_updated_loads', out)
        h = self.header('V293_task_prio_prefix_event_update_execution')
        for observable in ['V293_rekey_bitmap_loads Mh', 'V293_event_bitmap_loads Mh',
                           'V293_table_loads V293_tcb_type Mh', 'get Mh (c,i) = get M (c,i)']:
            self.assertIn(observable, h)

    def test_static_probe_does_not_alias_candidate_program_memory_or_contracts(self):
        for alias in ['V293_tcb_type', 'V293_task_prio_tcb_update', 'V293_task_prio_prefix_event_update',
                      'V293_tcb_update_memory', 'V293_tcb_update_bindings', 'V293_tcb_update_writable',
                      'V293_tcb_updated_loads', 'V293_tcb_update_fixture_le', 'V293_tcb_update_fixture_mem',
                      'V293_tcb_update_observes', 'V293_rekey_locals']:
            self.assertNotRegex(self.probe, r'\b'+alias+r'\b')
        for definition in ['checked_update', 'checked_all', 'checked_entry_mem', 'checked_updated',
                           'checked_five', 'checked_continuous', 'checked_observes']:
            self.assertIn('Definition '+definition, self.probe)

    def test_real_continuous_witness_only_assumes_byte_bounds(self):
        self.assertEqual(self.header('V293_tcb_update_continuous_witness').count('->'), 2)
        obs = self.proof.split('Definition V293_tcb_update_observes', 1)[1].split('Theorem ', 1)[0]
        for offset, value in [(58,6), (60,0), (59,6), (62,1), (61,64)]:
            self.assertIn(f'load Tint8 Mh (41%positive,{offset}%Z) = Some (V293_byteval {value})', obs)
        self.assertIn('cstepstar', obs)
        controls = self.header('V293_tcb_update_continuous_controls')
        for case in ['false 0 1 16 64 0 1', 'true 0 1 80 64 0 1',
                     'false 16 3 16 80 2 3', 'false 0 129 16 64 128 3']:
            self.assertIn(case, controls)

    def test_four_single_header_controls_keep_entire_original_proof_suffix(self):
        cases = CHECK.mutations(self.proof, tcb_update=True)
        self.assertEqual(len(cases), 4)
        for label, (candidate, declaration) in cases.items():
            a = self.proof.index(declaration)
            b = self.proof.index('Proof.', a)
            c = candidate.index('Proof.', a)
            self.assertEqual(self.proof[:a], candidate[:a], label)
            self.assertEqual(self.proof[b:], candidate[c:], label)
            self.assertNotEqual(self.proof[a:b], candidate[a:c], label)

    def test_four_actual_assumption_outputs_and_unknown_axiom_rejected(self):
        self.assertEqual(self.probe.count('Print Assumptions checked_'), 4)
        self.assertEqual(CHECK.checked_assumptions('Closed under the global context\n'*4, 4), [])
        for output in ['Closed under the global context\n'*3, 'Axioms:\nInjected : False\n'*4]:
            with self.assertRaises(ValueError):
                CHECK.checked_assumptions(output, 4)


if __name__ == '__main__':
    unittest.main()
