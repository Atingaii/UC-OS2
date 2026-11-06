"""Static scope checks only; actual semantic gate is --coordinates."""
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage26-task-prio-coordinates'
spec = importlib.util.spec_from_file_location('coordinate_gate', ROOT / 'scripts/check-v293-task-prio-rekey.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


def nodes(value):
    if isinstance(value, dict):
        yield value
        for v in value.values():
            yield from nodes(v)
    elif isinstance(value, list):
        for v in value:
            yield from nodes(v)


class CoordinatesLocalTests(unittest.TestCase):
    def setUp(self):
        self.proof = (ROOT / CHECK.PROOF).read_text()
        self.probe = (ROOT / 'audit/probes/V293TaskPrioCoordinatesProbe.v').read_text()

    def header(self, name):
        return self.proof.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]

    def test_append_only_and_fixed_function(self):
        for path in CHECK.SOURCES:
            self.assertTrue((ROOT / path).read_bytes().startswith((LOG / (Path(path).name + '.before.txt')).read_bytes()))
        self.assertEqual((LOG / 'configured-function-identity.json').read_bytes(),
                         (ROOT / 'audit/logs/stage26-task-prio-nonnull-frame/configured-function-identity.json').read_bytes())
        base = json.loads((LOG / 'baseline.json').read_text())
        for path, sha in base['protected'].items():
            self.assertEqual(hashlib.sha256((ROOT / path).read_bytes()).hexdigest(), sha)

    def test_actual_clang_four_assignment_order_and_promotions(self):
        ast = json.loads((LOG / 'configured-coordinate-ast.json').read_text())
        self.assertEqual([n['inner'][0]['referencedDecl']['name'] for n in ast],
                         ['y_new', 'x_new', 'bity_new', 'bitx_new'])
        self.assertEqual([n['range']['begin']['presumedLine'] for n in ast], [110, 111, 116, 117])
        self.assertEqual([[x['opcode'] for x in nodes(n) if x.get('kind') == 'BinaryOperator'] for n in ast],
                         [['=', '>>'], ['=', '&'], ['=', '<<'], ['=', '<<']])
        ops = [[x for x in nodes(n) if x.get('opcode') in ['>>', '&', '<<']][0] for n in ast]
        self.assertEqual([x['type']['qualType'] for x in ops], ['int', 'unsigned int', 'unsigned long', 'unsigned long'])
        for n in ast:
            self.assertIn('IntegralCast', [x.get('castKind') for x in nodes(n)])

    def test_generic_entry_has_no_success_store_execution_or_result_oracle(self):
        entry, result = self.header('V293_task_prio_coordinates_execution').split('let M\' :=', 1)
        for forbidden in ['cstepstar', 'store ', 'V293_coordinate_memory', 'V293_prio_row', 'V293_prio_bit']:
            self.assertNotIn(forbidden, entry)
        self.assertIn('exists v, get M (b,0%Z) = Some (true,v)', entry)
        for expected in ['V293_task_prio_coordinates newprio yn xi byn xn', 'load Tint8 M\' (bn,0%Z)', 'get M\' a = get M a']:
            self.assertIn(expected, result)
        self.assertIn('p < 13', entry)
        self.assertIn('Int.shr', self.header('V293_coordinate_arithmetic'))
        self.assertIn('Int.shru', self.header('V293_coordinate_arithmetic'))

    def test_stale_four_values_restore_real_suffix_not_an_assumed_midstate(self):
        fixture = self.proof.split('Definition V293_coordinate_fixture_mem', 1)[1].split('Lemma ', 1)[0]
        self.assertEqual(fixture.count(' 255'), 4)
        restore = self.proof.split('Lemma V293_coordinate_fixture_restore', 1)[1].split('Qed.', 1)[0]
        self.assertIn('HalfPermMap.extensionality', restore)
        body = self.proof.split('Theorem V293_coordinate_update_witness', 1)[1].split('Qed.', 1)[0]
        self.assertIn('V293_coordinate_fixture_execution', body)
        self.assertIn('V293_tcb_update_frame_witness', body)
        self.assertIn('V293_rekey_sequence_execution', body)
        self.assertEqual(self.header('V293_coordinate_update_witness').count('->'), 2)

    def test_same_final_state_and_four_actual_controls(self):
        obs = self.proof.split('Definition V293_coordinate_update_observes', 1)[1].split('Theorem ', 1)[0]
        self.assertEqual(obs.count('Some (V293_byteval 255)'), 4)
        for token in ['V293_task_prio_coordinates_update', 'V293_table_loads', 'V293_rekey_bitmap_loads',
                      'V293_event_bitmap_loads', '(41%positive,59%Z) = Some (V293_byteval 6)',
                      '(41%positive,61%Z) = Some (V293_byteval 64)', '(Tcom_ptr 411%Z)',
                      'get (V293_coordinate_fixture_mem live elo ehi) (41%positive,i)']:
            self.assertIn(token, obs)
        for args in ['false 0 1 16 64 0 1', 'true 0 1 80 64 0 1', 'false 16 3 16 80 2 3', 'false 0 129 16 64 128 3']:
            self.assertIn(args, self.header('V293_coordinate_update_controls'))

    def test_probe_has_four_handwritten_literal_roots_not_candidate_helpers(self):
        self.assertEqual(self.probe.count('Print Assumptions checked_'), 4)
        for name in ['V293_task_prio_coordinates', 'V293_task_prio_coordinates_update',
                     'V293_coordinate_memory', 'V293_coordinate_update_observes', 'V293_coordinate_fixture_mem',
                     'V293_tcb_type', 'V293_prio_bit', 'V293_prio_row']:
            self.assertNotRegex(self.probe, r'\b' + name + r'\b')
        self.assertIn('Definition checked_coordinate_y', self.probe)
        self.assertIn('Definition checked_coordinate_observes', self.probe)

    def test_four_negatives_only_change_designated_header(self):
        cases = CHECK.mutations(self.proof, coordinates=True)
        self.assertEqual(len(cases), 4)
        for label, (candidate, decl) in cases.items():
            a = self.proof.index(decl)
            b = self.proof.index('Proof.', a)
            c = candidate.index('Proof.', a)
            self.assertEqual(self.proof[:a], candidate[:a], label)
            self.assertEqual(self.proof[b:], candidate[c:], label)
            self.assertNotEqual(self.proof[a:b], candidate[a:c], label)

    def test_assumption_parser_rejects_missing_or_unknown_axioms(self):
        self.assertEqual(CHECK.checked_assumptions('Closed under the global context\n' * 4, 4), [])
        for s in ['Closed under the global context\n' * 3, 'Axioms:\nInjected : False\n' * 4]:
            with self.assertRaises(ValueError):
                CHECK.checked_assumptions(s, 4)


if __name__ == '__main__':
    unittest.main()
