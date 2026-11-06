"""Structure/parser checks supplement actual Coq; they are not proof evidence."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('task_rekey_local', ROOT / 'scripts/check-v293-task-prio-rekey.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


class TaskPrioRekeyTests(unittest.TestCase):
    def setUp(self):
        self.proof = (ROOT / CHECK.PROOF).read_text()
        self.probe = (ROOT / CHECK.PROBE).read_text()

    def header(self, name):
        return self.proof.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]

    def test_literal_translation_has_two_ordered_assignments(self):
        # Check exactly the original two-write fragment, not later independent definitions.
        code = (ROOT / CHECK.CODE).read_text().split('Definition V293_task_prio_rekey', 1)[1].split('Definition ', 1)[0]
        self.assertIn('sseq (sassign (earrayelem (evar table) (evar oldprio)) enull)', code)
        self.assertIn('(sassign (earrayelem (evar table) (evar newprio)) (evar ptcb))', code)
        self.assertEqual(code.count('sassign'), 2)
        self.assertNotIn('sprim', code)

    def test_execution_constructs_stores_from_real_operands_and_permissions(self):
        head = self.header('V293_OSTaskChangePrio_table_execution')
        before, after = head.split('exists M1 M2,')
        self.assertNotIn('store (', before)
        for token in ['old <> new ->', 'b <> bo -> b <> bn -> b <> bc ->',
                      'load Tint8 M (bo,0%Z)', 'load (Tptr tp) M (bc,0%Z)',
                      'V293_bytes_writable M b (4*Z.of_nat old)%Z 4 ->',
                      'V293_bytes_writable M b (4*Z.of_nat new)%Z 4 ->']:
            self.assertIn(token, before)
        self.assertIn('cstepstar', after)
        self.assertIn('get M2 (other,j) = get M (other,j)', after)

    def test_choice_does_not_hide_postbitmap_and_task_obligations(self):
        head = self.header('V293_task_prio_rekey_ready_choice')
        for token in ['V293_table_loads tp M b entries ->', 'V293_bitmap_tasks lo hi tasks ->',
                      'V293_priority_table', 'store (Tptr tp) M1',
                      'load (Tptr tp) M2', 'V293_ready_select']:
            self.assertIn(token, head)
        self.assertNotIn('GOOD_OS', head)

    def test_alias_is_semantic_not_a_full_api_execution(self):
        head = self.header('V293_task_prio_rekey_alias_control')
        self.assertEqual(head.count('store (Tptr tp)'), 2)
        self.assertIn('= Some (Vptr next)', head)
        self.assertIn('<> Some Vnull', head)
        self.assertNotIn('cstepstar', head)
        fixture = self.header('V293_task_prio_rekey_fixture_execution')
        self.assertIn('32%Z', fixture)
        self.assertIn('24%Z', fixture)
        self.assertNotIn('->', fixture)
        self.assertIn('cstepstar', fixture)

    def test_six_independent_interfaces_use_literal_ast(self):
        self.assertEqual(self.probe.count('Print Assumptions checked_'), 6)
        self.assertNotIn('V293_task_prio_rekey table', self.probe)
        self.assertNotIn('V293_task_prio_rekey 200', self.probe)
        self.assertNotIn('type of', self.probe)
        self.assertIn('sseq (sassign (earrayelem', self.probe)
        self.assertIn('Some (true,v)', self.probe)

    def test_four_mutations_preserve_all_proof_suffixes(self):
        controls = CHECK.mutations(self.proof)
        self.assertEqual(len(controls), 4)
        for label, (candidate, declaration) in controls.items():
            with self.subTest(label=label):
                start = self.proof.index(declaration)
                end = self.proof.index('Proof.', start)
                candidate_end = candidate.index('Proof.', start)
                self.assertEqual(candidate[:start], self.proof[:start])
                self.assertEqual(candidate[candidate_end:], self.proof[end:])
                self.assertNotEqual(candidate[start:candidate_end], self.proof[start:end])

    def test_assumption_count_and_unknown_trust_fail_closed(self):
        output = 'Axioms:\nClassical_Prop.classic : forall P : Prop, P \\/ ~ P\n' * 6
        self.assertEqual(CHECK.checked_assumptions(output), ['Classical_Prop.classic'])
        for altered in [output.rsplit('Axioms:', 1)[0], output + 'Unapproved.trust : False\n']:
            with self.assertRaises(ValueError):
                CHECK.checked_assumptions(altered)

    def test_strict_rejection_location_and_exit_status(self):
        candidate, declaration = next(iter(CHECK.mutations(self.proof).values()))
        path = Path('/tmp/rekey-designated.v')
        line = candidate[:candidate.index('Proof.', candidate.index(declaration))].count('\n') + 2
        output = f'File "{path}", line {line}, characters 0-1:\nError: type mismatch\n'
        self.assertFalse(CHECK.CHECK.check_rejection(1, output, candidate, declaration, path)['downstream_credit'])
        for code, altered in [(0, output), (1, output.replace(str(line), '1')),
                              (1, output.replace(str(path), '/tmp/wrong.v'))]:
            with self.assertRaises(ValueError):
                CHECK.CHECK.check_rejection(code, altered, candidate, declaration, path)


if __name__ == '__main__':
    unittest.main()
