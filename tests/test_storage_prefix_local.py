"""Local prefix gate; these tests do not refresh the full function record."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('storage_prefix_local', ROOT / 'scripts/check-v293-storage-prefix.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


class StoragePrefixLocalTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / CHECK.SOURCE).read_text()

    def test_exact_three_prefix_semantic_factors(self):
        variants = CHECK.mutations(self.source)
        self.assertEqual(set(variants), {'reserve_half_omitted_only', 'target_assignment_omitted_only',
                                              'inputs_not_borrowed_only'})
        half, declaration = variants['reserve_half_omitted_only']
        start, end = self.source.index(declaration), self.source.index('Proof.', self.source.index(declaration))
        self.assertEqual(half[:start], self.source[:start])
        self.assertEqual(half[half.index('Proof.', start):], self.source[end:])
        skip, _ = variants['target_assignment_omitted_only']
        self.assertEqual(skip.replace('(sseq (scall sched_id nil) (sskip None))',
                                     '(V293_OSSched_unlocked_prefix sched_id table high target)'), self.source)

        unborrowed, declaration = variants['inputs_not_borrowed_only']
        self.assertEqual(declaration, 'Lemma V293_retained_storage_prefix_lend_value :')
        self.assertEqual(unborrowed.replace('[intros st H; exact H | intros st H;',
                                           '[apply V293_inputs_borrow | intros st H;'), self.source)

    def test_only_physical_current_changes_in_witness_control(self):
        witness = (ROOT / CHECK.WITNESS).read_text()
        changed, declaration = CHECK.witness_mutation(witness)
        self.assertEqual(declaration, 'Lemma V293_storage_prefix_shared_witness :')
        self.assertEqual(changed.replace(
            'merge (V293_encoded_memory 6%positive 0 true (encode_val (Tptr Tvoid) (Vptr V293_current_next)))',
            'merge (V293_encoded_memory 6%positive 0 true (encode_val (Tptr Tvoid) (Vptr V293_idle_tid)))'), witness)
        self.assertIn('V293_encoded_memory 10%positive 0 true (encode_val (Tptr Tvoid) (Vptr V293_idle_tid))', changed)

    def test_closed_entry_requires_same_state_snapshot_and_actual_memory_witness(self):
        entry = self.source.split('Definition V293_prefix_entry_snapshot', 1)[1].split(
            'Lemma V293_prefix_entry_close', 1)[0]
        self.assertIn('SWINV (V293_storage_inv V293_prefix_cells target tp) //\\', entry)
        self.assertIn('V293_storage_open target tp tid tasks events now old **', entry)
        witness = (ROOT / CHECK.WITNESS).read_text()
        self.assertIn('forall different events now aop,', witness)
        self.assertIn('set (M := V293_storage_prefix_memory different)', witness)
        self.assertIn('exists s.', witness)
        self.assertNotIn('False ->', witness)
        self.assertIn('Definition checked_entry old hv', (ROOT / CHECK.PROBE).read_text())

    def test_missing_or_duplicate_anchor_rejected(self):
        for candidate in ['', 'x x']:
            with self.assertRaises(ValueError):
                CHECK.replace_once(candidate, 'x', 'y')

    def test_ready_controls_change_only_one_prospective_factor(self):
        variants = CHECK.ready_mutations(self.source)
        self.assertEqual(set(variants), {'ready_bitmap_relation_neutralized_only',
            'ready_table_task_relation_neutralized_only', 'critical_entry_primitive_omitted_only',
            'ready_abstract_current_update_omitted_only'})
        start = self.source.index('Definition V293_ready_resources ')
        end = self.source.index('Definition V293_ready_core ', start)
        for name, before, after in [
            ('ready_bitmap_relation_neutralized_only', 'V293_bitmap_tasks lo hi tasks', 'True'),
            ('ready_table_task_relation_neutralized_only', 'V293_priority_table entries tasks',
                'V293_priority_table entries TcbMod.emp')]:
            changed, declaration = variants[name]
            expected = (self.source[:start] + self.source[start:end].replace(before, after, 1)
                        + self.source[end:])
            self.assertEqual(changed, expected)
            self.assertEqual(declaration, 'Theorem V293_ready_core_snapshot :')
        changed, declaration = variants['critical_entry_primitive_omitted_only']
        start = self.source.index(declaration)
        end = self.source.index('Proof.', start)
        self.assertEqual(changed, self.source[:start] + self.source[start:end].replace(
            '(sprim encrit)', '(sskip None)', 1) + self.source[end:])
        changed, declaration = variants['ready_abstract_current_update_omitted_only']
        start = self.source.index(declaration)
        end = self.source.index('Proof.', start)
        self.assertEqual(changed, self.source[:start] + self.source[start:end].replace(
            'set O curtid (oscurt t)', 'O', 1) + self.source[end:])

    def test_ready_entry_has_no_frozen_ready_snapshot_in_precondition(self):
        probe = (ROOT / CHECK.PROBE).read_text()
        entry = probe.split('Definition checked_ready_enter :', 1)[1].split('End ReadyInvariant.', 1)[0]
        self.assertIn('(<||aop||> ** OS[(fun _ : hid => false), true, nil, critical] ** ATopis INUM ** P)', entry)
        self.assertIn('(sprim encrit)', entry)
        self.assertIn('false, nil, true::critical] ** snapshot ** P)', entry)
        self.assertIn('getinv ((V293_ready_inv bt bg br bh bp tp rest target) k)', probe)
        self.assertIn('GoodI (V293_ready_inv', probe)
        self.assertNotIn('V293_ready_resources', probe)
        self.assertNotIn('V293_ready_snapshot ', probe)

    def test_roundtrip_controls_pin_three_distinct_primitives_at_composition_root(self):
        variants = CHECK.roundtrip_mutations(self.source)
        factors = {
            'roundtrip_entry_omitted_only': '(sprim encrit)',
            'roundtrip_call_assignment_omitted_only':
                '(V293_OSSched_unlocked_prefix sched_id table high target)',
            'roundtrip_exit_omitted_only': '(sprim excrit)',
        }
        self.assertEqual(set(variants), set(factors))
        for name, factor in factors.items():
            changed, declaration = variants[name]
            self.assertEqual(declaration, 'Theorem V293_ready_OSSched_critical_prefix :')
            start = self.source.index(declaration)
            end = self.source.index('Proof.', start)
            self.assertEqual(changed, self.source[:start] +
                self.source[start:end].replace(factor, '(sskip None)', 1) + self.source[end:])

    def test_ready_execution_and_roundtrip_are_literal_same_invariant_interfaces(self):
        probe = (ROOT / CHECK.PROBE).read_text()
        for name in ['checked_ready_prefix', 'checked_ready_roundtrip']:
            header = probe.split('Definition ' + name + ' :', 1)[1].split(':=', 1)[0]
            self.assertIn('V293_ready_inv bt bg br bh bp tp rest target', header)
            self.assertIn('(scall sched_id nil)', header)
            self.assertIn('(sassign (evar target) (earrayelem (evar table) (evar high)))', header)
            self.assertNotIn('V293_storage_inv', header)
        header = probe.split('Definition checked_ready_roundtrip :', 1)[1].split(':=', 1)[0]
        pre = header.split(' r ri\n', 1)[1].split('(sseq (sprim encrit)', 1)[0]
        self.assertIn('OS[(fun _ : hid => false), true, nil, critical]', pre)
        self.assertIn('CurTid tid', pre)
        for frozen in ['lo', 'hi', 'tasks', 'entries', 'snapshot']:
            self.assertNotRegex(pre, r'\b' + frozen + r'\b')
        self.assertIn('(sprim excrit)', header)
        self.assertIn('SWINV (V293_ready_inv', probe.split('Let chosen tid', 1)[1])
        self.assertIn('V293_ready_prefix_execution_witness', (ROOT / CHECK.WITNESS).read_text())

    def test_rejection_requires_exact_file_and_declared_range(self):
        candidate, declaration = CHECK.mutations(self.source)['reserve_half_omitted_only']
        line = candidate[:candidate.index(declaration)].count('\n') + 1
        path = Path('/tmp/local-prefix/candidate') / Path(CHECK.SOURCE).name
        output = f'File "{path}", line {line}, characters 0-1:\nError: mismatch\n'
        result = CHECK.check_rejection(1, output, candidate, declaration, path)
        self.assertFalse(result['downstream_credit'])
        for code, text in [(0, output), (124, output),
                           (1, output.replace('Error:', 'Warning:')),
                           (1, output.replace('/candidate/', '/unrelated/')),
                           (1, output.replace(f'line {line}', 'line 1'))]:
            with self.subTest(code=code, text=text), self.assertRaises(ValueError):
                CHECK.check_rejection(code, text, candidate, declaration, path)

    def test_unknown_assumptions_cannot_hide_in_actual_output(self):
        valid = ('Axioms:\nClassical_Prop.classic : forall P : Prop, P \\/ ~ P\n'
                 'FunctionalExtensionality.functional_extensionality_dep\n  : forall A : Type, A = A\n')
        assumptions = CHECK.checked_assumptions(valid * CHECK.ROOT_COUNT)
        self.assertEqual(set(assumptions), {'Classical_Prop.classic',
            'FunctionalExtensionality.functional_extensionality_dep'})
        for changed in [valid * (CHECK.ROOT_COUNT - 1), valid * CHECK.ROOT_COUNT + 'evil : False\n', valid * CHECK.ROOT_COUNT + 'Bad.evil : False\n']:
            with self.subTest(output=changed), self.assertRaises(ValueError):
                CHECK.checked_assumptions(changed)

    def test_fixed_probe_pins_both_permissions_and_actual_call_assignment(self):
        probe = (ROOT / CHECK.PROBE).read_text()
        self.assertIn('checked_array false b offset step tau vs ** checked_array false b offset step tau vs ==>', probe)
        self.assertIn('(sseq (scall sched_id nil) (sassign (evar target) (earrayelem (evar table) (evar high))))', probe)
        self.assertNotIn('V293_storage_prefix_borrowed', probe)
        self.assertNotIn('V293_storage_prefix_closed', probe)
        self.assertNotIn('V293_prefix_cells', probe)
        self.assertNotIn('False ->', probe)
        self.assertEqual(probe.count('Print Assumptions '), CHECK.ROOT_COUNT)

    def test_pointer_typing_is_explicit_and_not_inferred_from_table_membership(self):
        self.assertIn('Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->', self.source)
        model = (ROOT / 'certiucos/v293/model/V293SchedulerTasks.v').read_text()
        table = model.split('Definition V293_priority_table', 1)[1].split('Definition V293_highest_ready', 1)[0]
        self.assertNotIn('rule_type_val_match', table)


if __name__ == '__main__':
    unittest.main()
