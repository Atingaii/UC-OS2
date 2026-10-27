"""Literal shared-storage contracts and designated, single-factor controls."""
import copy
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / name)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


STORAGE = load('v293-scheduler-storage.py')
CALLER = load('v293-scheduler-caller.py')


class SchedulerStorageTests(unittest.TestCase):
    def setUp(self):
        self.state, self.core, self.witness = [(ROOT / p).read_text() for p in STORAGE.FILES]
        self.variants = STORAGE.mutations(self.state, self.core, self.witness, CALLER.replace_once)

    def test_exact_four_factors_only_new_tail_changes(self):
        self.assertEqual(set(self.variants), set(STORAGE.OBLIGATIONS))
        self.assertEqual(set(self.variants), set(STORAGE.CONTROLS))
        self.assertEqual(len(self.variants), 4)
        for state, core, witness, _, _ in self.variants.values():
            self.assertEqual(state, self.state)
            self.assertEqual(witness, self.witness)
            self.assertNotEqual(core, self.core)

    def test_only_returned_invariant_footprint_changes(self):
        _, core, _, _, _ = self.variants['storage_omitted_only']
        self.assertEqual(core.replace('V293_storage_inv nil target tp',
                                      'V293_storage_inv cells target tp'), self.core)

    def test_only_intermediate_increment_ast_changes_to_well_typed_skip(self):
        _, core, _, _, _ = self.variants['increment_omitted_only']
        self.assertEqual(core.replace('(sskip None)', '(V293_OSSched_increment counter)'), self.core)
        self.assertIn('| sskip : option val -> stmts', (ROOT / 'framework/model/language.v').read_text())

    def test_only_resumed_counter_claim_changes(self):
        _, core, _, _, _ = self.variants['frozen_counter_post_only']
        self.assertEqual(core.replace(
            '(V293_storage_resumed ** PV (bcounter, Int.zero) @ Tint32 |-> (Vint32 (Int.add c Int.one))) tid.',
            'V293_storage_resumed tid.'), self.core)

    def test_only_false_premise_and_introduction_change(self):
        _, core, _, _, _ = self.variants['extra_false_only']
        self.assertEqual(core.replace('  False -> indom tasks tid ->', '  indom tasks tid ->')
                         .replace('intros Spec r ri c Hfalse Hmem', 'intros Spec r ri c Hmem'), self.core)
        self.assertNotIn('False ->', STORAGE.PROBE)

    def test_all_roots_have_independently_written_fixed_contracts(self):
        self.assertEqual(len(STORAGE.ROOTS), 6)
        for root in STORAGE.ROOTS:
            self.assertIn('Definition checked_' + root + ' :', STORAGE.PROBE)
        self.assertNotIn('Print ', STORAGE.PROBE)
        for candidate in ['V293_storage_tail ', 'V293_storage_switch_payload ',
                          'V293_storage_resumed ', 'V293_storage_open ']:
            self.assertNotIn(candidate, STORAGE.PROBE)

    def test_literal_storage_requires_full_typed_cells_without_unbounded_frame(self):
        start = STORAGE.PROBE.index('Fixpoint checked_storage')
        end = STORAGE.PROBE.index('Definition checked_fields')
        literal = STORAGE.PROBE[start:end]
        self.assertIn('Amapsto a tau true v', literal)
        self.assertIn('rule_type_val_match tau v = true', literal)
        self.assertNotIn('Atrue', literal)
        self.assertNotIn('V293_storage ', literal)

    def test_increment_remains_precise_before_switch(self):
        self.assertIn('(tail c) (V293_OSSched_increment counter) (tail (Int.add c Int.one))', STORAGE.PROBE)
        self.assertIn('(sseq (V293_OSSched_increment counter) (sprim (switch target)))', STORAGE.PROBE)
        self.assertNotIn('suffix', STORAGE.PROBE)

    def test_resumed_private_frame_contains_no_physical_counter_value(self):
        resumed = STORAGE.PROBE.split('Let resumed :=', 1)[1].split('Lemma checked_storage_equal', 1)[0]
        self.assertIn('SWINVt (V293_storage_inv cells target tp)', resumed)
        self.assertIn('(binding ** px)', resumed)
        self.assertNotIn('Vint32', resumed)
        self.assertNotIn('PV ', resumed)

    def test_same_state_full_pending_entry_for_both_modes_and_any_counter(self):
        entry = STORAGE.PROBE.split('Definition checked_V293_storage_increment_entry_witness', 1)[1]
        self.assertIn('forall different c events now aop', entry)
        self.assertIn('exists s,', entry)
        self.assertIn('<||sched;;aop||>', entry)
        self.assertIn('PV (3%positive, Int.zero) @ Tint32 |-> (Vint32 c) ** Aemp', entry)
        self.assertIn('CurTid V293_idle_tid', entry)
        self.assertIn('Agvarenv 111%Z Tint32', entry)

    def test_precise_invariant_proves_actual_store_preservation(self):
        self.assertIn('apply precise_star', self.state)
        self.assertIn('V293_storage_store', self.state)
        self.assertIn('store (Tptr tp) M', self.state)
        self.assertIn('set O curtid (oscurt t)', self.state)
        self.assertIn('apply V293_storage_tail_return.', self.core)
        self.assertIn('eapply switch_rule', self.core)

    def test_sources_and_checker_registered(self):
        for rel in STORAGE.FILES:
            self.assertIn(rel, (ROOT / '_CoqProject').read_text().splitlines())
        gate = (ROOT / 'scripts/check-v293-functions.py').read_text()
        self.assertIn("'scripts/v293-scheduler-storage.py'", gate)
        self.assertIn("report['scheduler_storage_checkpoint'] = storage.check", gate)
        self.assertIn("report['scheduler_storage_checkpoint'], checks, load", gate)

    def test_bounded_scope_not_full_function_kernel_or_global_layout(self):
        self.assertIn('NOT_FULL_OS_SCHED_OR_GOOD_OS', STORAGE.SCOPE)
        self.assertIn('empty extra-cell list, not all kernel globals', self.witness)
        for name in ['storage_omitted_only', 'increment_omitted_only', 'frozen_counter_post_only']:
            self.assertIn('NOT_DOWNSTREAM_CREDIT', STORAGE.CONTROLS[name])

    def test_rejection_requires_exact_declaration_range(self):
        for label, (state, core, witness, rel, decl) in self.variants.items():
            source = STORAGE.PROBE if rel is None else core
            for offset in [source.index(decl), source.index('Qed.', source.index(decl))]:
                line = source[:offset].count('\n') + 1
                file = rel or 'checks/Contract.v'
                row = dict(exit_code=1, stderr=f'File "/tmp/{file}", line {line}, characters 0-1:\nError: mismatch\n')
                STORAGE.check_rejection(row, source, rel, decl, label)

    def test_success_timeout_unrelated_file_or_parse_warning_not_credit(self):
        _, source, _, rel, decl = self.variants['increment_omitted_only']
        line = source[:source.index(decl)].count('\n') + 2
        row = dict(exit_code=1, stderr=f'File "/tmp/{rel}", line {line}, characters 0-1:\nError: mismatch\n')
        for change in [dict(exit_code=0), dict(exit_code=124),
                       dict(stderr=row['stderr'].replace('Error:', 'Warning:')),
                       dict(stderr=row['stderr'].replace(rel, 'unrelated.v')),
                       dict(stderr=row['stderr'].replace(f'line {line}', 'line 1'))]:
            test = copy.deepcopy(row); test.update(change)
            with self.subTest(change=change), self.assertRaises(ValueError):
                STORAGE.check_rejection(test, source, rel, decl, 'increment_omitted_only')


if __name__ == '__main__':
    unittest.main()
