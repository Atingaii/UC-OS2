"""Prospective ownership controls; no function-coverage credit for this core."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]


def load(root, name):
    spec = importlib.util.spec_from_file_location(name, root / 'scripts' / name)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


SHARED = load(ROOT, 'v293-shared-state.py')
CALLER = load(ROOT, 'v293-scheduler-caller.py')


class SharedStateTests(unittest.TestCase):
    def setUp(self):
        self.core = (ROOT / SHARED.CORE).read_text()
        self.witness = (ROOT / SHARED.WITNESS).read_text()
        self.variants = SHARED.mutations(self.core, self.witness, CALLER.replace_once)

    def test_controls_are_exact_and_nontrivial(self):
        self.assertEqual(set(self.variants), set(SHARED.CONTROLS))
        self.assertEqual(set(self.variants), set(SHARED.OBLIGATIONS))
        for core, witness, _, _ in self.variants.values():
            self.assertNotEqual((core, witness), (self.core, self.witness))

    def test_time_slot_is_the_only_removed_resource(self):
        core, witness, _, _ = self.variants['time_slot_removed_only']
        self.assertEqual(witness, self.witness)
        self.assertEqual(core.replace('(Aabsdata absecblsid (absecblist events) ** Aemp)',
            '(Aabsdata absecblsid (absecblist events) ** Aabsdata ostmid (ostm now))'), self.core)

    def test_update_control_only_changes_store_postcondition(self):
        core, witness, _, _ = self.variants['abstract_current_update_omitted_only']
        self.assertEqual(witness, self.witness)
        a = core.index('Lemma V293_shared_store :'); b = core.index('Proof.', a)
        self.assertEqual(core[:a], self.core[:a])
        self.assertEqual(core[b:], self.core[self.core.index('Proof.', a):])
        self.assertEqual(core[a:b].replace('aux, O, op) |= SWINVt V293_shared_inv t.',
            'aux, set O curtid (oscurt t), op) |= SWINVt V293_shared_inv t.'),
            self.core[a:self.core.index('Proof.', a)])

    def test_readonly_control_only_changes_fixture_bytes_permission(self):
        core, witness, _, _ = self.variants['fixture_current_read_only']
        self.assertEqual(core, self.core)
        self.assertEqual(witness.replace(
            'Definition V293_shared_fixture_mem t := V293_encoded_memory 1%positive 0 false',
            'Definition V293_shared_fixture_mem t := V293_encoded_memory 1%positive 0 true'), self.witness)

    def test_false_control_only_adds_unused_argument(self):
        core, witness, _, _ = self.variants['goodi_false_premise_added_only']
        self.assertEqual(witness, self.witness)
        self.assertEqual(core.replace('Theorem V293_shared_good : False -> GoodI',
                                     'Theorem V293_shared_good : GoodI')
                         .replace('intro Hfalse. split.', 'split.'), self.core)

    def test_independent_probe_has_no_extra_premise_and_all_four_slots(self):
        self.assertNotIn('False ->', SHARED.PROBE)
        self.assertNotIn('V293_shared_fields current', SHARED.PROBE)
        for slot in ['curtid', 'abstcblsid', 'absecblsid', 'ostmid']:
            self.assertIn('Aabsdata ' + slot, SHARED.PROBE)
        self.assertIn('V293_shared_core = checked_shared_core', SHARED.PROBE)
        self.assertIn('getinv (V293_shared_inv k)', SHARED.PROBE)

    def test_both_live_and_deleted_cases_have_target_and_store(self):
        self.assertIn('Definition checked_shared_cases : forall live,', SHARED.PROBE)
        self.assertIn('wait os_stat_time Int.one', SHARED.PROBE)
        self.assertIn('else None', SHARED.PROBE)
        self.assertIn('AHprio V293_scheduler (15%positive, Int.zero)', SHARED.PROBE)
        self.assertIn('store (Tptr Tvoid) M', SHARED.PROBE)
        self.assertNotIn('V293_shared_case_tasks live', SHARED.PROBE)

    def test_no_physical_kernel_or_function_coverage_claim(self):
        self.assertIn('NOT_PHYSICAL_KERNEL_INVARIANT_OR_SWITCH_OR_GOOD_OS', SHARED.SCOPE)
        self.assertEqual(len(SHARED.ROOTS), 6)

    def test_both_modules_are_active_and_current_write_is_reused(self):
        project = (ROOT / '_CoqProject').read_text()
        for path in SHARED.FILES:
            self.assertIn(path, project.splitlines())
        self.assertIn('apply V293_current_halves_write', self.core)
        self.assertNotIn('Lemma V293_shared_current_write', self.core)

    def rejection_row(self):
        label = 'abstract_current_update_omitted_only'
        core, _, rel, declaration = self.variants[label]
        line = core[:core.index(declaration)].count('\n') + 2
        row = dict(exit_code=1, stdout='',
                   stderr=f'File "/tmp/isolation/{rel}", line {line}, characters 0-1:\nError: mismatch\n')
        return label, core, rel, declaration, row

    def test_designated_semantic_rejection_is_accepted(self):
        label, core, rel, declaration, row = self.rejection_row()
        SHARED.check_rejection(row, core, rel, declaration, label)

    def test_unrelated_rejection_file_is_not_accepted(self):
        label, core, rel, declaration, row = self.rejection_row()
        row['stderr'] = row['stderr'].replace(rel, 'Other.v')
        with self.assertRaisesRegex(ValueError, 'missed designated obligation'):
            SHARED.check_rejection(row, core, rel, declaration, label)

    def test_earlier_line_failure_is_not_accepted(self):
        label, core, rel, declaration, row = self.rejection_row()
        row['stderr'] = row['stderr'].replace('line ' + str(core[:core.index(declaration)].count('\n') + 2), 'line 1')
        with self.assertRaisesRegex(ValueError, 'missed designated obligation'):
            SHARED.check_rejection(row, core, rel, declaration, label)

    def test_signal_termination_is_not_designated_rejection(self):
        label, core, rel, declaration, row = self.rejection_row()
        row['exit_code'] = -9
        with self.assertRaisesRegex(ValueError, 'missed designated obligation'):
            SHARED.check_rejection(row, core, rel, declaration, label)


class SharedReportTests(unittest.TestCase):
    def setUp(self):
        self.gate = load(ROOT, 'check-v293-functions.py')
        self.report = json.loads((ROOT / self.gate.REPORT).read_text())

    def validate(self):
        SHARED.validate(ROOT, self.report['shared_state_checkpoint'], self.report['checks'], load)

    def test_record_accepts_the_actual_scope(self):
        self.validate()

    def test_no_coverage_upgrade(self):
        self.report['shared_state_checkpoint']['coverage_credit'] = True
        with self.assertRaisesRegex(ValueError, 'scope/roots/source/controls differ'):
            self.validate()

    def test_frozen_source_location_is_required(self):
        self.report['shared_state_checkpoint']['source_location']['first_line'] = 1
        with self.assertRaisesRegex(ValueError, 'scope/roots/source/controls differ'):
            self.validate()

    def test_kernel_scope_upgrade_is_rejected(self):
        self.report['shared_state_checkpoint']['scope'] = 'GOOD_OS_PROVED'
        with self.assertRaisesRegex(ValueError, 'scope/roots/source/controls differ'):
            self.validate()

    def test_no_unknown_assumption(self):
        self.report['shared_state_checkpoint']['root_assumptions'].append('Unknown.shared')
        with self.assertRaisesRegex(ValueError, 'unexpected shared root assumptions'):
            self.validate()

    def test_every_positive_and_probe_check_is_required(self):
        original = copy.deepcopy(self.report)
        for key in ['positive:V293SharedState', 'positive:V293SharedStateWitness', 'positive:contract', 'coqchk']:
            with self.subTest(key=key):
                self.report = copy.deepcopy(original)
                self.report['checks']['shared:' + key]['exit_code'] = 1
                with self.assertRaisesRegex(ValueError, 'positive check failed'):
                    self.validate()

    def test_every_control_requires_its_designated_rejection(self):
        original = copy.deepcopy(self.report)
        for label, (rel, _) in SHARED.OBLIGATIONS.items():
            with self.subTest(label=label):
                self.report = copy.deepcopy(original)
                key = 'contract' if rel is None else Path(rel).stem
                self.report['checks']['shared:' + label + ':' + key]['exit_code'] = 0
                with self.assertRaisesRegex(ValueError, 'designated control missing'):
                    self.validate()

    def test_false_premise_requires_witness_compilation_first(self):
        self.report['checks']['shared:goodi_false_premise_added_only:V293SharedStateWitness']['exit_code'] = 1
        with self.assertRaisesRegex(ValueError, 'prerequisite missing'):
            self.validate()

    def test_record_rejects_unrelated_error_even_with_exit_code_one(self):
        row = self.report['checks']['shared:abstract_current_update_omitted_only:V293SharedState']
        row['stderr'] = row['stderr'].replace('V293SharedState.v', 'Other.v')
        with self.assertRaisesRegex(ValueError, 'missed designated obligation'):
            self.validate()
