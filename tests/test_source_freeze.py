"""Replayed source identity plus single-factor negative location-credit checks."""
import copy
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


def load(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), ROOT / 'scripts' / name)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


FREEZE = load('freeze-v293-source.py')
COVERAGE = load('coverage-audit.py')
FUNCTIONS = load('check-v293-functions.py')


class FrozenFixture(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='ucos-freeze-test-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        freeze = json.loads((ROOT / FREEZE.FREEZE).read_text())
        regression = json.loads((ROOT / 'audit/c-regressions.json').read_text())
        lock = json.loads((ROOT / 'csrc/UPSTREAM.lock.json').read_text())
        paths = set(freeze['input_sha256']) | set(regression['input_sha256'])
        paths |= {str(FREEZE.FREEZE), str(FREEZE.INVENTORY), 'audit/coverage.json', 'scripts/coverage-audit.py'}
        function_report = json.loads((ROOT / FUNCTIONS.REPORT).read_text())
        paths |= set(function_report['input_sha256']) | {FUNCTIONS.REPORT}
        paths |= {str(Path('csrc/upstream/v2.93.01/checkout') / p)
                  for p in [*lock['files'], lock['config_template'], 'os_cfg.h']}
        for rel in paths:
            destination = self.root / rel
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / rel, destination)

    def edit(self, rel, mutate):
        path = self.root / rel
        data = json.loads(path.read_text())
        mutate(data)
        path.write_text(FREEZE.serialize(data))

    def cli(self, *args):
        return subprocess.run(['python3', str(self.root / 'scripts/freeze-v293-source.py'), *args],
                              cwd=self.root, capture_output=True, text=True, timeout=30)


class SourceReplayTests(FrozenFixture):
    def test_real_replay_reproduces_both_records_without_rewriting(self):
        paths = [FREEZE.FREEZE, FREEZE.INVENTORY, Path('audit/coverage.json'),
                 Path('csrc/upstream/v2.93.01/checkout/Source/os_mutex.c')]
        before = {str(p): (self.root / p).read_bytes() for p in paths}
        result = self.cli()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('"configured_c_definitions": 94', result.stdout)
        self.assertEqual(before, {str(p): (self.root / p).read_bytes() for p in paths})
        self.assertFalse((self.root / FREEZE.SOURCE).exists())

    def test_record_does_not_overwrite_existing_evidence(self):
        before = (self.root / FREEZE.FREEZE).read_bytes()
        result = self.cli('--record')
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn('already exist', result.stderr)
        self.assertEqual(before, (self.root / FREEZE.FREEZE).read_bytes())

    def test_inventory_drift_is_rejected_without_rewrite(self):
        self.edit(FREEZE.INVENTORY, lambda x: x['functions'][0].update(first_line=1))
        before = (self.root / FREEZE.INVENTORY).read_bytes()
        result = self.cli()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn('frozen source drift', result.stderr)
        self.assertEqual(before, (self.root / FREEZE.INVENTORY).read_bytes())

    def test_patch_identity_drift_is_rejected(self):
        p = self.root / 'csrc/repairs/0001-nested-mutex-restoration.patch'
        p.write_bytes(p.read_bytes() + b'\n')
        result = self.cli()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn('C regression input identity drift', result.stderr)

    def test_replay_must_match_the_source_actually_used_by_c_evidence(self):
        self.edit('audit/c-regressions.json', lambda x: x['variants']['both']['source_sha256'].update(
            {'Source/os_mutex.c': '0' * 64}))
        result = self.cli()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn('replayed source differs from C regression source identity', result.stderr)


class AuthorizedDeltaTests(unittest.TestCase):
    def setUp(self):
        self.before = json.loads((ROOT / 'audit/source-inventory.json').read_text())
        self.after = json.loads((ROOT / FREEZE.INVENTORY).read_text())

    def test_actual_delta_is_six_changed_functions_and_two_static_helpers(self):
        delta = FREEZE.check_delta(self.before, self.after)
        self.assertEqual(len(delta['changed_existing_bodies']), 6)
        self.assertEqual(delta['added_static_helpers'], sorted(FREEZE.HELPERS))

    def test_removing_a_definition_is_rejected(self):
        self.after['functions'] = [f for f in self.after['functions'] if f['name'] != 'OSVersion']
        with self.assertRaisesRegex(ValueError, 'definition set'):
            FREEZE.check_delta(self.before, self.after)

    def test_exporting_a_helper_is_rejected(self):
        f = next(f for f in self.after['functions'] if f['name'] == 'OSMutex_BasePrio')
        f['linkage'] = 'external'
        with self.assertRaisesRegex(ValueError, 'static and internal'):
            FREEZE.check_delta(self.before, self.after)

    def test_changing_an_unrelated_body_is_rejected(self):
        f = next(f for f in self.after['functions'] if f['name'] == 'OSVersion')
        f['source_lines_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'authorized functions'):
            FREEZE.check_delta(self.before, self.after)

    def test_erasing_a_boundary_is_rejected(self):
        self.after['boundaries'].pop()
        with self.assertRaisesRegex(ValueError, 'boundaries'):
            FREEZE.check_delta(self.before, self.after)

    def test_effective_configuration_change_is_rejected(self):
        self.after['effective_os_macros']['OS_LOWEST_PRIO'] = '63u'
        with self.assertRaisesRegex(ValueError, 'effective configuration'):
            FREEZE.check_delta(self.before, self.after)


class LocationCreditTests(FrozenFixture):
    def test_locations_and_only_checked_function_gates_receive_credit(self):
        self.assertEqual(COVERAGE.audit(self.root), dict(zip(FREEZE.STATES, [94, 1, 1, 1, 1, 0])))

    def reject(self, mutate, message):
        self.edit('audit/coverage.json', mutate)
        with self.assertRaisesRegex(ValueError, message):
            COVERAGE.audit(self.root)

    def test_missing_function_is_rejected(self):
        self.reject(lambda x: x['rows'].pop(), 'exactly match every frozen function')

    def test_duplicate_function_is_rejected(self):
        self.reject(lambda x: x['rows'].append(copy.deepcopy(x['rows'][0])), 'duplicate')

    def test_wrong_body_locator_is_rejected(self):
        self.reject(lambda x: x['rows'][0]['location'].update(preprocessed_body_sha256='0' * 64),
                    'exactly match every frozen function')

    def test_wrong_source_revision_is_rejected(self):
        self.reject(lambda x: x['rows'][0].update(source_identity_sha256='0' * 64),
                    'exactly match every frozen function')

    def test_wrong_release_is_rejected(self):
        self.reject(lambda x: x.update(target_release='V2.93.00'), 'locked release/commit')

    def test_gate_list_cannot_be_weakened(self):
        self.reject(lambda x: x['states'].pop(), 'six fixed gates')

    def test_string_true_is_not_a_boolean(self):
        self.reject(lambda x: x['rows'][0].update(located='true'), 'explicit booleans')

    def test_cannot_skip_modeling_and_specification(self):
        self.reject(lambda x: x['rows'][0].update(local_hoare=True), 'skip an earlier gate')

    def test_a_model_file_or_name_cannot_manufacture_modeling_credit(self):
        self.reject(lambda x: x['rows'][0].update(modeled=True), 'evidence checker not implemented')

    def test_changed_inventory_is_rejected_before_using_its_locations(self):
        self.edit(FREEZE.INVENTORY, lambda x: x['functions'][0].update(first_line=1))
        with self.assertRaisesRegex(ValueError, 'inventory hash/path differs'):
            COVERAGE.audit(self.root)

    def test_osversion_cannot_claim_full_target_linkage(self):
        self.reject(lambda x: next(r for r in x['rows'] if r['name'] == 'OSVersion').update(
            full_target_linked=True), 'evidence checker not implemented')

    def test_stale_source_model_evidence_is_rejected(self):
        path = self.root / 'certiucos/v293/code/V293OSVersion.v'
        path.write_text(path.read_text().replace('29300', '29301'))
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_stale_specification_evidence_is_rejected(self):
        path = self.root / 'certiucos/v293/spec/V293OSVersionSpec.v'
        path.write_text(path.read_text().replace('29300', '29301'))
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_evidence_cannot_claim_more_gates_than_the_checker(self):
        self.edit(FUNCTIONS.REPORT, lambda x: x['functions']['OSVersion']['gates'].append(
            'full_target_linked'))
        with self.assertRaisesRegex(ValueError, 'checked source/model/contracts'):
            COVERAGE.audit(self.root)

    def test_report_without_a_passing_coqchk_is_rejected(self):
        self.edit(FUNCTIONS.REPORT, lambda x: x['checks']['coqchk'].update(exit_code=1))
        with self.assertRaisesRegex(ValueError, 'unsuccessful positive gate'):
            COVERAGE.audit(self.root)


class ComponentCreditTests(FrozenFixture):
    def test_stale_api_component_evidence_is_rejected(self):
        path = self.root / FUNCTIONS.API
        path.write_text(path.read_text().replace('spec_done (Some V293_OSVersion_result)',
            'spec_done (Some (Vint32 (Int.repr 29301)))', 1))
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_another_function_cannot_borrow_component_credit(self):
        def mutate(data):
            row = next(r for r in data['rows'] if r['name'] != 'OSVersion')
            row.update(modeled=True, specified=True, local_hoare=True, component_linked=True)
        self.edit('audit/coverage.json', mutate)
        with self.assertRaisesRegex(ValueError, 'evidence checker not implemented'):
            COVERAGE.audit(self.root)

    def test_a_component_failure_cannot_receive_credit(self):
        self.edit(FUNCTIONS.REPORT,
            lambda data: data['checks']['positive:V293OSVersionAPI'].update(exit_code=1))
        with self.assertRaisesRegex(ValueError, 'unsuccessful positive gate'):
            COVERAGE.audit(self.root)

    def test_missing_component_control_is_rejected(self):
        self.edit(FUNCTIONS.REPORT,
            lambda data: data['checks']['missing_api_entry:V293OSVersionAPI'].update(exit_code=0))
        with self.assertRaisesRegex(ValueError, 'designated negative controls'):
            COVERAGE.audit(self.root)


class SchedulerCheckpointTests(FrozenFixture):
    def reject_report(self, mutate, message):
        self.edit(FUNCTIONS.REPORT, mutate)
        with self.assertRaisesRegex(ValueError, message):
            COVERAGE.audit(self.root)

    def test_scheduler_checkpoint_cannot_claim_function_coverage(self):
        self.reject_report(lambda x: x['scheduler_checkpoint'].update(coverage_credit=True),
                           'scheduler checkpoint scope/roots/controls differ')

    def test_changed_scheduler_model_invalidates_report(self):
        path = self.root / 'certiucos/v293/code/V293OSSchedNew.v'
        path.write_text(path.read_text().replace('Int.repr 3', 'Int.repr 2'))
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_changed_source_seam_invalidates_report(self):
        path = self.root / 'scripts/v293-scheduler-source.py'
        path.write_text(path.read_text() + '\n# mutation\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_scheduler_compilation_failure_rejects_report(self):
        self.reject_report(lambda x: x['checks']['scheduler:positive:V293OSSchedNewExec'].update(exit_code=1),
                           'scheduler checkpoint positive compilation failed')

    def test_scheduler_coqchk_failure_rejects_report(self):
        self.reject_report(lambda x: x['checks']['scheduler:coqchk'].update(exit_code=1),
                           'scheduler checkpoint probe/coqchk failed')

    def test_missing_table_rejection_rejects_report(self):
        self.reject_report(lambda x: x['checks']['scheduler:wrong_table:V293ReadyBitmap'].update(exit_code=0),
                           'scheduler designated table/shift rejection missing')

    def test_early_shift_rejection_is_not_downstream_evidence(self):
        self.reject_report(lambda x: x['checks']['scheduler:wrong_shift:V293ReadyBitmap'].update(exit_code=1),
                           'scheduler designated table/shift rejection missing')

    def test_permission_control_must_first_compile_actual_result(self):
        self.reject_report(lambda x: x['checks']['scheduler:writable_permission_removed_only:actual'].update(exit_code=1),
                           'scheduler designated concrete semantic control missing')

    def test_nonempty_control_must_reject_wrong_property(self):
        self.reject_report(lambda x: x['checks']['scheduler:nonempty_removed_only:rejected'].update(exit_code=0),
                           'scheduler designated concrete semantic control missing')

    def test_scheduler_cannot_borrow_modeling_credit_from_checkpoint(self):
        self.edit('audit/coverage.json', lambda x: next(r for r in x['rows']
                  if r['name'] == 'OS_SchedNew').update(modeled=True))
        with self.assertRaisesRegex(ValueError, 'evidence checker not implemented'):
            COVERAGE.audit(self.root)

    def test_body_hoare_positive_compilation_required(self):
        self.reject_report(lambda x: x['checks']['scheduler:positive:V293OSSchedNewHoare'].update(exit_code=1),
                           'scheduler checkpoint positive compilation failed')

    def test_spatial_witness_positive_compilation_required(self):
        self.reject_report(lambda x: x['checks']['scheduler:positive:V293OSSchedNewWitness'].update(exit_code=1),
                           'scheduler checkpoint positive compilation failed')

    def test_erased_read_resource_control_must_fail(self):
        self.reject_report(lambda x: x['checks']['scheduler:group_resource_removed_only:V293OSSchedNewHoare'].update(exit_code=0),
                           'scheduler designated body control missing')

    def test_readonly_local_control_must_first_reach_hoare(self):
        self.reject_report(lambda x: x['checks']['scheduler:local_write_permission_removed_only:V293OSSchedNewEval'].update(exit_code=1),
                           'scheduler body control prerequisite compilation missing')

    def test_old_output_post_control_must_fail(self):
        self.reject_report(lambda x: x['checks']['scheduler:output_post_restores_old_value_only:V293OSSchedNewHoare'].update(exit_code=0),
                           'scheduler designated body control missing')

    def test_false_premise_mutant_must_compile_first(self):
        self.reject_report(lambda x: x['checks']['scheduler:body_false_premise_added_only:V293OSSchedNewHoare'].update(exit_code=1),
                           'scheduler designated body control missing')

    def test_false_premise_mutant_must_be_rejected_by_exact_type(self):
        self.reject_report(lambda x: x['checks']['scheduler:body_false_premise_added_only_probe:contract'].update(exit_code=0),
                           'scheduler vacuous body mutant/probe evidence missing')

    def test_vacuous_mutant_witness_must_still_compile(self):
        self.reject_report(lambda x: x['checks']['scheduler:body_false_premise_added_only:V293OSSchedNewWitness'].update(exit_code=1),
                           'scheduler vacuous body mutant/probe evidence missing')

    def test_changed_body_proof_invalidates_report(self):
        path = self.root / 'certiucos/v293/proofs/V293OSSchedNewHoare.v'
        path.write_text(path.read_text() + '\n(* mutation *)\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_changed_spatial_witness_invalidates_report(self):
        path = self.root / 'certiucos/v293/proofs/V293OSSchedNewWitness.v'
        path.write_text(path.read_text() + '\n(* mutation *)\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)


class SchedulerInternalCheckpointTests(FrozenFixture):
    def reject_report(self, mutate, message):
        self.edit(FUNCTIONS.REPORT, mutate)
        with self.assertRaisesRegex(ValueError, message):
            COVERAGE.audit(self.root)

    def test_internal_checkpoint_cannot_claim_kernel_or_function_credit(self):
        self.reject_report(lambda x: x['scheduler_internal_checkpoint'].update(coverage_credit=True),
                           'internal checkpoint scope/roots/controls differ')

    def test_changed_internal_contract_invalidates_evidence(self):
        path = self.root / 'certiucos/v293/proofs/V293OSSchedNewInternal.v'
        path.write_text(path.read_text() + '\n(* changed contract input *)\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_changed_internal_checker_invalidates_evidence(self):
        path = self.root / 'scripts/v293-scheduler-internal.py'
        path.write_text(path.read_text() + '\n# changed checker\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_missing_wffun_root_is_rejected(self):
        self.reject_report(lambda x: x['scheduler_internal_checkpoint']['roots'].remove('V293_OSSchedNew_WFFunEnv'),
                           'internal checkpoint scope/roots/controls differ')

    def test_unknown_internal_assumption_is_rejected(self):
        self.reject_report(lambda x: x['scheduler_internal_checkpoint']['root_assumptions'].append('Unknown.assumption'),
                           'unexpected internal root assumptions')

    def test_failed_internal_positive_is_rejected(self):
        self.reject_report(lambda x: x['checks']['internal:positive:V293OSSchedNewInternal'].update(exit_code=1),
                           'internal positive compilation failed')

    def test_failed_internal_witness_is_rejected(self):
        self.reject_report(lambda x: x['checks']['internal:positive:V293OSSchedNewInternalWitness'].update(exit_code=1),
                           'internal positive compilation failed')

    def test_failed_internal_coqchk_is_rejected(self):
        self.reject_report(lambda x: x['checks']['internal:coqchk'].update(exit_code=1),
                           'internal positive/isolation check failed')

    def test_failed_isolation_baseline_is_rejected(self):
        self.reject_report(lambda x: x['checks']['internal:contract_isolation_baseline:contract'].update(exit_code=1),
                           'internal positive/isolation check failed')

    def test_vacuous_mutant_must_compile_before_interface_rejection(self):
        self.reject_report(lambda x: x['checks']['internal:contract_false_premise_added_only:V293OSSchedNewInternal'].update(exit_code=1),
                           'internal designated core control missing')

    def test_internal_false_contract_probe_must_reject(self):
        self.reject_report(lambda x: x['checks']['internal:contract_false_premise_added_only:contract'].update(exit_code=0),
                           'internal vacuous contract/selector probe control missing')

    def test_internal_semantic_control_must_reach_its_core(self):
        self.reject_report(lambda x: x['checks']['internal:local_domain_removed_only:V293OSSchedNewInternal'].update(exit_code=0),
                           'internal designated core control missing')

    def test_internal_control_cannot_claim_early_failure_as_downstream_evidence(self):
        self.reject_report(lambda x: x['checks']['internal:return_value_changed_only:V293OSSchedNewHoare'].update(exit_code=1),
                           'internal control prerequisite failed')

    def test_all_false_selector_probe_must_reject(self):
        self.reject_report(lambda x: x['checks']['internal:pre_assertion_false_only:contract'].update(exit_code=0),
                           'internal vacuous contract/selector probe control missing')

    def test_all_false_selector_mutant_must_compile(self):
        self.reject_report(lambda x: x['checks']['internal:pre_assertion_false_only:V293OSSchedNewInternal'].update(exit_code=1),
                           'internal designated core control missing')


class SchedulerCallerCheckpointTests(FrozenFixture):
    def reject_report(self, mutate, message):
        self.edit(FUNCTIONS.REPORT, mutate)
        with self.assertRaisesRegex(ValueError, message):
            COVERAGE.audit(self.root)

    def test_caller_cannot_claim_coverage(self):
        self.reject_report(lambda x: x['scheduler_caller_checkpoint'].update(coverage_credit=True),
                           'caller checkpoint scope/roots/source/controls differ')

    def test_whole_function_scope_cannot_replace_prefix_scope(self):
        self.reject_report(lambda x: x['scheduler_caller_checkpoint'].update(scope='OS_SCHED_PROVED'),
                           'caller checkpoint scope/roots/source/controls differ')

    def test_source_location_is_exactly_bound(self):
        self.reject_report(lambda x: x['scheduler_caller_checkpoint']['source_location'].update(first_line=1),
                           'caller checkpoint scope/roots/source/controls differ')

    def test_missing_task_selection_root(self):
        self.reject_report(lambda x: x['scheduler_caller_checkpoint']['roots'].remove('V293_ready_selection_task'),
                           'caller checkpoint scope/roots/source/controls differ')

    def test_unknown_caller_assumption(self):
        self.reject_report(lambda x: x['scheduler_caller_checkpoint']['root_assumptions'].append('Unknown.assumption'),
                           'unexpected caller root assumptions')

    def test_failed_target_witness(self):
        self.reject_report(lambda x: x['checks']['caller:positive:V293OSSchedTargetWitness'].update(exit_code=1),
                           'caller checkpoint positive check failed')

    def test_failed_caller_coqchk(self):
        self.reject_report(lambda x: x['checks']['caller:coqchk'].update(exit_code=1),
                           'caller checkpoint positive check failed')

    def test_missing_pointer_stride_control(self):
        self.reject_report(lambda x: x['checks']['caller:pointer_resource_stride_changed_only:V293OSSchedTarget'].update(exit_code=0),
                           'caller designated control missing')

    def test_earlier_rejection_cannot_count_as_stride_evidence(self):
        self.reject_report(lambda x: x['checks']['caller:pointer_resource_stride_changed_only:V293SchedulerTasks'].update(exit_code=1),
                           'caller control prerequisite missing')

    def test_vacuous_call_must_compile_first(self):
        self.reject_report(lambda x: x['checks']['caller:call_false_premise_added_only:V293OSSchedCall'].update(exit_code=1),
                           'caller control prerequisite missing')

    def test_vacuous_call_requires_independent_rejection(self):
        self.reject_report(lambda x: x['checks']['caller:call_false_premise_added_only:contract'].update(exit_code=0),
                           'caller designated control missing')

    def test_vacuous_target_must_compile_all_prerequisites(self):
        self.reject_report(lambda x: x['checks']['caller:target_false_premise_added_only:V293OSSchedTargetWitness'].update(exit_code=1),
                           'caller control prerequisite missing')

    def test_modified_caller_coq_source_is_stale(self):
        path = self.root / 'certiucos/v293/proofs/V293OSSchedTarget.v'
        path.write_text(path.read_text() + '\n(* mutation *)\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_modified_caller_checker_is_stale(self):
        path = self.root / 'scripts/v293-scheduler-caller.py'
        path.write_text(path.read_text() + '\n# mutation\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)
