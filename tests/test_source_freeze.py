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


class SchedulerPrefixCheckpointTests(FrozenFixture):
    def reject_report(self, mutate, message):
        self.edit(FUNCTIONS.REPORT, mutate)
        with self.assertRaisesRegex(ValueError, message):
            COVERAGE.audit(self.root)

    def test_prefix_cannot_claim_function_coverage(self):
        self.reject_report(lambda x: x['scheduler_prefix_checkpoint'].update(coverage_credit=True),
                           'prefix checkpoint scope/roots/source/controls differ')

    def test_prefix_cannot_claim_whole_function(self):
        self.reject_report(lambda x: x['scheduler_prefix_checkpoint'].update(scope='OS_SCHED_PROVED'),
                           'prefix checkpoint scope/roots/source/controls differ')

    def test_prefix_wrong_source_location(self):
        self.reject_report(lambda x: x['scheduler_prefix_checkpoint']['source_location'].update(first_line=1),
                           'prefix checkpoint scope/roots/source/controls differ')

    def test_prefix_missing_root(self):
        self.reject_report(lambda x: x['scheduler_prefix_checkpoint']['roots'].remove('V293_OSSched_target_assign'),
                           'prefix checkpoint scope/roots/source/controls differ')

    def test_prefix_unknown_assumption(self):
        self.reject_report(lambda x: x['scheduler_prefix_checkpoint']['root_assumptions'].append('Unknown.assumption'),
                           'unexpected prefix root assumptions')

    def test_prefix_failed_whole_precondition_witness(self):
        self.reject_report(lambda x: x['checks']['prefix:positive:V293OSSchedPrefixWitness'].update(exit_code=1),
                           'prefix checkpoint positive check failed')

    def test_prefix_failed_coqchk(self):
        self.reject_report(lambda x: x['checks']['prefix:coqchk'].update(exit_code=1),
                           'prefix checkpoint positive check failed')

    def test_prefix_missing_permission_rejection(self):
        self.reject_report(lambda x: x['checks']['prefix:output_write_permission_removed_only:V293OSSchedPrefix'].update(exit_code=0),
                           'prefix designated control missing')

    def test_prefix_missing_order_rejection(self):
        self.reject_report(lambda x: x['checks']['prefix:statement_order_reversed_only:V293OSSchedPrefix'].update(exit_code=0),
                           'prefix designated control missing')

    def test_prefix_vacuity_cannot_fail_before_probe(self):
        self.reject_report(lambda x: x['checks']['prefix:prefix_false_premise_added_only:V293OSSchedPrefixWitness'].update(exit_code=1),
                           'prefix control prerequisite missing')

    def test_prefix_vacuity_probe_must_reject(self):
        self.reject_report(lambda x: x['checks']['prefix:prefix_false_premise_added_only:contract'].update(exit_code=0),
                           'prefix designated control missing')

    def test_prefix_changed_coq_is_stale(self):
        path = self.root / 'certiucos/v293/proofs/V293OSSchedPrefix.v'
        path.write_text(path.read_text() + '\n(* changed *)\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_prefix_changed_checker_is_stale(self):
        path = self.root / 'scripts/v293-scheduler-prefix.py'
        path.write_text(path.read_text() + '\n# changed\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_guards_cannot_claim_function_coverage(self):
        self.reject_report(lambda x: x['scheduler_guards_checkpoint'].update(coverage_credit=True),
                           'guards checkpoint scope/roots/source/controls differ')

    def test_guards_cannot_hide_open_suffix(self):
        self.reject_report(lambda x: x['scheduler_guards_checkpoint'].update(scope='OS_SCHED_PROVED'),
                           'guards checkpoint scope/roots/source/controls differ')

    def test_guards_source_location_is_fixed(self):
        self.reject_report(lambda x: x['scheduler_guards_checkpoint']['source_location'].update(first_line=1),
                           'guards checkpoint scope/roots/source/controls differ')

    def test_guards_missing_root(self):
        self.reject_report(lambda x: x['scheduler_guards_checkpoint']['roots'].pop(),
                           'guards checkpoint scope/roots/source/controls differ')

    def test_guards_unknown_assumption(self):
        self.reject_report(lambda x: x['scheduler_guards_checkpoint']['root_assumptions'].append('Unknown.guard'),
                           'unexpected guards root assumptions')

    def test_guards_failed_whole_witness(self):
        self.reject_report(lambda x: x['checks']['guards:positive:V293OSSchedGuardsWitness'].update(exit_code=1),
                           'guards checkpoint positive check failed')

    def test_guards_failed_coqchk(self):
        self.reject_report(lambda x: x['checks']['guards:coqchk'].update(exit_code=1),
                           'guards checkpoint positive check failed')

    def test_guards_missing_inner_guard_rejection(self):
        self.reject_report(lambda x: x['checks']['guards:lock_guard_replaced_with_interrupt_only:V293OSSchedGuards'].update(exit_code=0),
                           'guards designated control missing')

    def test_guards_false_premise_requires_witness_success(self):
        self.reject_report(lambda x: x['checks']['guards:continuation_false_premise_added_only:V293OSSchedGuardsWitness'].update(exit_code=1),
                           'guards control prerequisite missing')

    def test_guards_false_premise_probe_must_reject(self):
        self.reject_report(lambda x: x['checks']['guards:continuation_false_premise_added_only:contract'].update(exit_code=0),
                           'guards designated control missing')

    def test_guards_changed_checker_is_stale(self):
        path = self.root / 'scripts/v293-scheduler-guards.py'
        path.write_text(path.read_text() + '\n# changed\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_guards_semantic_rejection_requires_code_success(self):
        self.reject_report(lambda x: x['checks']['guards:lock_guard_replaced_with_interrupt_only:code:V293OSSchedGuards'].update(exit_code=1),
                           'guards control code prerequisite missing')

    def test_changes_cannot_claim_function_coverage(self):
        self.reject_report(lambda x: x['scheduler_change_checkpoint'].update(coverage_credit=True),
                           'changes checkpoint scope/roots/source/controls differ')

    def test_changes_cannot_hide_open_suffix(self):
        self.reject_report(lambda x: x['scheduler_change_checkpoint'].update(scope='OS_SCHED_PROVED'),
                           'changes checkpoint scope/roots/source/controls differ')

    def test_changes_source_location_is_fixed(self):
        self.reject_report(lambda x: x['scheduler_change_checkpoint']['source_location'].update(first_line=1),
                           'changes checkpoint scope/roots/source/controls differ')

    def test_changes_missing_root(self):
        self.reject_report(lambda x: x['scheduler_change_checkpoint']['roots'].pop(),
                           'changes checkpoint scope/roots/source/controls differ')

    def test_changes_unknown_assumption(self):
        self.reject_report(lambda x: x['scheduler_change_checkpoint']['root_assumptions'].append('Unknown.change'),
                           'unexpected changes root assumptions')

    def test_changes_failed_whole_witness(self):
        self.reject_report(lambda x: x['checks']['changes:positive:V293OSSchedChangeWitness'].update(exit_code=1),
                           'changes checkpoint positive check failed')

    def test_changes_failed_coqchk(self):
        self.reject_report(lambda x: x['checks']['changes:coqchk'].update(exit_code=1),
                           'changes checkpoint positive check failed')

    def test_changes_missing_equal_path_rejection(self):
        self.reject_report(lambda x: x['checks']['changes:equal_priority_post_inverted_only:V293OSSchedChange'].update(exit_code=0),
                           'changes designated control missing')

    def test_changes_false_premise_requires_witness_success(self):
        self.reject_report(lambda x: x['checks']['changes:guarded_change_false_premise_added_only:V293OSSchedChangeWitness'].update(exit_code=1),
                           'changes control prerequisite missing')

    def test_changes_false_premise_probe_must_reject(self):
        self.reject_report(lambda x: x['checks']['changes:guarded_change_false_premise_added_only:contract'].update(exit_code=0),
                           'changes designated control missing')

    def test_changes_changed_checker_is_stale(self):
        path = self.root / 'scripts/v293-scheduler-change.py'
        path.write_text(path.read_text() + '\n# changed\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_changes_semantic_rejection_requires_code_success(self):
        self.reject_report(lambda x: x['checks']['changes:equal_priority_post_inverted_only:code:V293OSSchedChange'].update(exit_code=1),
                           'changes control code prerequisite missing')

    def test_changes_normalization_boundary_is_fixed(self):
        self.reject_report(lambda x: x['scheduler_change_checkpoint']['normalization'].update(boundary='VERIFIED'),
                           'changes checkpoint scope/roots/source/controls differ')

    def test_changes_no_wrap_control_requires_all_modules_success(self):
        self.reject_report(lambda x: x['checks']['changes:counter_no_wrap_premise_added_only:V293OSSchedChangeWitness'].update(exit_code=1),
                           'changes control prerequisite missing')

    def test_changes_no_wrap_probe_must_reject(self):
        self.reject_report(lambda x: x['checks']['changes:counter_no_wrap_premise_added_only:contract'].update(exit_code=0),
                           'changes designated control missing')


class SchedulerCurrentCheckpointTests(FrozenFixture):
    def reject_report(self, mutate, message):
        self.edit(FUNCTIONS.REPORT, mutate)
        with self.assertRaisesRegex(ValueError, message):
            COVERAGE.audit(self.root)

    def test_current_cannot_claim_coverage(self):
        self.reject_report(lambda x: x['scheduler_current_checkpoint'].update(coverage_credit=True),
                           'current checkpoint scope/roots/source/controls differ')

    def test_current_scope_cannot_claim_switch(self):
        self.reject_report(lambda x: x['scheduler_current_checkpoint'].update(scope='SWITCH_PROVED'),
                           'current checkpoint scope/roots/source/controls differ')

    def test_current_source_location_is_exact(self):
        self.reject_report(lambda x: x['scheduler_current_checkpoint']['source_location'].update(first_line=1),
                           'current checkpoint scope/roots/source/controls differ')

    def test_current_root_cannot_be_removed(self):
        self.reject_report(lambda x: x['scheduler_current_checkpoint']['roots'].remove('V293_OSSched_guarded_current_prefix'),
                           'current checkpoint scope/roots/source/controls differ')

    def test_current_unknown_assumption(self):
        self.reject_report(lambda x: x['scheduler_current_checkpoint']['root_assumptions'].append('Unknown.current'),
                           'unexpected current root assumptions')

    def test_current_witness_must_succeed(self):
        self.reject_report(lambda x: x['checks']['current:positive:V293OSSchedCurrentWitness'].update(exit_code=1),
                           'current checkpoint positive check failed')

    def test_current_coqchk_must_succeed(self):
        self.reject_report(lambda x: x['checks']['current:coqchk'].update(exit_code=1),
                           'current checkpoint positive check failed')

    def test_current_permission_control_must_reject(self):
        self.reject_report(lambda x: x['checks']['current:target_output_read_permission_only:V293OSSchedCurrent'].update(exit_code=0),
                           'current designated control missing')

    def test_blocked_witness_requires_core_success(self):
        self.reject_report(lambda x: x['checks']['current:blocked_current_forced_ready_only:V293OSSchedCurrent'].update(exit_code=1),
                           'current control prerequisite missing')

    def test_current_false_premise_requires_witness_success(self):
        self.reject_report(lambda x: x['checks']['current:current_prefix_false_premise_added_only:V293OSSchedCurrentWitness'].update(exit_code=1),
                           'current control prerequisite missing')

    def test_current_false_premise_requires_probe_rejection(self):
        self.reject_report(lambda x: x['checks']['current:current_prefix_false_premise_added_only:contract'].update(exit_code=0),
                           'current designated control missing')

    def test_current_changed_checker_is_stale(self):
        path = self.root / 'scripts/v293-scheduler-current.py'
        path.write_text(path.read_text() + '\n# mutation\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_current_changed_proof_is_stale(self):
        path = self.root / 'certiucos/v293/proofs/V293OSSchedCurrent.v'
        path.write_text(path.read_text() + '\n(* mutation *)\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)


class SchedulerCriticalCheckpointTests(FrozenFixture):
    def reject_report(self, mutate, message):
        self.edit(FUNCTIONS.REPORT, mutate)
        with self.assertRaisesRegex(ValueError, message):
            COVERAGE.audit(self.root)

    def test_critical_cannot_claim_coverage(self):
        self.reject_report(lambda x: x['scheduler_critical_checkpoint'].update(coverage_credit=True),
                           'critical checkpoint scope/roots/source/controls differ')

    def test_critical_scope_cannot_claim_switch(self):
        self.reject_report(lambda x: x['scheduler_critical_checkpoint'].update(scope='SWITCH_PROVED'),
                           'critical checkpoint scope/roots/source/controls differ')

    def test_critical_source_location_is_exact(self):
        self.reject_report(lambda x: x['scheduler_critical_checkpoint']['source_location'].update(first_line=1),
                           'critical checkpoint scope/roots/source/controls differ')

    def test_critical_root_cannot_be_removed(self):
        self.reject_report(lambda x: x['scheduler_critical_checkpoint']['roots'].pop(),
                           'critical checkpoint scope/roots/source/controls differ')

    def test_critical_unknown_assumption(self):
        self.reject_report(lambda x: x['scheduler_critical_checkpoint']['root_assumptions'].append('Unknown.critical'),
                           'unexpected critical root assumptions')

    def test_critical_witness_must_succeed(self):
        self.reject_report(lambda x: x['checks']['critical:positive:V293OSSchedCriticalWitness'].update(exit_code=1),
                           'critical checkpoint positive check failed')

    def test_critical_probe_must_succeed(self):
        self.reject_report(lambda x: x['checks']['critical:positive:contract'].update(exit_code=1),
                           'critical checkpoint positive check failed')

    def test_critical_coqchk_must_succeed(self):
        self.reject_report(lambda x: x['checks']['critical:coqchk'].update(exit_code=1),
                           'critical checkpoint positive check failed')

    def test_dropped_payload_must_reject(self):
        self.reject_report(lambda x: x['checks']['critical:payload_return_dropped_only:V293OSSchedCritical'].update(exit_code=0),
                           'critical designated control missing')

    def test_reset_snapshot_must_reject(self):
        self.reject_report(lambda x: x['checks']['critical:critical_call_snapshot_reset_only:V293OSSchedCritical'].update(exit_code=0),
                           'critical designated control missing')

    def test_ignored_stack_requires_core_success(self):
        self.reject_report(lambda x: x['checks']['critical:critical_stack_ignored_only:V293OSSchedCritical'].update(exit_code=1),
                           'critical control prerequisite missing')

    def test_ignored_stack_requires_witness_success(self):
        self.reject_report(lambda x: x['checks']['critical:critical_stack_ignored_only:V293OSSchedCriticalWitness'].update(exit_code=1),
                           'critical control prerequisite missing')

    def test_ignored_stack_selector_must_reject(self):
        self.reject_report(lambda x: x['checks']['critical:critical_stack_ignored_only:contract'].update(exit_code=0),
                           'critical designated control missing')

    def test_critical_false_premise_requires_witness_success(self):
        self.reject_report(lambda x: x['checks']['critical:critical_prefix_false_premise_added_only:V293OSSchedCriticalWitness'].update(exit_code=1),
                           'critical control prerequisite missing')

    def test_critical_false_premise_requires_probe_rejection(self):
        self.reject_report(lambda x: x['checks']['critical:critical_prefix_false_premise_added_only:contract'].update(exit_code=0),
                           'critical designated control missing')

    def test_illegal_frame_requires_core_success(self):
        self.reject_report(lambda x: x['checks']['critical:critical_prefix_illegal_frame_premise_added_only:V293OSSchedCritical'].update(exit_code=1),
                           'critical control prerequisite missing')

    def test_illegal_frame_requires_witness_success(self):
        self.reject_report(lambda x: x['checks']['critical:critical_prefix_illegal_frame_premise_added_only:V293OSSchedCriticalWitness'].update(exit_code=1),
                           'critical control prerequisite missing')

    def test_illegal_frame_probe_must_reject(self):
        self.reject_report(lambda x: x['checks']['critical:critical_prefix_illegal_frame_premise_added_only:contract'].update(exit_code=0),
                           'critical designated control missing')

    def test_critical_changed_checker_is_stale(self):
        path = self.root / 'scripts/v293-scheduler-critical.py'
        path.write_text(path.read_text() + '\n# mutation\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_critical_changed_proof_is_stale(self):
        path = self.root / 'certiucos/v293/proofs/V293OSSchedCritical.v'
        path.write_text(path.read_text() + '\n(* mutation *)\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)


class SchedulerSwitchPreCheckpointTests(FrozenFixture):
    def reject_report(self, mutate, message):
        self.edit(FUNCTIONS.REPORT, mutate)
        with self.assertRaisesRegex(ValueError, message):
            COVERAGE.audit(self.root)

    def test_switch_pre_cannot_claim_coverage(self):
        self.reject_report(lambda x: x['scheduler_switch_pre_checkpoint'].update(coverage_credit=True),
                           'switch_pre checkpoint scope/roots/source/controls differ')

    def test_switch_pre_scope_cannot_claim_switch(self):
        self.reject_report(lambda x: x['scheduler_switch_pre_checkpoint'].update(scope='SWITCH_PROVED'),
                           'switch_pre checkpoint scope/roots/source/controls differ')

    def test_switch_pre_source_location_is_exact(self):
        self.reject_report(lambda x: x['scheduler_switch_pre_checkpoint']['source_location'].update(first_line=1),
                           'switch_pre checkpoint scope/roots/source/controls differ')

    def test_switch_pre_root_cannot_be_removed(self):
        self.reject_report(lambda x: x['scheduler_switch_pre_checkpoint']['roots'].pop(),
                           'switch_pre checkpoint scope/roots/source/controls differ')

    def test_switch_pre_unknown_assumption(self):
        self.reject_report(lambda x: x['scheduler_switch_pre_checkpoint']['root_assumptions'].append('Unknown.switch_pre'),
                           'unexpected switch_pre root assumptions')

    def test_switch_pre_core_must_succeed(self):
        self.reject_report(lambda x: x['checks']['switch_pre:positive:V293OSSchedSwitchPre'].update(exit_code=1),
                           'switch_pre checkpoint positive check failed')

    def test_switch_pre_witness_must_succeed(self):
        self.reject_report(lambda x: x['checks']['switch_pre:positive:V293OSSchedSwitchPreWitness'].update(exit_code=1),
                           'switch_pre checkpoint positive check failed')

    def test_switch_pre_probe_must_succeed(self):
        self.reject_report(lambda x: x['checks']['switch_pre:positive:contract'].update(exit_code=1),
                           'switch_pre checkpoint positive check failed')

    def test_switch_pre_coqchk_must_succeed(self):
        self.reject_report(lambda x: x['checks']['switch_pre:coqchk'].update(exit_code=1),
                           'switch_pre checkpoint positive check failed')

    def test_second_half_removal_must_reject(self):
        self.reject_report(lambda x: x['checks']['switch_pre:current_second_half_removed_only:V293OSSchedSwitchPre'].update(exit_code=0),
                           'switch_pre designated control missing')

    def test_membership_removal_must_reject(self):
        self.reject_report(lambda x: x['checks']['switch_pre:current_membership_removed_only:V293OSSchedSwitchPre'].update(exit_code=0),
                           'switch_pre designated control missing')

    def test_readonly_fixture_requires_core_success(self):
        self.reject_report(lambda x: x['checks']['switch_pre:fixture_current_read_only:V293OSSchedSwitchPre'].update(exit_code=1),
                           'switch_pre control prerequisite missing')

    def test_readonly_fixture_must_reject(self):
        self.reject_report(lambda x: x['checks']['switch_pre:fixture_current_read_only:V293OSSchedSwitchPreWitness'].update(exit_code=0),
                           'switch_pre designated control missing')

    def test_switch_pre_false_premise_requires_core_success(self):
        self.reject_report(lambda x: x['checks']['switch_pre:switch_pre_false_premise_added_only:V293OSSchedSwitchPre'].update(exit_code=1),
                           'switch_pre control prerequisite missing')

    def test_switch_pre_false_premise_requires_witness_success(self):
        self.reject_report(lambda x: x['checks']['switch_pre:switch_pre_false_premise_added_only:V293OSSchedSwitchPreWitness'].update(exit_code=1),
                           'switch_pre control prerequisite missing')

    def test_switch_pre_false_premise_requires_probe_rejection(self):
        self.reject_report(lambda x: x['checks']['switch_pre:switch_pre_false_premise_added_only:contract'].update(exit_code=0),
                           'switch_pre designated control missing')

    def test_switch_pre_changed_checker_is_stale(self):
        path = self.root / 'scripts/v293-scheduler-switch-pre.py'
        path.write_text(path.read_text() + '\n# mutation\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_switch_pre_changed_proof_is_stale(self):
        path = self.root / 'certiucos/v293/proofs/V293OSSchedSwitchPre.v'
        path.write_text(path.read_text() + '\n(* mutation *)\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)


class SharedCoreIdentityTests(FrozenFixture):
    def test_shared_checker_identity_drift_is_stale(self):
        path = self.root / 'scripts/v293-shared-state.py'
        path.write_text(path.read_text() + '\n# identity drift\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_shared_core_identity_drift_is_stale(self):
        path = self.root / 'certiucos/v293/proofs/V293SharedState.v'
        path.write_text(path.read_text() + '\n(* identity drift *)\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_shared_case_witness_identity_drift_is_stale(self):
        path = self.root / 'certiucos/v293/proofs/V293SharedStateWitness.v'
        path.write_text(path.read_text() + '\n(* identity drift *)\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)


class SharedPrefixCheckpointTests(FrozenFixture):
    def reject_report(self, mutate, message):
        self.edit(FUNCTIONS.REPORT, mutate)
        with self.assertRaisesRegex(ValueError, message):
            COVERAGE.audit(self.root)

    def test_shared_prefix_cannot_claim_coverage(self):
        self.reject_report(lambda x: x['scheduler_shared_checkpoint'].update(coverage_credit=True),
                           'shared-prefix checkpoint scope/roots/source/controls differ')

    def test_shared_prefix_scope_cannot_claim_switch(self):
        self.reject_report(lambda x: x['scheduler_shared_checkpoint'].update(scope='SWITCH_PROVED'),
                           'shared-prefix checkpoint scope/roots/source/controls differ')

    def test_shared_prefix_location_and_roots_are_exact(self):
        self.reject_report(lambda x: x['scheduler_shared_checkpoint']['source_location'].update(first_line=1),
                           'shared-prefix checkpoint scope/roots/source/controls differ')

    def test_shared_prefix_root_cannot_be_removed(self):
        self.reject_report(lambda x: x['scheduler_shared_checkpoint']['roots'].pop(),
                           'shared-prefix checkpoint scope/roots/source/controls differ')

    def test_shared_prefix_unknown_assumption_is_rejected(self):
        self.reject_report(lambda x: x['scheduler_shared_checkpoint']['root_assumptions'].append('Unknown.shared_prefix'),
                           'unexpected shared-prefix root assumptions')

    def test_shared_prefix_all_positive_rows_must_succeed(self):
        for key in ['positive:V293OSSchedShared', 'positive:V293OSSchedSharedWitness', 'positive:contract', 'coqchk']:
            with self.subTest(key=key):
                original = (self.root / FUNCTIONS.REPORT).read_text()
                self.reject_report(lambda x: x['checks']['shared_prefix:' + key].update(exit_code=1),
                                   'shared-prefix checkpoint positive check failed')
                (self.root / FUNCTIONS.REPORT).write_text(original)

    def test_shared_prefix_all_designated_failures_must_reject(self):
        endings = [('post_time_changed_only', 'V293OSSchedShared'),
                   ('callee_owns_shared_core_only', 'V293OSSchedShared'),
                   ('witness_time_slot_removed_only', 'V293OSSchedSharedWitness'),
                   ('prefix_false_premise_added_only', 'contract')]
        for label, suffix in endings:
            with self.subTest(label=label):
                original = (self.root / FUNCTIONS.REPORT).read_text()
                self.reject_report(lambda x: x['checks']['shared_prefix:' + label + ':' + suffix].update(exit_code=0),
                                   'shared designated control missing')
                (self.root / FUNCTIONS.REPORT).write_text(original)

    def test_shared_prefix_false_control_requires_both_modules_to_compile(self):
        for suffix in ['V293OSSchedShared', 'V293OSSchedSharedWitness']:
            with self.subTest(suffix=suffix):
                original = (self.root / FUNCTIONS.REPORT).read_text()
                self.reject_report(lambda x: x['checks']['shared_prefix:prefix_false_premise_added_only:' + suffix].update(exit_code=1),
                                   'shared-prefix control prerequisite missing')
                (self.root / FUNCTIONS.REPORT).write_text(original)

    def test_shared_prefix_wrong_rejection_file_is_rejected(self):
        self.reject_report(lambda x: x['checks']['shared_prefix:post_time_changed_only:V293OSSchedShared'].update(
            stderr=x['checks']['shared_prefix:post_time_changed_only:V293OSSchedShared']['stderr'].replace(
                'certiucos/v293/proofs/V293OSSchedShared.v', 'unrelated.v')),
            'shared-prefix control missed designated obligation')

    def test_shared_prefix_wrong_rejection_line_is_rejected(self):
        import re
        self.reject_report(lambda x: x['checks']['shared_prefix:post_time_changed_only:V293OSSchedShared'].update(
            stderr=re.sub(r'line \d+, characters', 'line 1, characters',
                x['checks']['shared_prefix:post_time_changed_only:V293OSSchedShared']['stderr'])),
            'shared-prefix control missed designated obligation')

    def test_shared_prefix_checker_identity_drift_is_stale(self):
        path = self.root / 'scripts/v293-scheduler-shared.py'
        path.write_text(path.read_text() + '\n# identity drift\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_shared_prefix_core_identity_drift_is_stale(self):
        path = self.root / 'certiucos/v293/proofs/V293OSSchedShared.v'
        path.write_text(path.read_text() + '\n(* identity drift *)\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)

    def test_shared_prefix_witness_identity_drift_is_stale(self):
        path = self.root / 'certiucos/v293/proofs/V293OSSchedSharedWitness.v'
        path.write_text(path.read_text() + '\n(* identity drift *)\n')
        with self.assertRaisesRegex(ValueError, 'stale function evidence'):
            COVERAGE.audit(self.root)


class NormalSwitchCheckpointTests(FrozenFixture):
    def setUp(self):
        super().setUp()
        self.switch = load('v293-scheduler-switch.py')

    def reject_report(self, mutate, message):
        self.edit(FUNCTIONS.REPORT, mutate)
        with self.assertRaisesRegex(ValueError, message):
            COVERAGE.audit(self.root)

    def test_switch_cannot_claim_function_coverage(self):
        self.reject_report(lambda x: x['scheduler_switch_checkpoint'].update(coverage_credit=True),
                           'normal-switch checkpoint scope/roots/source/controls differ')

    def test_switch_cannot_claim_full_source_caller(self):
        self.reject_report(lambda x: x['scheduler_switch_checkpoint'].update(scope='FULL_OS_SCHED'),
                           'normal-switch checkpoint scope/roots/source/controls differ')

    def test_switch_source_identity_and_roots_are_fixed(self):
        self.reject_report(lambda x: x['scheduler_switch_checkpoint']['source_location'].update(first_line=1),
                           'normal-switch checkpoint scope/roots/source/controls differ')

    def test_switch_root_cannot_disappear(self):
        self.reject_report(lambda x: x['scheduler_switch_checkpoint']['roots'].pop(),
                           'normal-switch checkpoint scope/roots/source/controls differ')

    def test_unknown_switch_assumption_rejected(self):
        self.reject_report(lambda x: x['scheduler_switch_checkpoint']['root_assumptions'].append('Unknown.switch'),
                           'unexpected normal-switch root assumptions')

    def test_all_switch_positive_commands_required(self):
        for key in ['positive:' + Path(p).stem for p in self.switch.FILES] + ['positive:contract', 'coqchk']:
            with self.subTest(key=key):
                original = (self.root / FUNCTIONS.REPORT).read_text()
                self.reject_report(lambda x: x['checks']['normal_switch:' + key].update(exit_code=1),
                                   'normal-switch checkpoint positive check failed')
                (self.root / FUNCTIONS.REPORT).write_text(original)

    def test_all_switch_designated_rejections_required(self):
        for label, (rel, _) in self.switch.OBLIGATIONS.items():
            suffix = 'contract' if rel is None else Path(rel).stem
            with self.subTest(label=label):
                original = (self.root / FUNCTIONS.REPORT).read_text()
                self.reject_report(lambda x: x['checks']['normal_switch:' + label + ':' + suffix].update(exit_code=0),
                                   'shared designated control missing')
                (self.root / FUNCTIONS.REPORT).write_text(original)

    def test_false_switch_control_requires_all_modules_success(self):
        for rel in self.switch.FILES:
            with self.subTest(rel=rel):
                original = (self.root / FUNCTIONS.REPORT).read_text()
                self.reject_report(lambda x: x['checks']['normal_switch:switch_false_premise_added_only:' + Path(rel).stem].update(exit_code=1),
                                   'normal-switch control prerequisite missing')
                (self.root / FUNCTIONS.REPORT).write_text(original)

    def test_switch_wrong_rejection_file_is_rejected(self):
        key = 'normal_switch:resumed_action_pending_only:V293OSSchedSwitch'
        self.reject_report(lambda x: x['checks'][key].update(stderr=x['checks'][key]['stderr'].replace(
            self.switch.CORE, 'unrelated.v')), 'normal-switch control missed designated obligation')

    def test_switch_wrong_rejection_line_is_rejected(self):
        import re
        key = 'normal_switch:resumed_action_pending_only:V293OSSchedSwitch'
        self.reject_report(lambda x: x['checks'][key].update(stderr=re.sub(
            r'line \d+, characters', 'line 1, characters', x['checks'][key]['stderr'])),
            'normal-switch control missed designated obligation')

    def test_switch_module_or_checker_drift_is_stale(self):
        for rel in [*self.switch.FILES, 'scripts/v293-scheduler-switch.py']:
            with self.subTest(rel=rel):
                path = self.root / rel; original = path.read_text()
                path.write_text(original + '\n')
                with self.assertRaisesRegex(ValueError, 'stale function evidence'):
                    COVERAGE.audit(self.root)
                path.write_text(original)
