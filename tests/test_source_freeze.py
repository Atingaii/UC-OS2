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
    def test_all_and_only_locations_receive_credit(self):
        self.assertEqual(COVERAGE.audit(self.root), {s: 94 if s == 'located' else 0 for s in FREEZE.STATES})

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
