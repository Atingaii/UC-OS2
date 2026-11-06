"""Concrete entry non-vacuity; Coq results are checked separately, not inferred."""
import ast
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT/'audit/logs/stage26-ready-owned-transition/replayed-entry'
SOURCE = ROOT/'certiucos/v293/proofs/V293CriticalReturn.v'


def gate():
    spec = importlib.util.spec_from_file_location('entry_gate', ROOT/'scripts/check-v293-success-entry-witness.py')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def section(name):
    s = SOURCE.read_text()
    i = s.index('Theorem '+name+' :')
    return s[i:s.index('\nQed.', i)+6]


def result():
    return json.loads((LOG/'gate02/result.json').read_text())


class SuccessEntryWitness(unittest.TestCase):
    def test_frozen_4107_line_prefix(self):
        old = (LOG/'V293CriticalReturn.before.v.snapshot.txt').read_bytes()
        self.assertEqual(len(old), gate().PREFIX_BYTES)
        self.assertEqual(old.count(b'\n'), 4107)
        self.assertEqual(hashlib.sha256(old).hexdigest(), gate().PREFIX_SHA)
        self.assertTrue(SOURCE.read_bytes().startswith(old))

    def test_nonvacuity_has_no_resource_or_execution_premises(self):
        for name in gate().ROOTS:
            statement = section(name).split('Proof.', 1)[0]
            self.assertIn('forall ir enabled si ci,\n  exists Mf,', statement)
            self.assertNotIn('->', statement.split('  exists Mf,', 1)[0])
            self.assertIn('((V293_complete_fixture_ge,emp,Mf),ir,(enabled,si,ci))', statement)
            self.assertIn('V293_local_steps V293_success_tail_fixture_program', statement)

    def test_each_branch_applies_the_full_root_with_one_original_memory(self):
        for branch, name in [('null', gate().NULL), ('event', gate().EVENT)]:
            text = section(name)
            self.assertEqual(text.count('V293_critical_'+branch+'_success_return_execution'), 1)
            self.assertIn('8%Z 30%positive 31%positive 16 1 255 6 V293_prefix_fixture_entries', text)
            self.assertIn('1001%Z 100%positive 1 999%Z', text)
            self.assertIn('AllWritable : forall c ty', text)
            self.assertIn('V293_complete_fixture_get_frame', text)

    def test_all_eleven_locals_have_seventeen_bytes(self):
        for name in gate().ROOTS:
            text = section(name)
            addresses = text[text.index('assert (Addresses :'):text.index('assert (CoordsW :')]
            self.assertEqual(addresses.count(',Tint8)'), 9)
            self.assertEqual(addresses.count(',Tptr '), 2)
            self.assertEqual(9+2*4, 17)
            for item in ['(40%positive,Tptr V293_tcb_type)', '(70%positive,Tptr V293_event_type)',
                         '(52%positive,Tint8)', '(73%positive,Tint8)']:
                self.assertIn(item, addresses)
            self.assertIn('rewrite Addresses. repeat constructor', text)

    def test_observations_and_initial_staleness_share_the_same_witness(self):
        for name in gate().ROOTS:
            statement = section(name).split('Proof.', 1)[0]
            for item in ['V293_tcb_updated_loads Mf 41%positive 8%Z 6',
                         'V293_rekey_bitmap_loads Mf 30%positive 31%positive 80 0 1',
                         'V293_table_loads V293_tcb_type Mf 50%positive',
                         'get Mf (c,Z.of_nat k) = None', 'Some (V293_byteval 255)',
                         'In c [100%positive;101%positive;102%positive]']:
                self.assertIn(item, statement)
        self.assertIn('V293_event_bitmap_loads Mf 72%positive 5%Z 64 0 1', section(gate().EVENT))

    def test_no_oracle_or_large_memory_evaluation_added(self):
        suffix = SOURCE.read_bytes()[gate().PREFIX_BYTES:].decode()
        bare = re.sub(r'\(\*.*?\*\)', '', suffix, flags=re.S)
        self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|vm_compute)\b', bare))
        self.assertIn('apply V293_load_block_frame', suffix)

    def test_fixed_probe_checks_literal_program_and_complete_observations(self):
        probe = (ROOT/gate().PROBE).read_text()
        for item in ['expected_entry_mem', 'expected_entry_program', 'expected_entry_trace',
                     'expected_entry_observations', 'expected_success_program', 'expected_tail',
                     'expected_null_simultaneous_entry', 'expected_event_simultaneous_entry']:
            self.assertIn(item, probe)
        driver = (ROOT/'scripts/check-v293-success-entry-witness.py').read_text()
        self.assertNotIn('(ROOT/PROBE).write_text', driver)
        self.assertNotIn('Admitted', probe)

    def test_prospective_negatives_keep_target_proof_suffix_identical(self):
        controls = gate().controls(SOURCE.read_text())
        self.assertEqual({x[0] for x in controls}, {'ReturnOne', 'LocalRetained', 'EventBitmapNeutralized'})
        for _, target, changed, original, _ in controls:
            i = changed.index('Proof.', changed.index('Theorem '+target+' :'))
            j = original.index('Proof.', original.index('Theorem '+target+' :'))
            self.assertEqual(changed[i:], original[j:])

    def test_control_baseline_hash_excludes_only_print_diagnostics(self):
        protocol = {row['label']: row for row in json.loads((LOG/'gate02/control-protocol.json').read_text())}
        for label, target, changed, original, _ in gate().controls(SOURCE.read_text()):
            name = 'PositiveNull' if target == gate().NULL else 'PositiveEvent'
            actual = (LOG/('gate02/'+name+'.v.snapshot.txt')).read_text()
            self.assertTrue(actual.startswith(original))
            self.assertTrue(actual[len(original):].strip().startswith('Print Assumptions '))
            self.assertEqual(hashlib.sha256(original.encode()).hexdigest(), protocol[label]['positive_sha256'])
            self.assertEqual(hashlib.sha256(changed.encode()).hexdigest(), protocol[label]['sha256'])

    def test_gate_actually_passed_thirteen_checks(self):
        report = result()
        self.assertTrue(report['passed'])
        self.assertTrue(report['temporary_tree_removed'])
        self.assertTrue(report['inputs_unchanged'])
        self.assertEqual(len(report['checks']), 13)
        for key, row in report['checks'].items():
            self.assertEqual(row['exit_code'], 1 if key.startswith('negative-') else 0)

    def test_current_gate_identity(self):
        report = result()
        self.assertEqual(len(report['inputs']), 175)
        for path, expected in report['inputs'].items():
            self.assertEqual(hashlib.sha256((ROOT/path).read_bytes()).hexdigest(), expected, path)

    def test_actual_assumptions_are_bounded(self):
        report = result()
        allowed = {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
        for names in [report['probe_assumptions'], *report['positive_assumptions'].values()]:
            self.assertLessEqual(set(names), allowed)

    def test_negatives_reject_inside_target_and_get_no_downstream_credit(self):
        rows = [v for k, v in result()['checks'].items() if k.startswith('negative-')]
        self.assertEqual(len(rows), 3)
        for row in rows:
            self.assertTrue(row['proof_suffix_unchanged'])
            self.assertGreater(row['error_line'], row['target_proof_line'])
            self.assertFalse(row['downstream_credit'])

    def test_historical_assertions_preserved_current_evidence_replayed(self):
        old = (LOG/'test_success_complete_return_local.before.py.snapshot.txt').read_text()
        current = (ROOT/'tests/test_success_complete_return_local.py').read_text()

        def assertions(text):
            return [ast.dump(n, include_attributes=False) for n in ast.walk(ast.parse(text))
                    if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                    and n.func.attr.startswith('assert')]

        self.assertEqual(assertions(old), assertions(current))
        self.assertEqual(len(assertions(current)), 31)
        replay = json.loads((LOG/'complete-return-replay/gate02/result.json').read_text())
        self.assertTrue(replay['passed'])
        self.assertEqual(len(replay['checks']), 17)
        self.assertEqual(replay['inputs'][gate().SOURCE], hashlib.sha256(SOURCE.read_bytes()).hexdigest())


if __name__ == '__main__':
    unittest.main()
