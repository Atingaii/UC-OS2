"""Protocol regressions; semantic credit comes from actual Coq/coqchk logs."""
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage26-current-ownership'


def driver():
    spec = importlib.util.spec_from_file_location('ownership_gate', ROOT/'scripts/check-v293-current-ownership.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def header(source, name):
    a = source.index('Theorem '+name+' :')
    return source[a:source.index('Proof.', a)]


class CurrentOwnershipTests(unittest.TestCase):
    def test_prefix_and_prior_material_unchanged(self):
        gate = driver()
        baseline = json.loads((LOG/'baseline.json').read_text())
        self.assertEqual(len(baseline['active']), 166)
        self.assertEqual(sha(ROOT/gate.BEFORE), gate.BEFORE_SHA)
        self.assertTrue((ROOT/gate.SOURCE).read_bytes().startswith((ROOT/gate.BEFORE).read_bytes()))
        protected = {**baseline['protected'], **baseline['historical'],
                     **{p:h for p,h in baseline['active'].items() if p != gate.SOURCE}}
        for path, identity in protected.items():
            self.assertEqual(sha(ROOT/path), identity, path)

    def test_owned_entry_and_all_old_outputs(self):
        gate = driver()
        old = 'V293_critical_event_current_execution'
        before = header((ROOT/gate.BEFORE).read_text(), old)
        current = header((ROOT/gate.SOURCE).read_text(), gate.TARGET)
        original_entry, original_post = before.split("  exists Mf Os' OO',", 1)
        owned_entry, owned_post = current.split("  exists Mf Os' OO',", 1)
        expected = original_entry.replace(old, gate.TARGET, 1).replace(
            'V293_shared_fields abstract_current tasks events now ** R ->',
            '(CurTid abstract_current ** V293_shared_fields abstract_current tasks events now) ** R ->')
        self.assertTrue(owned_entry.startswith(expected))
        self.assertIn('~ In pointer_block (map fst (getaddr le))', owned_entry[len(expected):])
        self.assertTrue(owned_post.startswith(original_post.rstrip()[:-1]+' /\\'))
        probe = (ROOT/gate.PROBE).read_text()
        self.assertEqual(current.replace(gate.TARGET, 'expected_current_owned_contract', 1),
                         header(probe, 'expected_current_owned_contract'))

    def test_one_execution_and_actual_owned_final_resources(self):
        gate = driver()
        source = (ROOT/gate.SOURCE).read_text()
        suffix = source[source.index('Theorem '+gate.TARGET+' :'):]
        proof = suffix[suffix.index('Proof.'):]
        self.assertEqual(proof.count('V293_critical_event_current_execution P'), 1)
        for fragment in ['FieldsOwned', 'EntryCurrent', 'PointerApart', 'Outside', 'FinalFields',
                         'V293_current_owned_frame', 'V293_current_fields_reconstruct',
                         "exists Mf. exists Os'. exists OO'."]:
            self.assertIn(fragment, proof)
        for forbidden in ['Admitted', 'Axiom ', 'Parameter ', 'Conjecture ']:
            self.assertNotIn(forbidden, source)

    def test_constructive_half_permission_and_same_return_rejection(self):
        probe = (ROOT/driver().PROBE).read_text()
        for fragment in ['OwnershipProbeInstalledHalf', 'V293_encoded_memory b offset false bytes',
                         'OwnershipProbeEntryCurrent', 'V293_encoded_memory_mapsto',
                         'OwnershipProbeEntryCore', 'expected_current_owned_contract V293_success_tail_fixture_program',
                         'exact FinalCore', 'OwnershipProbeExecution sc now op ir enabled si ci',
                         'V293_shared_core ** Atrue', 'OwnershipProbeEmptyCannotOwnCurrent',
                         'CurTid (41%positive,Int.repr 8) ** Atrue']:
            self.assertIn(fragment, probe)
        self.assertNotIn('destruct (CurrentProbeExecution ', probe)
        self.assertEqual(probe.count('Print Assumptions '), 7)

    def test_single_factor_fixed_proof_controls(self):
        gate = driver()
        positive, negative = gate.controls((ROOT/gate.SOURCE).read_text())
        self.assertEqual(set(negative), {'DroppedBlockFrame', 'ChangedCurrent'})
        for name, data in negative.items():
            marker = 'Lemma V293_owned_block_frame :' if name == 'DroppedBlockFrame' else 'Theorem '+gate.TARGET+' :'
            start = lambda text: text.index('Proof.', text.index(marker))
            self.assertEqual(positive[start(positive):], data[start(data):])
        self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.', positive)
        self.assertIn('Require Import CurrentOwnershipGate.FrozenPrefix.', positive)

    def test_nineteen_actual_checks_and_frozen_inputs(self):
        report = json.loads((LOG/'gate01/result.json').read_text())
        self.assertTrue(report['passed'])
        self.assertTrue(report['inputs_unchanged'])
        self.assertTrue(report['temporary_tree_removed'])
        self.assertEqual(len(report['checks']), 19)
        for path, identity in report['inputs'].items():
            self.assertEqual(sha(ROOT/path), identity, path)
        for name, result in report['checks'].items():
            self.assertEqual(result['exit_code'], 1 if name.startswith('negative-') else 0, name)
            if name.startswith('negative-'):
                self.assertGreater(result['error_line'], result['target_proof_line'])
                self.assertTrue(result['proof_suffix_unchanged'])
                self.assertFalse(result['downstream_credit'])
        for name in ['Production-coqchk', 'Probe-coqchk', 'PositiveRoots-coqchk']:
            self.assertIn(name, report['checks'])

    def test_actual_assumptions_snapshots_and_configured_identity(self):
        gate = driver()
        report = json.loads((LOG/'gate01/result.json').read_text())
        checker = gate.module('check-v293-task-prio-rekey.py')
        for name, count, key in [('PositiveRoots', 5, 'positive_assumptions'),
                                 ('V293CurrentOwnershipProbe', 7, 'probe_assumptions')]:
            self.assertEqual(checker.checked_assumptions((LOG/f'gate01/{name}.log').read_text(), count), report[key])
        self.assertEqual((LOG/'gate01/Production.v.snapshot.txt').read_bytes(), (ROOT/gate.SOURCE).read_bytes())
        self.assertEqual((LOG/'gate01/Probe.v.snapshot.txt').read_bytes(), (ROOT/gate.PROBE).read_bytes())
        identity = json.loads((LOG/'configured-source/result.json').read_text())
        self.assertEqual(identity['function']['preprocessed_definition_sha256'],
                         'c29b633e71cf54c2d244eb87c7a5910a1f2973e6cd23d7a23769070b24bc2dbf')
