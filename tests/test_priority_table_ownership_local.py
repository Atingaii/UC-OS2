"""Supplement actual Coq entry/two-store proofs, controls and kernel checks."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage26-priority-table'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def driver():
    spec = importlib.util.spec_from_file_location('priority_table_gate', ROOT / 'scripts/check-v293-priority-table-ownership.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def proof(source, declaration):
    return source[source.index(declaration):].split('Qed.', 1)[0]


class PriorityTableTests(unittest.TestCase):
    def test_preserved_2212_line_prefix_and_frozen_inputs(self):
        gate = driver()
        base = json.loads((LOG / 'baseline.json').read_text())
        prefix = (LOG / 'Before_Ownership.v.snapshot.txt').read_bytes()
        self.assertEqual(len(prefix.decode().splitlines()), 2212)
        self.assertEqual(hashlib.sha256(prefix).hexdigest(), base['sources'][gate.SOURCE])
        self.assertTrue((ROOT / gate.SOURCE).read_bytes().startswith(prefix))
        self.assertEqual(len(base['sources']), 167)
        self.assertEqual(len(base['protected']), 12)
        self.assertEqual(len(base['history']), 9291)
        frozen = {**base['history'], **base['protected'],
                  **{p: h for p, h in base['sources'].items() if p != gate.SOURCE}}
        for path, digest in frozen.items():
            self.assertEqual(sha(ROOT / path), digest, path)
        appended = (ROOT / gate.SOURCE).read_bytes()[len(prefix):].decode()
        self.assertIsNone(re.search(r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit)\b', appended))

    def test_prospective_single_factor_controls_and_actual_rejection(self):
        gate = driver()
        source = (ROOT / gate.SOURCE).read_text()
        controls = gate.controls(source)
        self.assertTrue(json.loads((LOG / 'protocol.json').read_text())['prospective'])
        self.assertTrue(json.loads((LOG / 'control-binding.json').read_text())['prospective_before_control_execution'])
        self.assertEqual(set(controls), {'ReadOnlyTableBytes', 'StaleFullTable'})
        report = json.loads((LOG / 'gate01/result.json').read_text())
        checks = {c['name']: c for c in report['checks']}
        for name, negative in controls.items():
            root = gate.CONTROL_ROOTS[name]
            a = source.index('Proof.', source.index(root))
            b = negative.index('Proof.', negative.index(root))
            self.assertEqual(source[a:], negative[b:])
            self.assertEqual(negative, (LOG / ('gate01/' + name + '.v.snapshot.txt')).read_text())
            self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.', negative)
            c = checks[name]
            self.assertEqual(c['exit_code'], 1)
            self.assertEqual(c['proof_line'], negative[:b].count('\n') + 1)
            self.assertGreater(c['error_line'], c['proof_line'])
            self.assertFalse(c['downstream_credit'])
            self.assertTrue(c['entire_proof_suffix_unchanged'])

    def test_actual_compilation_assumptions_and_independent_kernel_checks(self):
        gate = driver()
        report = json.loads((LOG / 'gate01/result.json').read_text())
        for flag in ['passed', 'inputs_unchanged', 'temporary_tree_removed']:
            self.assertTrue(report[flag])
        self.assertEqual(len(gate.FIXTURES), 18)
        self.assertEqual(len(report['checks']), 26)
        for item in report['checks']:
            self.assertEqual(item['exit_code'], item['expected_exit_code'], item['name'])
        kernels = {c['name']: c['command'][-1] for c in report['checks'] if c['name'].endswith('-coqchk')}
        self.assertEqual(kernels, {
            'Production-coqchk': 'CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership',
            'Probe-coqchk': 'CertiOS.audit.probes.V293PriorityTableOwnershipProbe',
            'Positive-coqchk': 'PriorityTableGate.Positive'})
        for path, digest in report['inputs'].items():
            self.assertEqual(sha(ROOT / path), digest, path)
        check = gate.helper(gate.HELPERS[0]).checked_assumptions
        self.assertEqual(check((LOG / 'gate01/Positive.log').read_text(), 6), report['positive_assumptions'])
        self.assertEqual(check((LOG / 'gate01/Probe.log').read_text(), 6), report['probe_assumptions'])

    def test_real_52_byte_entry_and_supplied_store_results(self):
        source = (ROOT / driver().SOURCE).read_text()
        entry = proof(source, 'Theorem V293_full_priority_table_entry')
        for required in ['length entries = 13', 'Forall', 'V293_bytes_writable M b 0%Z 52',
                         'V293_table_loads', 'V293_priority_cells_from_full_bytes']:
            self.assertIn(required, entry)
        constructor = proof(source, 'Theorem V293_priority_cells_from_full_bytes')
        for required in ['HeadW', 'TailW', 'Same', 'V293_raw_cells_above', 'V293_loadbytes_equal_range']:
            self.assertIn(required, constructor)
        stores = proof(source, 'Theorem V293_full_priority_table_two_stores')
        self.assertIn('forall entries b old new next R ge le M M1 M2', stores)
        self.assertEqual(stores.count('V293_priority_cells_store'), 2)
        self.assertIn('rewrite S1 in StoreFirst', stores)
        self.assertIn('rewrite S2 in StoreFinal', stores)
        self.assertNotIn('V293_critical_wait_joint_owned_execution', stores)
        self.assertNotIn('exists Mf', stores)

    def test_literal_entry_unused_slot_stale_half_and_sparse_controls(self):
        gate = driver()
        source = (ROOT / gate.PROBE).read_text()
        for name in gate.PROBE_ROOTS:
            self.assertIn('Print Assumptions ' + name + '.', source)
        for required in ['V293_bytes_writable (PriorityMemory true) 20%positive 0%Z 52',
                         'PriorityEntryLoads', 'PriorityLiteralOwned', 'PriorityLiteralTwoStores',
                         'PriorityAll13RemainWritable', 'PriorityTwoSlotsAreNotFullTable',
                         'PriorityMemory false', 'Loads 4', 'Loads 6', 'Loads 8']:
            self.assertIn(required, source)
        stores = proof(source, 'Theorem PriorityLiteralTwoStores')
        self.assertEqual(stores.count('V293_full_priority_table_two_stores'), 1)
        self.assertIn('exact S1', stores)
        self.assertIn('exact S2', stores)
        review = json.loads((LOG / 'bounded-scope.json').read_text())
        self.assertFalse(review['joint_api_return_completed'])
        self.assertFalse(review['goal_complete'])
        self.assertFalse(review['ucos3_started'])
        self.assertFalse(review['current_identity_source_only_full_clean_build'])

    def test_cache_and_old_document_identity(self):
        gate = driver()
        base = json.loads((LOG / 'baseline.json').read_text())
        record = json.loads((LOG / 'production-artifacts.json').read_text())
        production = {p for p in base['caches'] if 'V293TaskRecordOwnership.' in p}
        self.assertEqual(len(base['caches']), 835)
        self.assertEqual(len(production), 5)
        self.assertEqual(set(record['artifacts']), production)
        self.assertEqual(record['source_sha256'], sha(ROOT / gate.SOURCE))
        for path, digest in base['caches'].items():
            self.assertTrue((ROOT / path).is_file(), path)
            self.assertEqual(sha(ROOT / path),
                             record['artifacts'][path]['sha256'] if path in production else digest, path)
        for path in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((ROOT / path).read_bytes().endswith((LOG / (path + '.before.snapshot.txt')).read_bytes()))
