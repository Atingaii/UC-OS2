"""Supplement actual same-return joint ownership proofs, controls and kernel checks."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage26-table-joint'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def driver():
    spec = importlib.util.spec_from_file_location('priority_table_gate', ROOT / 'scripts/check-v293-table-joint-ownership.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def proof(source, declaration):
    return source[source.index(declaration):].split('Qed.', 1)[0]


class TableJointTests(unittest.TestCase):
    def test_preserved_2505_line_prefix_and_frozen_inputs(self):
        gate = driver()
        base = json.loads((LOG / 'baseline.json').read_text())
        prefix = (LOG / 'Before_Ownership.v.snapshot.txt').read_bytes()
        self.assertEqual(len(prefix.decode().splitlines()), 2505)
        self.assertEqual(hashlib.sha256(prefix).hexdigest(), base['sources'][gate.SOURCE])
        self.assertTrue((ROOT / gate.SOURCE).read_bytes().startswith(prefix))
        self.assertEqual(len(base['sources']), 167)
        self.assertEqual(len(base['protected']), 12)
        self.assertEqual(len(base['history']), 9439)
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
        binding = json.loads((LOG / 'control-binding02.json').read_text())
        self.assertTrue(binding['prospective_before_control_execution'])
        self.assertEqual(binding['source_sha256'], sha(ROOT / gate.SOURCE))
        self.assertEqual(binding['negative_sha256'],
                         {n: hashlib.sha256(v.encode()).hexdigest() for n, v in controls.items()})
        self.assertEqual(set(controls), {'TablePointerOverlapAllowed', 'StaleJointTable'})
        report = json.loads((LOG / 'gate02/result.json').read_text())
        checks = {c['name']: c for c in report['checks']}
        for name, negative in controls.items():
            root = gate.CONTROL_ROOTS[name]
            a = source.index('Proof.', source.index(root))
            b = negative.index('Proof.', negative.index(root))
            self.assertEqual(source[a:], negative[b:])
            self.assertEqual(negative, (LOG / ('gate02/' + name + '.v.snapshot.txt')).read_text())
            self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.', negative)
            c = checks[name]
            self.assertEqual(c['exit_code'], 1)
            self.assertEqual(c['proof_line'], negative[:b].count('\n') + 1)
            self.assertGreater(c['error_line'], c['proof_line'])
            self.assertFalse(c['downstream_credit'])
            self.assertTrue(c['entire_proof_suffix_unchanged'])

    def test_actual_compilation_assumptions_and_independent_kernel_checks(self):
        gate = driver()
        report = json.loads((LOG / 'gate02/result.json').read_text())
        for flag in ['passed', 'inputs_unchanged', 'temporary_tree_removed']:
            self.assertTrue(report[flag])
        self.assertEqual(len(gate.FIXTURES), 19)
        self.assertEqual(len(report['checks']), 27)
        for item in report['checks']:
            self.assertEqual(item['exit_code'], item['expected_exit_code'], item['name'])
        kernels = {c['name']: c['command'][-1] for c in report['checks'] if c['name'].endswith('-coqchk')}
        self.assertEqual(kernels, {
            'Production-coqchk': 'CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership',
            'Probe-coqchk': 'CertiOS.audit.probes.V293TableJointReturnProbe',
            'Positive-coqchk': 'TableJointGate.Positive'})
        for path, digest in report['inputs'].items():
            self.assertEqual(sha(ROOT / path), digest, path)
        check = gate.helper(gate.HELPERS[0]).checked_assumptions
        self.assertEqual(check((LOG / 'gate02/Positive.log').read_text(), 6), report['positive_assumptions'])
        self.assertEqual(check((LOG / 'gate02/Probe.log').read_text(), 6), report['probe_assumptions'])

    def test_one_execution_one_final_memory_real_joint_table(self):
        source = (ROOT / driver().SOURCE).read_text()
        root = proof(source, 'Theorem V293_critical_wait_table_joint_owned_execution')
        self.assertEqual(root.count('destruct (V293_critical_event_return_bitmap_owned '), 1)
        self.assertIn('as (Mf & Surviving & BitmapOwned & Result)', root)
        for required in ['FullTableWritable', 'TableValuesValid', 'FullJoint',
                         'V293_spatial_priority_table_joint', 'V293_physical_shared_fields_joint',
                         'V293_current_tasks_cells_local', 'V293_owned_priority_table b']:
            self.assertIn(required, root)
        constructor = proof(source, 'Lemma V293_spatial_priority_table_joint')
        for required in ['Support', 'RestW', 'RestReads', 'Same', 'V293_full_priority_table_entry']:
            self.assertIn(required, constructor)
        self.assertNotIn('V293_critical_wait_joint_owned_execution', root)

    def test_joint_literal_consumers_and_bounded_scope(self):
        gate = driver()
        source = (ROOT / gate.PROBE).read_text()
        for name in gate.PROBE_ROOTS:
            self.assertIn('Print Assumptions ' + name + '.', source)
        root = proof(source, 'Theorem TableUnifiedOwnedFullReturn')
        self.assertEqual(root.count('V293_critical_wait_table_joint_owned_execution'), 1)
        self.assertIn('TableEntry52', root)
        for required in ['TableJointAssertion', 'V293_full_priority_table_any_slot_store',
                         'Loads 4', 'Loads 6', 'Loads 8', 'UnifiedUseAllResources',
                         'wait expected_wait_reason Int.one', 'unfold language.priority, msg in Ready', 'rewrite Waiting in Ready']:
            self.assertIn(required, source)
        review = json.loads((LOG / 'bounded-scope.json').read_text())
        self.assertTrue(review['selected_blocked_joint_api_return_completed'])
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
