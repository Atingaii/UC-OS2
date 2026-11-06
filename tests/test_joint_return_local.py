"""Protocol checks supplement actual same-return Coq proofs and kernel checks."""
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage26-joint-return'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def driver():
    spec = importlib.util.spec_from_file_location('joint_return_gate', ROOT / 'scripts/check-v293-joint-return.py')
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class JointReturnTests(unittest.TestCase):
    def test_original_1861_lines_and_protected_inputs(self):
        g = driver()
        b = json.loads((LOG / 'baseline.json').read_text())
        prefix = (LOG / 'Before_Ownership.v.snapshot.txt').read_bytes()
        self.assertEqual(hashlib.sha256(prefix).hexdigest(), b['sources'][g.SOURCE])
        self.assertEqual(len(prefix.decode().splitlines()), 1861)
        self.assertTrue((ROOT / g.SOURCE).read_bytes().startswith(prefix))
        self.assertEqual(len(b['sources']), 167)
        self.assertEqual(len(b['protected']), 12)
        for p, h in {**{p: h for p, h in b['sources'].items() if p != g.SOURCE}, **b['protected']}.items():
            self.assertEqual(sha(ROOT / p), h, p)

    def test_prospective_single_factor_controls(self):
        g = driver()
        source = (ROOT / g.SOURCE).read_text()
        controls = g.controls(source)
        self.assertTrue(json.loads((LOG / 'protocol.json').read_text())['prospective'])
        self.assertEqual(set(controls), {'PointerOverlapAllowed', 'StaleJointEvent'})
        for name, negative in controls.items():
            root = g.CONTROL_ROOTS[name]
            self.assertEqual(negative[negative.index('Proof.', negative.index(root)):],
                             source[source.index('Proof.', source.index(root)):])
            self.assertEqual(negative, (LOG / f'gate02/{name}.v.snapshot.txt').read_text())
            self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.', negative)

    def test_actual_coqc_and_independent_kernel_checks(self):
        g = driver()
        r = json.loads((LOG / 'gate02/result.json').read_text())
        for flag in ['passed', 'inputs_unchanged', 'temporary_tree_removed']:
            self.assertTrue(r[flag])
        self.assertEqual(len(g.FIXTURES), 17)
        self.assertEqual(len(r['checks']), 25)
        for c in r['checks']:
            self.assertEqual(c['exit_code'], c['expected_exit_code'])
            if c['name'] in g.CONTROL_ROOTS:
                self.assertFalse(c['downstream_credit'])
                self.assertTrue(c['entire_proof_suffix_unchanged'])
                snapshot = (LOG / ('gate02/' + c['name'] + '.v.snapshot.txt')).read_text()
                actual_proof_line = snapshot[:snapshot.index('Proof.', snapshot.index(
                    g.CONTROL_ROOTS[c['name']]))].count('\n') + 1
                self.assertEqual(c['proof_line'], actual_proof_line)
                self.assertGreater(c['error_line'], c['proof_line'])
        modules = {c['name']: c['command'][-1] for c in r['checks'] if c['name'].endswith('-coqchk')}
        self.assertEqual(modules['Probe-coqchk'], 'CertiOS.audit.probes.V293JointReturnProbe')
        self.assertEqual(modules['Production-coqchk'], 'CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership')
        self.assertEqual(modules['Positive-coqchk'], 'JointReturnGate.Positive')
        for p, h in r['inputs'].items():
            self.assertEqual(sha(ROOT / p), h, p)
        check = g.helper(g.HELPERS[0]).checked_assumptions
        self.assertEqual(check((LOG / 'gate02/Positive.log').read_text(), 4), r['positive_assumptions'])
        self.assertEqual(check((LOG / 'gate02/Probe.log').read_text(), 7), r['probe_assumptions'])

    def test_one_execution_and_identical_entry_conditions(self):
        g = driver()
        s = (ROOT / g.SOURCE).read_text()
        root = s[s.index('Theorem V293_critical_wait_joint_owned_execution'):]
        header, proof = root.split('Proof.', 1)
        old = s[s.index('Theorem V293_critical_wait_current_all_owned_execution'):]
        self.assertEqual(header.split("exists Mf Os' OO',", 1)[0].split(':', 1)[1],
                         old.split("exists Mf Os' OO',", 1)[0].split(':', 1)[1])
        self.assertEqual(proof.count('V293_critical_event_return_bitmap_owned'), 1)
        self.assertEqual(proof.count('exists Mf.'), 1)
        for forbidden in ['V293_critical_wait_current_all_owned_execution',
                          'V293_critical_wait_all_records_owned_execution']:
            self.assertNotIn(forbidden, proof)
        for link in ['V293_wait_prio_owned_step', 'V293_owned_task_records_update',
                     'V293_current_task_records_block_frame', 'V293_current_tasks_bytes_joint',
                     'V293_current_tasks_bytes_fields_reconstruct']:
            self.assertIn(link, proof)
        for resource in ['CurTid abstract_current', 'V293_owned_task_records',
                         'V293_bitmap_layout', 'V293_shared_fields']:
            self.assertIn(resource, header)
        helper = s[s.index('Lemma V293_current_tasks_bytes_joint'):s.index('Lemma V293_owned_cells_abstract_empty')]
        for necessary in ['ResidualValues', 'map_join_get_none', 'get M a = Some (true,raw)', 'PointerApart', 'TasksApart']:
            self.assertIn(necessary, helper)

    def test_literal_entry_and_joint_store_consumer(self):
        g = driver()
        s = (ROOT / g.PROBE).read_text()
        for name in g.PROBE_ROOTS:
            self.assertIn('Print Assumptions ' + name + '.', s)
        body = s[s.index('Theorem UnifiedOwnedFullReturn'):s.index('Theorem UnifiedFinalReadAndWritable')]
        self.assertEqual(body.count('V293_critical_wait_joint_owned_execution'), 1)
        self.assertNotIn('JointOwnedFullReturn', body)
        self.assertNotIn('BitmapOwnedFullReturn', body)
        self.assertIn('V293_owned_record_cells (V293_bitmap_layout', body)
        consumer = s[s.index('Theorem UnifiedBitmapStorePreservesJoint'):]
        for link in ['V293_owned_cells_byte_update', 'Framed', 'V293_put_byte_store', 'CurTid',
                     'V293_owned_task_records', 'V293_shared_fields']:
            self.assertIn(link, consumer)

    def test_frozen_history_and_document_bodies(self):
        b = json.loads((LOG / 'baseline.json').read_text())
        for p, h in b['history'].items():
            self.assertEqual(sha(ROOT / p), h, p)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((ROOT / p).read_bytes().endswith((LOG / (p + '.before.snapshot.txt')).read_bytes()))
        # Rebuilding the intentionally changed production module replaces its
        # own five artifacts. Every other pre-existing cache is immutable.
        produced = json.loads((LOG / 'production-artifacts.json').read_text())
        self.assertEqual(len(produced['artifacts']), 5)
        self.assertEqual(set(produced['artifacts']),
                         {p for p in b['caches'] if 'V293TaskRecordOwnership.' in p})
        self.assertEqual(produced['source_sha256'], sha(ROOT / driver().SOURCE))
        gate = json.loads((LOG / 'gate02/result.json').read_text())
        self.assertTrue(gate['passed'])
        self.assertEqual({c['name']: c['exit_code'] for c in gate['checks']}['Production-coqchk'], 0)
        for p, h in b['caches'].items():
            self.assertTrue((ROOT / p).exists(), p)
            if p in produced['artifacts']:
                self.assertEqual(sha(ROOT / p), produced['artifacts'][p]['sha256'], p)
            else:
                self.assertEqual(sha(ROOT / p), h, p)
        self.assertEqual(len(b['caches']) - len(produced['artifacts']), 830)
        self.assertFalse(json.loads((LOG / 'adversarial-review.json').read_text())['goal_complete'])
