"""接线、身份和证据回归；语义对照由 Coq 内核检查，不由字符串检查替代。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage149-tick-task-bridge'
BRIDGE = 'certiucos/v293/proofs/V293TimeTickTaskBridge.v'
PROBE = 'audit/probes/V293TimeTickTaskBridgeProbe.v'


class TickTaskBridgeTests(unittest.TestCase):
    def setUp(self):
        self.bridge = (R / BRIDGE).read_text()
        self.probe = (R / PROBE).read_text()

    def test_frozen_source_and_original_iteration(self):
        row = json.loads((D / 'source-identity.json').read_text())
        source = (R / row['current_upstream_file']).read_bytes()
        self.assertEqual(hashlib.sha256(source).hexdigest(), row['current_upstream_file_sha256'])
        i = row['identity']
        lines = b''.join(source.splitlines(keepends=True)[i['first_line'] - 1:i['last_line']])
        self.assertEqual(hashlib.sha256(lines).hexdigest(), i['source_lines_sha256'])
        self.assertFalse(row['new_AST'])
        self.assertNotIn('Definition V293_tick_iteration', self.bridge)
        self.assertIn('V293_tick_node_iteration_owned_execution', self.bridge)

    def test_same_memory_abstract_and_spatial_bridge(self):
        statement = self.bridge.split('Theorem V293_tick_wait_iteration_refines :', 1)[1].split('Proof.', 1)[0]
        for term in ('exists Mf,', 'spec_step sd', 'V293_local_steps P',
                     'V293_task_records Mf tasks\'', 'V293_priority_table entries tasks\'',
                     'V293_bitmap_tasks (fst rr) (snd rr) tasks\'',
                     'V293_shared_fields current tasks\' events now ** R',
                     'V293_owned_task_records (del tasks (b,Int.repr base))'):
            self.assertIn(term, statement)
        for oracle in ('evalval', 'store ', 'cstepstar'):
            self.assertNotIn(oracle, statement)
        for term in ('spec_prim_step', 'V293_shared_replace_slot', 'V293_tick_wait_record_after'):
            self.assertIn(term, self.bridge)
        # The bitmap preservation proof did not use a priority table: remove it.
        bitmap = self.bridge.split('Theorem V293_tick_wait_bitmap_tasks :', 1)[1].split('Qed.', 1)[0]
        self.assertNotIn('entries', bitmap)
        self.assertNotIn('V293_priority_table', bitmap)

    def test_nonempty_entry_and_single_factor_controls(self):
        for term in ('OwnershipCellsSpatial', 'Theorem BridgeEntry :',
                     'V293_tick_wait_iteration_refines', 'Theorem BridgeLiteral :',
                     'BridgeTasks d : TcbMod.map :=', 'sig BridgeTask'):
            self.assertIn(term, self.probe)
        countdown = self.probe.split('Theorem BridgeCountdownControl :', 1)[1].split('Proof.', 1)[0]
        for term in ('BridgeExecution P ks 3%Z Mf', 'V293_task_records Mf (BridgeNewTasks 3%Z)',
                     '~ V293_task_records Mf (BridgeTasks 3%Z)'):
            self.assertIn(term, countdown)
        expiry = self.probe.split('Theorem BridgeExpiryControls :', 1)[1].split('Proof.', 1)[0]
        for term in ('BridgeExecution P ks 1%Z Mf',
                     'V293_bitmap_tasks 0 4 (BridgeNewTasks 1%Z)',
                     '~ V293_bitmap_tasks 0 0 (BridgeNewTasks 1%Z)',
                     '~ V293_bitmap_tasks 0 4 (BridgeTasks 1%Z)',
                     'load Tint8 Mf (93%positive,1%Z)=Some (V293_byteval 4)'):
            self.assertIn(term, expiry)
        self.assertIn('Theorem BridgeOtherSlots :', self.probe)

    def test_subset_boundary_not_full_tick_claim(self):
        for reason in ('os_stat_time', 'os_stat_sem', 'os_stat_mbox', 'os_stat_q', 'os_stat_mutexsem'):
            self.assertIn(reason, self.bridge)
        suspended = self.probe.split('Theorem BridgeSuspensionBoundary :', 1)[1].split('Proof.', 1)[0]
        for term in ('ExpiryExecution P ks false 9 Mf',
                     'load Tint8 Mf (81%positive,56%Z)=Some (V293_byteval 8)',
                     '(forall reason, V293_tick_reason_stat reason<>9)'):
            self.assertIn(term, suspended)
        self.assertNotIn('V293_tick_wait_step', suspended)
        for term in ('CertiOS.audit.', 'Theorem GOOD_OS', 'Theorem WFIFun', 'verified_os'):
            self.assertNotIn(term, self.bridge)

    def test_stable_compiles_no_holes(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('bridge', BRIDGE), ('probe', PROBE)]:
            source = (R / path).read_bytes()
            self.assertNotRegex(source.decode(), r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show|idtac)\b')
            self.assertNotRegex(source.decode(), re.compile(r'^Inductive ', re.M))
            row = json.loads((D / (stable[kind] + '.json')).read_text())
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256(source).hexdigest())
            self.assertEqual(source, (D / (stable[kind] + '.v.snapshot.txt')).read_bytes())
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(BRIDGE), 1)

    def test_old_source_and_evidence_not_rewritten(self):
        base = json.loads((D / 'baseline.json').read_text())
        for name, row in base.items():
            if name.endswith('.v') or name.startswith(('csrc/', 'framework/', 'tactics/', 'audit/logs/')):
                self.assertEqual(hashlib.sha256((R / name).read_bytes()).hexdigest(), row['sha256'], name)


if __name__ == '__main__':
    unittest.main()
