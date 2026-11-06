"""启动到初始化任务记录的结构回归；语义由 Coq 内核另行检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage78-start-record'
PROOF = ROOT / 'certiucos/v293/proofs/V293StartRecord.v'
PROBE = ROOT / 'audit/probes/V293StartRecordProbe.v'


class StartRecordTests(unittest.TestCase):
    def test_production_real_call_not_assumed_current_or_record(self):
        source = PROOF.read_text()
        self.assertIn(str(PROOF.relative_to(ROOT)), (ROOT / '_CoqProject').read_text().splitlines())
        self.assertNotIn('CertiOS.audit', source)
        self.assertNotRegex(re.sub(r'\(\*.*?\*\)', '', source, flags=re.S),
                            r'\b(Axiom|Parameter|Conjecture|Admitted|admit)\b')
        signature = source.split('Theorem V293_OSStart_initialized_task :', 1)[1].split('Proof.', 1)[0]
        entry, post = signature.split('exists Mf,', 1)
        self.assertNotIn('CurTid', entry)
        self.assertNotIn('V293_owned_task_record', entry)
        self.assertNotIn('CurLINV', signature)
        self.assertIn('V293_tcb_init_final_fields', entry)
        self.assertIn('sfexec port nil nil', post)
        self.assertIn('V293_owned_task_record', post)
        self.assertIn('V293_OSStart_call_establishes_current', source)
        self.assertIn('V293_ready_selection_task', source)

    def test_consumed_fields_not_duplicated_in_remainder(self):
        source = PROOF.read_text()
        remainder = source.split('Definition V293_tcb_init_record_remainder', 1)[1].split('Lemma ', 1)[0]
        offsets = [int(n) for n in re.findall(r'base\+(\d+)', remainder)]
        selected = {50, 52, 51, 54, 53, 32, 48}
        self.assertEqual(len(offsets), 11)
        self.assertEqual(len(set(offsets)), 11)
        self.assertFalse(set(offsets) & selected)
        self.assertEqual(set(offsets) | selected,
                         {0, 4, 8, 12, 16, 18, 28, 32, 36, 44, 48, 49, 50, 51, 52, 53, 54, 55})
        self.assertIn('V293_raw_record_ownership', source)
        self.assertIn('V293_tcb_init_final_valid', source)

    def test_current_sources_have_successful_checked_snapshots(self):
        for name, path in [('proof06', PROOF), ('probe12', PROBE)]:
            result = json.loads((LOG / (name + '.json')).read_text())
            self.assertEqual(result['exit'], 0)
            self.assertEqual(result['source_sha256'], hashlib.sha256(path.read_bytes()).hexdigest())
        source = PROBE.read_text()
        for name in ['RecordLiteralEntry', 'RecordNoInitialTask', 'RecordGoodCall',
                     'RecordGoodSameMf', 'RecordGoodPostSound']:
            self.assertIn('Theorem ' + name, source)
        self.assertIn('Theorem RecordPortMissing : CurrentProgram 902%Z=None.', source)

    def test_priority_ablation_executes_both_arms(self):
        source = PROBE.read_text()
        for name in ['RecordOnlyFactor', 'RecordMemoryOnlyFactor', 'RecordColdCall', 'RecordBadCall']:
            self.assertIn('Theorem ' + name, source)
        self.assertIn('a<>(90%positive,50%Z)', source)
        self.assertIn('destruct (RecordColdCall 11)', source)
        self.assertIn('~ CurrentState Mf |= V293_owned_task_record StartTarget (Int.repr 12)', source)
        result = json.loads((LOG / 'controls.json').read_text())
        self.assertTrue(result['passed'])
        self.assertTrue(result['no_early_rejection_credit'])

    def test_postcondition_single_factor_same_proof(self):
        plan = json.loads((LOG / 'post-control-plan.json').read_text())
        self.assertTrue(plan['frozen_before_control_compilation'])
        positive = (LOG / 'Positive.v.snapshot.txt').read_text()
        negative = (LOG / 'WrongPriority.v.snapshot.txt').read_text()
        self.assertEqual(positive.count(plan['old']), 1)
        self.assertEqual(positive.replace(plan['old'], plan['new'], 1), negative)
        self.assertEqual(positive.split('Proof.', 1)[1], negative.split('Proof.', 1)[1])
        for name, expected in [('Positive', 0), ('WrongPriority', 1)]:
            result = json.loads((LOG / (name + '.json')).read_text())
            self.assertEqual(result['exit'], expected)
            data = (LOG / (name + '.v.snapshot.txt')).read_bytes()
            self.assertEqual(result['source_sha256'], hashlib.sha256(data).hexdigest())
        self.assertIn('expected to have type', (LOG / 'WrongPriority.log').read_text())

    def test_prospective_protocol_order(self):
        order = json.loads((LOG / 'prospective-order.json').read_text())
        self.assertLess(order['protocol.json']['mtime_ns'], order['proof01.json']['mtime_ns'])
        self.assertLess(order['proof01.json']['mtime_ns'], order['probe01.json']['mtime_ns'])
        self.assertLess(order['post-control-plan.json']['mtime_ns'], order['Positive.json']['mtime_ns'])
        for name in ['protocol.json', 'post-control-plan.json']:
            self.assertEqual(order[name]['sha256'], hashlib.sha256((LOG / name).read_bytes()).hexdigest())
