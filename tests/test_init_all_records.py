"""全任务初始化资源结构检查；真实语义另由 Coq/coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage79-init-all-records'
PROOF = ROOT / 'certiucos/v293/proofs/V293InitAllRecords.v'
PROBE = ROOT / 'audit/probes/V293InitAllRecordsProbe.v'


class InitAllRecordsTests(unittest.TestCase):
    def test_actual_stores_extend_not_assume_new_record(self):
        source = PROOF.read_text()
        self.assertIn(str(PROOF.relative_to(ROOT)), (ROOT / '_CoqProject').read_text().splitlines())
        self.assertNotIn('CertiOS.audit', source)
        self.assertNotRegex(re.sub(r'\(\*.*?\*\)', '', source, flags=re.S),
                            r'\b(Axiom|Parameter|Conjecture|Admitted|admit)\b')
        signature = source.split('Theorem V293_OS_TCBInit_fields_extend_records :', 1)[1].split('Proof.', 1)[0]
        entry, post = signature.split('exists Mf,', 1)
        self.assertIn('get tasks (bt,Int.repr base)=None', entry)
        self.assertIn('V293_tcb_init_old_fields', entry)
        self.assertIn('(V293_owned_task_records tasks ** R)', entry)
        self.assertNotIn('V293_owned_task_record (bt', entry)
        self.assertIn('set tasks (bt,Int.repr base)', post)
        self.assertIn('(ge,le,Mf,ir,aux,O,op)', post)
        self.assertNotIn('CurLINV', signature)
        self.assertIn('V293_OS_TCBInit_fields_execution', source)
        self.assertIn('apply V293_initialized_ready_record', source)

    def test_canonical_insertion_preserves_all_existing_resources(self):
        source = PROOF.read_text()
        insertion = source.split('Lemma V293_task_list_insert_record', 1)[1].split('Theorem V293_task_records_insert', 1)[0]
        self.assertIn('induction entries', insertion)
        self.assertIn('tidspec.blt t head', insertion)
        self.assertIn('tidspec.beq t head', insertion)
        self.assertIn('apply (IH', insertion)
        self.assertIn('V293_owned_task_list (TcbMod.set\'', insertion)
        self.assertNotIn('Atrue', source)
        self.assertIn('apply V293_raw_cells_move_frame in Final', source)
        self.assertIn('V293_tcb_init_record_remainder', source)

    def test_success_snapshots_and_nonempty_shared_block_fixture(self):
        for name, path in [('proof02', PROOF), ('probe06', PROBE)]:
            result = json.loads((LOG / (name + '.json')).read_text())
            self.assertEqual(result['exit'], 0)
            self.assertEqual(result['source_sha256'], hashlib.sha256(path.read_bytes()).hexdigest())
        source = PROBE.read_text()
        self.assertIn('Definition AllOldTid : tid := (301%positive,Int.repr 8)', source)
        self.assertIn('Definition AllNewTid : tid := (301%positive,Int.repr 128)', source)
        for name in ['AllLiteralEntry', 'AllExistingOwned', 'AllGoodCall', 'AllGoodSameMf']:
            self.assertIn('Theorem ' + name, source)
        self.assertIn('V293_OS_TCBInit_fields_extend_records (AllTasks 12)', source)
        self.assertIn('destruct (AllGoodCall P ks) as (Mf&Exec&Owned)', source)
        self.assertIn('load Tint32 Mf (601%positive,0%Z)=Some(Vint32(Int.repr 77))', source)

    def test_bad_mapping_refuted_after_actual_same_execution(self):
        source = PROBE.read_text()
        for name in ['AllRawCall', 'AllMapOnlyFactor', 'AllMapLookups', 'AllBadCall']:
            self.assertIn('Theorem ' + name, source)
        self.assertIn('destruct (AllRawCall P ks) as (Mf&Exec&Raw)', source)
        self.assertIn('~ AllState Mf |= V293_owned_task_records (AllUpdated 11)', source)
        self.assertIn('load Tint8 Mf (301%positive,58%Z)=Some(V293_byteval 12)', source)
        controls = json.loads((LOG / 'controls.json').read_text())
        self.assertTrue(controls['passed'])
        self.assertTrue(controls['no_early_rejection_credit'])
        self.assertFalse(controls['actual_abstract_map_update_claim'])

    def test_postcondition_single_factor_same_proof(self):
        plan = json.loads((LOG / 'post-control-plan.json').read_text())
        self.assertTrue(plan['frozen_before_control_compilation'])
        positive = (LOG / 'Positive.v.snapshot.txt').read_text()
        negative = (LOG / 'WrongNewPriority.v.snapshot.txt').read_text()
        self.assertEqual(positive.count(plan['old']), 1)
        self.assertEqual(positive.replace(plan['old'], plan['new'], 1), negative)
        self.assertEqual(positive.split('Proof.', 1)[1], negative.split('Proof.', 1)[1])
        for name, expected in [('Positive', 0), ('WrongNewPriority', 1)]:
            result = json.loads((LOG / (name + '.json')).read_text())
            self.assertEqual(result['exit'], expected)
            data = (LOG / (name + '.v.snapshot.txt')).read_bytes()
            self.assertEqual(result['source_sha256'], hashlib.sha256(data).hexdigest())
        self.assertIn('expected to have type', (LOG / 'WrongNewPriority.log').read_text())

    def test_prospective_order_and_protocol_hashes(self):
        order = json.loads((LOG / 'prospective-order.json').read_text())
        self.assertLess(order['protocol.json']['mtime_ns'], order['proof01.json']['mtime_ns'])
        self.assertLess(order['proof01.json']['mtime_ns'], order['probe01.json']['mtime_ns'])
        self.assertLess(order['post-control-plan.json']['mtime_ns'], order['Positive.json']['mtime_ns'])
        for name in ['protocol.json', 'post-control-plan.json']:
            self.assertEqual(order[name]['sha256'], hashlib.sha256((LOG / name).read_bytes()).hexdigest())
