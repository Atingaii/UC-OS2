"""发布资源结构回归；真实执行与同末态语义另由Coq/coqchk检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage80-publish-records'
PROOF = ROOT / 'certiucos/v293/proofs/V293PublishRecords.v'
PROBE = ROOT / 'audit/probes/V293PublishRecordsProbe.v'


class PublishRecordsTests(unittest.TestCase):
    def test_real_publication_borrows_and_returns_record_fields(self):
        source = PROOF.read_text()
        self.assertIn(str(PROOF.relative_to(ROOT)), (ROOT / '_CoqProject').read_text().splitlines())
        self.assertNotIn('CertiOS.audit', source)
        self.assertNotRegex(re.sub(r'\(\*.*?\*\)', '', source, flags=re.S),
                            r'\b(Axiom|Parameter|Conjecture|Admitted|admit)\b')
        signature = source.split('Theorem V293_OS_TCBInit_publication_preserves_records :', 1)[1].split('Proof.', 1)[0]
        entry, post = signature.split('exists Mf,', 1)
        self.assertIn('get tasks (bt,Int.repr base)=None', entry)
        self.assertIn('V293_owned_task_records (set tasks', entry)
        self.assertIn('V293_local_steps P', post)
        self.assertIn('V293_owned_task_records (set tasks', post)
        self.assertIn('(ge,le,Mf,ir,aux,O,op)', post)
        self.assertIn('V293_OS_TCBInit_publication_execution P ks', source)
        self.assertIn('apply V293_ready_record_to_raw', source)
        self.assertIn('apply V293_raw_to_ready_record', source)
        links = source.split('Definition V293_pub_link_cells', 1)[1].split('Definition V293_pub_record_rest', 1)[0]
        for offset in [52, 53, 54]:
            self.assertNotIn(f'base+{offset}', links)
        self.assertNotIn('Atrue', source)

    def test_canonical_extraction_preserves_existing_record_frame(self):
        source = PROOF.read_text()
        extraction = source.split('Lemma V293_task_list_extract_fresh', 1)[1].split('Lemma V293_record_cells_to_raw', 1)[0]
        for text in ['induction entries', 'tidspec.blt t head', 'tidspec.beq t head',
                     'apply (IH', 'V293_owned_task_list (TcbMod.set\'',
                     'V293_owned_task_record t priority status message ** (V293_owned_task_records tasks ** R)']:
            self.assertIn(text, extraction)
        self.assertIn('V293_task_records_insert tasks', source)
        self.assertIn('destruct present', source)

    def test_success_snapshots_nonempty_head_and_shared_block(self):
        for name, path in [('proof06', PROOF), ('probe07', PROBE)]:
            result = json.loads((LOG / (name + '.json')).read_text())
            self.assertEqual(result['exit'], 0)
            self.assertEqual(result['source_sha256'], hashlib.sha256(path.read_bytes()).hexdigest())
        source = PROBE.read_text()
        self.assertIn('Definition PubOldTid : tid := (301%positive,Int.repr 8)', source)
        self.assertIn('Definition PubNewTid : tid := (301%positive,Int.repr 128)', source)
        self.assertIn('301%positive 8%Z true', source)
        for name in ['PubLiteralEntry', 'PubSpatialEntry', 'PubGoodCall',
                     'PubInitialHeadAndBack', 'PubGoodSameMf']:
            self.assertIn('Theorem ' + name, source)
        self.assertIn('V293_OS_TCBInit_publication_preserves_records PubTasks', source)

    def test_one_actual_Mf_carries_records_and_correct_back_pointer(self):
        source = PROBE.read_text()
        self.assertIn('destruct (PubGoodCall P ks enabled si ci) as (Mf&Exec&Owned)', source)
        self.assertIn('V293_task_records Mf PubUpdated', source)
        self.assertIn('get PubUpdated PubOldTid=Some(Int.repr 12,rdy,Vnull)', source)
        self.assertIn('get PubUpdated PubNewTid=Some(Int.repr 11,rdy,Vnull)', source)
        self.assertIn('load Tint8 M (403%positive,1%Z)=Some(V293_byteval 24)', source)
        self.assertIn('load Tint32 M (601%positive,0%Z)=Some(Vint32(Int.repr 77))', source)
        bad = source.split('Theorem PubBadBackPointer', 1)[1]
        self.assertIn('~ PubState Mf |= Amapsto (301%positive,32%Z)', bad)
        self.assertIn('Some(Vptr PubNewTid)', bad)
        self.assertIn('rewrite Read in Wrong. discriminate.', bad)
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
