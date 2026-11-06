"""结构检查不替代实际执行、独立fixture与Coq内核校验。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage81-publish-return-records'
PROOF = ROOT / 'certiucos/v293/proofs/V293PublishReturnRecords.v'
PROBE = ROOT / 'audit/probes/V293PublishReturnRecordsProbe.v'


class PublishReturnRecordsTests(unittest.TestCase):
    def test_actual_publication_and_free_are_composed(self):
        s = PROOF.read_text()
        self.assertIn(str(PROOF.relative_to(ROOT)), (ROOT / '_CoqProject').read_text().splitlines())
        self.assertNotIn('CertiOS.audit', s)
        self.assertNotRegex(re.sub(r'\(\*.*?\*\)', '', s, flags=re.S),
                            r'\b(Axiom|Parameter|Conjecture|Admitted|admit)\b')
        for part in ['V293_OS_TCBInit_publication_preserves_records tasks P',
                     'V293_error_return_execution P', 'apply V293_csteps_local;exact Return',
                     'V293_tcb_second_hook_cont f hi hc caller ks',
                     '(curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((ge,caller,Mf)',
                     'get Mf (b,Z.of_nat k)=None']:
            self.assertIn(part, s)

    def test_one_joint_fragment_is_transported_not_independent_records(self):
        s = PROOF.read_text().split('Theorem V293_OS_TCBInit_publication_return_preserves_records')[0]
        for part in ['(V293_owned_task_records tasks ** V293_rdy_raw_cells cells Aemp) ** R',
                     'destruct Joint as (mp&mr', 'Maps.sub mp Mf',
                     'get mp (c,i)=None', 'exists mp. exists remaining.',
                     'V293_owned_task_list_local', 'V293_raw_cells_absent_block',
                     'V293_raw_cells_environment', 'apply Rebase']:
            self.assertIn(part, s)
        self.assertNotIn('V293_owned_task_record_block_frame', s)
        self.assertNotIn('V293_owned_task_records_block_frame', s)

    def test_finite_frame_support_and_caller_rebase_are_explicit(self):
        signature = PROOF.read_text().split('Theorem V293_OS_TCBInit_publication_return_preserves_records :')[1].split('Proof.')[0]
        entry, post = signature.split('exists Mf,')
        self.assertIn('In (t,value) (TcbMod.lst tasks\') -> ~In (fst t) blocks', entry)
        self.assertIn('In (a,tp,v) (tl after++frame) -> ~In (fst a) blocks', entry)
        self.assertIn('V293_rdy_raw_cells (tl after++frame) Atrue', post)
        self.assertNotRegex(signature, r'\bR\b')
        self.assertIn('(ge,caller,Mf,ir,aux,O,op)', post)
        self.assertIn('get tasks (bt,Int.repr base)=None', entry)

    def test_successful_exact_source_snapshots(self):
        for label, path in [('proof09', PROOF), ('probe06', PROBE)]:
            row = json.loads((LOG / (label + '.json')).read_text())
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['source_sha256'], hashlib.sha256(path.read_bytes()).hexdigest())
            self.assertEqual(path.read_bytes(), (LOG / (label + '.v.snapshot.txt')).read_bytes())
        s = PROBE.read_text()
        for part in ['(301%positive,Int.repr 8)', '(301%positive,Int.repr 128)',
                     'Definition RetCaller : env := sig 777%Z', 'RetFreed Mf',
                     'V293_task_records Mf RetUpdated', 'RetReads Mf',
                     'load Tint32 M (601%positive,0%Z)=Some(Vint32(Int.repr 77))']:
            self.assertIn(part, s)

    def test_semantic_negative_runs_to_actual_return(self):
        s = PROBE.read_text()
        for part in ['Theorem RetInitialLocal', 'Theorem RetFreedLocalCannotSurvive',
                     'Theorem RetActualNoLocal',
                     'destruct (RetGoodSameMf P f hi hc ks enabled si ci)',
                     'get Mf (208%positive,0%Z)=None', 'rewrite Gone in Full. discriminate.']:
            self.assertIn(part, s)
        self.assertTrue(json.loads((LOG / 'controls.json').read_text())['passed'])

    def test_prospective_single_factor_same_proof_control(self):
        plan = json.loads((LOG / 'post-control-plan.json').read_text())
        a = (LOG / 'PositiveFinal.v.snapshot.txt').read_text()
        b = (LOG / 'WrongNewPriorityFinal.v.snapshot.txt').read_text()
        self.assertEqual(a.count(plan['old']), 1)
        self.assertEqual(a.replace(plan['old'], plan['new'], 1), b)
        self.assertEqual(a.split('Proof.')[1], b.split('Proof.')[1])
        for label, exit_code in [('PositiveFinal', 0), ('WrongNewPriorityFinal', 1)]:
            self.assertEqual(json.loads((LOG / (label + '.json')).read_text())['exit'], exit_code)
        order = json.loads((LOG / 'prospective-order.json').read_text())
        self.assertLess(order['protocol.json']['mtime_ns'], order['proof01.json']['mtime_ns'])
        self.assertLess(order['post-control-plan.json']['mtime_ns'], order['Positive.json']['mtime_ns'])
        for name in ['protocol.json', 'post-control-plan.json']:
            self.assertEqual(order[name]['sha256'], hashlib.sha256((LOG / name).read_bytes()).hexdigest())
