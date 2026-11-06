"""Pending TaskSim 的结构/证据回归；形式语义由 Coq 内核核查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage273-pending-return-tasksim'
PROD = 'certiucos/v293/proofs/V293PendingReturnTaskSim.v'
PROBE = 'audit/probes/V293PendingReturnTaskSimProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class PendingReturnTaskSimTests(unittest.TestCase):
    def test_original_inputs_and_registration(self):
        for p, h in read('baseline.json')['files'].items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d']:
                self.assertEqual(sha(R / p), h, p)
        project = (R / '_CoqProject').read_text().splitlines()
        self.assertEqual(project.count(PROD), 1)
        self.assertNotIn(PROBE, project)
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h, p)
        lines = (R / 'csrc/upstream/v2.93.01/checkout/Source/os_core.c').read_text().splitlines()
        for n, s in read('source-identity.json')['line_anchors'].items():
            self.assertEqual(lines[int(n) - 1].strip(), s)

    def test_universal_frames_and_original_obligations(self):
        src = (R / PROD).read_text()
        self.assertNotIn('CertiOS.audit', src)
        self.assertNotRegex(src, r'(?m)^Definition ')
        internal = theorem(src, 'V293_pending_internal_TaskSim')
        for term in ['forall Mf Mall,join M Mf Mall', "join M' Mf Mall'", 'forall Cf ofull,loststep',
                     'apply task_sim', 'V293_pending_shared_empty', 'V293_pending_join_frame',
                     'V293_return_disabled_INV_empty', 'inversion Bad', 'exact Progress']:
            self.assertIn(term, internal)
        self.assertEqual(len(re.findall(r'^ - ', internal, re.M)), 7)
        self.assertIn('Ms=(emp:mem) /\\Os=(emp:osabst)', theorem(src, 'V293_pending_shared_empty'))
        self.assertIn('V293_cstep_not_primitive', theorem(src, 'V293_pending_cstep_successor'))

    def test_public_owned_saved_to_exact_endpoint(self):
        src = (R / PROD).read_text()
        self.assertEqual(re.findall(r'^Theorem (\w+)\s*:', src, re.M), ['V293_pending_return_TaskSim'])
        body = theorem(src, 'V293_pending_return_TaskSim')
        stmt = body.split('Proof.', 1)[0]
        pre = stmt.split(' TaskSim', 1)[0]
        for term in ['InitTaskSt', 'TaskSim', 'ProgSim', 'V293_global_steps', 'free Tint32']:
            self.assertNotIn(term, pre)
        for term in ['(false,nil,false::ci)', '(forall i,ir i=false)',
                     'Amapsto(b,0%Z)Tint32 true v **(Core **CurTid t)',
                     '(RDYINV G t **LINV V293_shared_li t nil)']:
            self.assertIn(term, stmt)
        for term in ['free_mono', 'join_free', 'V293_tick_free_owned', 'V293_excrit_successor',
                     'V293_free_cell_successor', 'V293_free_end_successor', 'V293_return_client_coinduction']:
            self.assertIn(term, body)
        self.assertNotIn('Atrue', stmt)

    def test_same_entry_reached_pending_and_boundaries(self):
        src = (R / PROBE).read_text()
        full = theorem(src, 'PTfull_call')
        pre = full.split(' exists Mc Ms Mf,', 1)[0]
        self.assertEqual(pre.count('fresh('), 2)
        for term in ['TaskSim', 'PTpacket', 'V293_global_steps', 'ProgSim']:
            self.assertNotIn(term, pre)
        for term in ['FTto_switch', 'PTselected', 'STselected_return', 'STsaved_retained', "assert(Ms'=Ms)by congruence"]:
            self.assertIn(term, full)
        for term in ['V293_ready_storage_switch_step', 'V293_current_handoff_switch_highest_frame', 'apply PTclose']:
            self.assertIn(term, theorem(src, 'PTselected'))
        for term in ['free Tint32 98%positive(emp:mem)=None', 'forall R:asrt,~', 'free_mono', 'discriminate Impossible']:
            self.assertIn(term, theorem(src, 'PTowned_free_boundary'))
        for term in ['false::ci', 'true::ci', '~exists C\' st\'']:
            self.assertIn(term, theorem(src, 'PTsaved_stack_boundary'))
        self.assertIn('memory_has_fresh_block', theorem(src, 'PTnonvacuous'))
        doc = (R / 'audit/STAGE273_PENDING_RETURN_TASKSIM.md').read_text()
        for term in ['不是整核', '任意可分离外部 frame', '不复制', '不是目标任务私有 LINV',
                     '所有权分区边界', '没有证明 IE=true 的 pending TaskSim', '原任务仍 blocked',
                     'uCOS3 未开始', 'ADR-0010', '不是把 whole-heap free 成功当作任务所有权证据']:
            self.assertIn(term, doc)

    def test_stable_compiles_recursive_trust_and_protocol(self):
        roots = []
        for p in [PROD, PROBE]:
            src = (R / p).read_text()
            self.assertNotRegex(src, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        self.assertEqual(len(roots), 13)
        for p, labels in read('stable-compiles.json').items():
            self.assertEqual(len(labels), 2)
            for n in labels:
                row = read(n + '.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
                self.assertEqual(row['source_sha256'], sha(R / p))
        t = read('trust.json')
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 13)
        self.assertEqual(list(read('assumptions-by-root.json')), roots)
        self.assertTrue(all(row['exit'] == 0 for row in t['commands']))
        self.assertLessEqual(set(t['assumptions']), {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
