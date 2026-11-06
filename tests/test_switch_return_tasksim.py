"""切换恢复接口及可达性边界回归；Coq 语义由递归内核检查承担。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage275-switch-return-tasksim'
PROD = 'certiucos/v293/proofs/V293SwitchReturnTaskSim.v'
PROBE = 'audit/probes/V293SwitchReturnTaskSimProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(s, name):
    return s.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class SwitchReturnTaskSimTests(unittest.TestCase):
    def test_original_inputs_and_registration(self):
        for p, h in read('baseline.json')['files'].items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d']:
                self.assertEqual(sha(R / p), h, p)
        project = (R / '_CoqProject').read_text().splitlines()
        self.assertEqual(project.count(PROD), 1)
        self.assertNotIn(PROBE, project)
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h, p)

    def test_original_switch_obligation_and_public_contract(self):
        s = (R / PROD).read_text()
        self.assertNotIn('CertiOS.audit', s)
        self.assertNotRegex(s, r'(?m)^Definition ')
        self.assertEqual(re.findall(r'^Theorem (\w+)\s*:', s, re.M), ['V293_switch_return_TaskSim'])
        main = theorem(s, 'V293_switch_return_TaskSim')
        pre = main.split(' TaskSim', 1)[0]
        for term in ['TaskSim', 'ProgSim', 'InitTaskSt', 'V293_global_steps', 'free Tint32']:
            self.assertNotIn(term, pre)
        for term in ['getsched(pc,A)=V293_scheduler', '(false,nil,top::ci)',
                     r'SWINVt G t //\\ SWPRE_NDEAD V293_scheduler x t',
                     'spec_seq sched(spec_done None)', 'RDYINV G t **LINV V293_shared_li t nil',
                     'exact AbsPartition', 'exact PreAll', 'intros Mc\' Oc\' o\' O\'',
                     'eapply V293_resume_callback']:
            self.assertIn(term, main)
        self.assertEqual(len(re.findall(r'^ - ', main, re.M)), 7)
        self.assertIn('Mc,ir,(false,nil,top::ci))Oc(SWPRE_NDEAD', main)

    def test_universal_resume_and_real_high_done_step(self):
        s = (R / PROD).read_text()
        cb = theorem(s, 'V293_resume_callback')
        stmt = cb.split('Proof.', 1)[0]
        self.assertIn("forall Mc Oc o' O'", stmt)
        self.assertNotIn('Mc=', stmt)
        self.assertNotIn('Oc=', stmt)
        for term in ['joinmem', 'join Ol Oc O\'', 'V293_resume_open', 'apply V293_resume_high_done',
                     'destruct top', 'V293_enabled_pending_TaskSim', 'V293_pending_return_TaskSim']:
            self.assertIn(term, cb)
        done = theorem(s, 'V293_resume_high_done')
        for term in ['hapi_step', 'hapiexit_step', 'ht_starS', 'htev_stepstar', 'htabtstar']:
            self.assertIn(term, done)
        self.assertEqual(len(re.findall(r'^ - ', done, re.M)), 7)

    def test_nonvacuous_callback_is_not_actual_switch_prefix(self):
        s = (R / PROBE).read_text()
        self.assertIn('PTnonvacuous', theorem(s, 'SPnonvacuous'))
        self.assertIn('eapply SPpartition', theorem(s, 'SPnonvacuous'))
        packet = s.split('Definition SPpacket', 1)[1].split('Lemma SPclose', 1)[0]
        self.assertNotIn('TaskSim', packet)
        partition = theorem(s, 'SPpartition')
        self.assertNotIn('exact UnusedSim', partition)
        self.assertIn('apply SPclose', partition)
        self.assertIn('forall ip A Mc\' Oc\' o\' O\'', theorem(s, 'SPresume'))
        self.assertIn('eapply V293_resume_callback', theorem(s, 'SPresume'))
        gap = theorem(s, 'SPcopied_cache_gap')
        for term in ['V293_byteval 4', 'OwnershipWaiting OwnershipTasks', 'V293_current_handoff_guard_reject',
                     'NCcurrent_mismatch', 'SCwaiting_not_highest']:
            self.assertIn(term, gap)
        old = (R / 'audit/probes/V293EnabledPendingTaskSimProbe.v').read_text()
        for term in ['free Tint32 98%positive(emp:mem)=None', 'forall R:asrt,~']:
            self.assertIn(term, theorem(old, 'EPowned_free_boundary'))
        self.assertIn('PTsaved_stack_boundary', theorem(old, 'EPsaved_stack_boundary'))
        doc = (R / 'audit/STAGE275_SWITCH_RETURN_TASKSIM.md').read_text()
        for term in ['Core 不复制', '任意兼容替换', '不是 OSIntExit 完整入口', '这不是整核证明',
                     '没有证明 true 快照从原完整入口可达', '不是仍 blocked 的 OwnershipWaiting',
                     '没有增加原真实活跃切出路径', '强 current', 'uCOS3 未开始', 'ADR-0010']:
            self.assertIn(term, doc)

    def test_stable_compile_and_recursive_kernel_check(self):
        roots = []
        for p in [PROD, PROBE]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', s, re.M)]
        self.assertEqual(len(roots), 9)
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
        self.assertEqual(t['roots_printed'], 9)
        self.assertEqual(list(read('assumptions-by-root.json')), roots)
        self.assertTrue(all(row['exit'] == 0 for row in t['commands']))
        self.assertLessEqual(set(t['assumptions']), {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
