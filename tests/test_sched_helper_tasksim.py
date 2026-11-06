"""helper 调用前缀回归；静态检查不替代 Coq 内核检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage282-helper-allocation'
PROD = 'certiucos/v293/proofs/V293SchedHelperTaskSim.v'
PROBE = 'audit/probes/V293SchedHelperAllocationProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def body(s, n):
    return s.split(n + ' :', 1)[1].split('Qed.', 1)[0]


class SchedHelperTaskSimTests(unittest.TestCase):
    def test_identity_and_registration(self):
        baseline = read('baseline.json')['files']
        self.assertEqual(len(baseline), 1647)
        for p, h in baseline.items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d', '.lia.cache', '.nia.cache']:
                self.assertEqual(sha(R / p), h, p)
        project = (R / '_CoqProject').read_text().splitlines()
        self.assertEqual(project.count(PROD), 1)
        self.assertNotIn(PROBE, project)
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h, p)
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])

    def test_all_successors_and_actual_frame_stripping(self):
        s = (R / PROD).read_text()
        bridge = body(s, 'V293_branching_cstep_TaskSim')
        for term in ['forall Cf mf,cstep', 'forall Mf Mall,join M Mf Mall',
                     '@cstep_frame', 'Posts _ _ Owned', 'map_join_assoc JSF',
                     'V293_enabled_join_frames', 'inapi_step', 'inv_ncare_le']:
            self.assertIn(term, bridge)
        self.assertNotIn('Unique', bridge)
        self.assertEqual(bridge.count('apply task_sim'), 1)

    def test_conditional_real_helper_prefix(self):
        s = (R / PROD).read_text()
        main = body(s, 'V293_sched_helper_call_TaskSim')
        stmt = main.split('Proof.', 1)[0]
        self.assertEqual(stmt.count('TaskSim('), 2)
        self.assertIn('forall b,fresh M b ->', stmt)
        self.assertIn('Amapsto(b,0%Z)Tint8 true Vundef **R', stmt)
        for bad in ['cstepstar', 'store(', 'evalval', 'V293_ready_fresh_avoiding']:
            self.assertNotIn(bad, main)
        for term in ['V293_branching_cstep_TaskSim', 'memory_has_fresh_block Mall',
                     'V293_tick_allocate_frame', 'AllocatedLocal', 'V293_helper_byte_successor',
                     'V293_helper_exec_successor', 'snpcall_step', 'sfexec_step',
                     'salloclv_step', 'sallocend_step', 'apply Body']:
            self.assertIn(term, main)
        self.assertEqual(re.findall(r'^Theorem (\w+)\s*:', s, re.M), ['V293_sched_helper_call_TaskSim'])

    def test_fixed_choice_counterexample_and_limits(self):
        s = (R / PROBE).read_text()
        two = body(s, 'HAtwo_real_successors')
        self.assertEqual(two.split('Proof.', 1)[0].count('cstep p'), 2)
        self.assertEqual(two.split('Proof.', 1)[0].count('(ge,(emp:env),M)'), 2)
        self.assertIn('~exists Cf mf,forall C\' m\'', body(s, 'HAno_fixed_successor'))
        frame = body(s, 'HAframe_excludes_old_choice')
        self.assertIn('~fresh(allocb M b', frame)
        self.assertIn('allocb_get_some', frame)
        self.assertIn('HAallocation', body(s, 'HAhelper_real_prefix'))
        doc = (R / 'audit/STAGE282_HELPER_ALLOCATION.md').read_text()
        for term in ['是条件接口', '不是完整调用入口 TaskSim', 'GOOD_OS 未闭合',
                     'uCOS3 未开始', '不是完整入口执行消融', '没有接通第281步',
                     '所有真实执行步骤', '消去本步的函数体 TaskSim 前提']:
            self.assertIn(term, doc)

    def test_stable_compilation_and_recursive_kernel(self):
        stable = read('stable-compiles.json')
        roots = []
        for p in [PROD, PROBE]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            if p == PROD:
                self.assertNotIn('CertiOS.audit', s)
            names = re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', s, re.M)
            roots.extend(Path(p).stem + '.' + n for n in names)
            self.assertEqual(stable[p]['sha256'], sha(R / p))
            self.assertEqual(stable[p]['roots'], names)
            self.assertEqual(len(stable[p]['runs']), 2)
            for row in stable[p]['runs']:
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['source_sha256'], row['initial_source_sha256'])
                self.assertEqual(row['source_sha256'], sha(R / p))
        self.assertEqual(len(roots), 9)
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], 9)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))
        self.assertEqual(list(read('assumptions-by-root.json')), roots)
        self.assertLessEqual(set(trust['assumptions']), {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
