"""具体实例的接口／来源回归；Coq 与递归 coqchk 检查证明有效性。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage264-dispatch-resume-witness'
PROD = 'certiucos/v293/proofs/V293ResumedReturnProgSim.v'
PROBE = 'audit/probes/V293DispatchResumeWitnessProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class DispatchResumeWitnessTests(unittest.TestCase):
    def test_existing_production_and_project_unchanged(self):
        baseline = read('baseline.json')['files']
        for p in [PROD, '_CoqProject', '.Makefile.coq.d']:
            self.assertEqual(sha(R / p), baseline[p])
        src = (R / PROD).read_text()
        self.assertEqual(len(re.findall(r'^Theorem ', src, re.M)), 3)
        for name in ['V293_pending_exit_progsim', 'V293_switch_pending_exit_progsim',
                     'V293_exit_call_resume_progsim']:
            self.assertEqual(theorem(src, name).split('Proof.', 1)[0].count('ProgSim'), 2)
        self.assertNotIn('CertiOS.audit.', src)
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h)

    def test_actual_full_scheduler_canonical_heap(self):
        body = theorem((R / PROBE).read_text(), 'DPscheduled_canonical')
        self.assertNotIn('ProgSim', body.split('Proof.', 1)[0])
        for term in ['forall ks', 'CGmemory OwnershipWaiting true 0 0',
                     'V293_OSSched_unlocked_prefix', 'V293_ready_dispatch_call',
                     'V293_ready_lenv_frame', 'HalfPermMap.extensionality',
                     'V293_full_byte_load_encoding', 'rewrite Canonical in Store',
                     'V293_ready_selection_range', 'RTonly_ready']:
            self.assertIn(term, body)

    def test_same_heap_counter_copy_switch_and_real_free(self):
        src = (R / PROBE).read_text()
        body = theorem(src, 'DPdispatch_storage')
        self.assertNotIn('ProgSim', body.split('Proof.', 1)[0])
        for term in ['DPscheduled_canonical(kseq DPtail ks)',
                     'Int.add Int.mone Int.one=Int.zero',
                     'load Tint32 M1(95%positive,0%Z)=Some(Vint32 Int.zero)',
                     'V293_owned_record_cell_update', 'V293_exit_boundary_tail',
                     'V293_handoff_copy_execution', 'V293_ready_current_write',
                     'free Tint32 98%positive Msw=Some Mret', 'V293_cpu_release',
                     'forall i,(0<=i<4)%Z ->get Mret(98%positive,i)=None',
                     'get Mret(b,i)=get Msw(b,i)', 'exact Schedule', 'exact Prefix|exact Copy']:
            self.assertIn(term, body)
        self.assertIn('DPprogram(curs XPbody', body)

    def test_global_execution_original_simulation_and_bounded_control(self):
        src = (R / PROBE).read_text()
        body = theorem(src, 'DPactual_dispatch_and_resume')
        self.assertEqual(body.split('Proof.', 1)[0].count('ProgSim'), 1)
        for term in ['DPdispatch_storage CGpending', 'DPtasks,RPstate CEM cs ncs',
                     'RPfinal,RPreturned Mret cs ncs', 'V293_global_steps',
                     'DPprefix_global', 'RPfinite_switch_and_return',
                     'V293_exit_call_resume_progsim', 'HPschedule', 'SPterminal',
                     'get RPfinal OwnershipWaiting=Some(SKIP,(kenil,HPpending))',
                     'get(set RPenvs OwnershipReady emp)OwnershipWaiting=Some emp',
                     'OwnershipWaiting=Some(false,nil,cs)']:
            self.assertIn(term, body)
        self.assertIn('V293_csteps_global', theorem(src, 'DPprefix_global'))
        control = theorem(src, 'DPtarget_store_and_omission')
        for term in ['DPscheduled_canonical kstop', 'V293_store_readback',
                     'Some(Vptr OwnershipWaiting)', '~load(Tptr V293_tcb_type)CFfinal',
                     'exact XPomit_target_rejected']:
            self.assertIn(term, control)
        self.assertNotIn('ProgSim', control)

    def test_stable_compiles_trust_and_explicit_limits(self):
        self.assertEqual(sha(D / 'protocol.json'), (D / 'protocol.sha256').read_text().strip())
        stable = read('stable-compiles.json')
        roots = []
        for key, p in [('production', PROD), ('probe', PROBE)]:
            src = (R / p).read_text()
            self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
            row = read(stable[key] + '.json')
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['source_sha256'], row['initial_source_sha256'])
            self.assertEqual(row['source_sha256'], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        for label in stable['repeat_passes']:
            self.assertEqual(read(label + '.json')['exit'], 0)
        trust = read('trust.json')
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertEqual(len(roots), 9)
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']),
                             {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertEqual(read('build.json')['exit'], 0)
        doc = (R / 'audit/STAGE264_DISPATCH_RESUME_WITNESS.md').read_text()
        for term in ['不是 `GOOD_OS`', '不是 `WFInt`', 'IE=false', 'ADR-0010',
                     'K1–K4 未闭合', 'uCOS3 未开始', '未提交／推送', 'high=88',
                     '最终 caller 端点模拟', 'pending 在任务映射中已存在',
                     '完整内层 dispatch，不是完整 OSIntExit 调用', '切出任务仍挂起',
                     '不是一个完整 mutant 程序执行']:
            self.assertIn(term, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- dispatch-resume-witness-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
