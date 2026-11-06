"""第341步连接与边界检查；数学结论由Coq内核检查，不由字符串检查代替。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage341-time-source-task-simulation'
P = 'certiucos/v293/proofs/V293TimeSourceTaskSim.v'
Q = 'audit/probes/V293TimeSourceTaskSimProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())
part = lambda s, n: s.split(n + ' :', 1)[1].split('\nQed.', 1)[0]


class TimeSourceTaskSimTests(unittest.TestCase):
    def test_prospective_single_name_factor(self):
        self.assertEqual((D / 'protocol.sha256').read_text().split(),
                         [sha(D / 'protocol.json'), 'protocol.json'])
        p = read('protocol.json')
        self.assertTrue(p['prospective'])
        self.assertIn('remove only time global-name binding', p['ablation']['factor'])
        self.assertIn('entry resource gate only', p['ablation']['scope'])

    def test_source_bodies_to_strong_WFAPI(self):
        s = part((R / P).read_text(), 'Theorem V293_source_time_ready_WFAPI')
        for x in ['WFAPI (V293_source_time_program', 'V293_source_time_get_exact',
                  'V293_source_time_set_exact', 'V293_time_ready_inv',
                  'V293_TimeGet_ready_api_contract', 'V293_TimeSet_ready_api_contract']:
            self.assertIn(x, s)
        self.assertNotIn('V293_time_shared_inv', s)

    def test_original_soundness_to_universal_simulation(self):
        p = (R / P).read_text()
        method = part(p, 'Theorem V293_source_time_ready_method')
        for x in ['MethSimAsrt', 'MethSim_to_Methsim\'', 'apply RuleSound',
                  'V293_time_ready_names_good']:
            self.assertIn(x, method)
        s = part(p, 'Theorem V293_source_time_ready_tasksim')
        pre, conclusion = s.split('  TaskSim ', 1)
        self.assertNotRegex(pre, r'\b(?:TaskSim|MethSimAsrt|MethSim|ltstep|lpstep|V293_local_steps|V293_global_steps)\b')
        for x in ['eapply SmCTaskSim', 'eapply ApiMethSim', "apply bpr'_to_bpr",
                  'V293_source_time_ready_WFAPI', 'InitTaskSt', 'WFFuncsSim']:
            self.assertIn(x, s)
        self.assertNotIn('exists', conclusion.split('Proof.', 1)[0])

    def test_concrete_internal_and_joint_nonempty_entry(self):
        q = (R / Q).read_text()
        self.assertIn('apply V293_OSSchedNew_WFFunEnv', q)
        s = part(q, 'Theorem TSget_set_client')
        for x in ['forall ip intspec t clock n', 'no_call_api_ipu ip TSapi',
                  'EqDomInt ip intspec', 'join Ml Ms (TRmemory t clock)',
                  'join Ol Os (TRabstract t clock)', 'INV TSinv',
                  'TaskSim (TSpc n,(TSapi,RAinternal,ip))', 'exact TSinternal_checked']:
            self.assertIn(x, s)
        pre = s.split('  exists Ml Ms Ol Os,', 1)[0]
        self.assertNotRegex(pre, r'\b(?:WFFuncsSim|InitTaskSt|TaskSim|satp|ltstep)\b')
        self.assertIn('Jcore_and_current', part(q, 'Theorem TSnonempty_joint_entry'))

    def test_single_factor_preserves_heap_abstract_and_invariant(self):
        s = part((R / Q).read_text(), 'Theorem TSname_single_factor')
        for x in ['join Ml Ms (TRmemory t clock)', 'join Ol Os (TRabstract t clock)',
                  'satp (TSstate JGE Ms) Os (INV TSinv)',
                  'satp (TSstate (del JGE 1001%Z) Ms) Os (INV TSinv)',
                  'x<>1001%Z', '~InitTaskSt RAli t', 'TSmissing_name_entry']:
            self.assertIn(x, s)
        self.assertNotIn('~TaskSim', s)

    def test_compiled_twice_recursive_trust(self):
        for label, path in [('proof', P), ('probe', Q)]:
            for i in [1, 2]:
                row = read(f'stable-{label}-{i}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / path))
                self.assertEqual(row['source_sha256'], sha(R / path))
        t = read('trust.json')
        roots = [Path(p).stem + '.' + n for p in [P, Q] for n in
                 re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', (R / p).read_text(), re.M)]
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 13)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in t['commands']))
        self.assertLessEqual(set(t['assumptions']),
                             {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        for p in [P, Q]:
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
        self.assertNotIn('Require Import CertiOS.audit.', (R / P).read_text())

    def test_old_inputs_and_append_only_registration(self):
        self.assertEqual([p for p, h in read('baseline.json').items()
                          if not (R / p).is_file() or sha(R / p) != h], [])
        old = json.loads((R / 'audit/logs/stage340-time-continuous-global/checkpoint-evidence-manifest.json').read_text())
        self.assertEqual([p for p, row in old.items()
                          if p not in {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject'}
                          and sha(R / p) != row['sha256']], [])
        project = (R / '_CoqProject').read_bytes()
        prefix = (D / '_CoqProject.baseline').read_bytes() + (P + '\n').encode()
        self.assertTrue(project.startswith(prefix))
        self.assertEqual(project.decode().splitlines().count(P), 1)
        for n in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / n).read_bytes().endswith((D / (n + '.baseline')).read_bytes()))

    def test_bounded_claims_no_whole_kernel_credit(self):
        e = json.loads((R / 'audit/time-source-task-sim-evidence-stage341.json').read_text())
        self.assertFalse(e['full_target_linked'])
        self.assertEqual(e['source_correspondence']['mode'], 'reuse_frozen_not_fresh_replay')
        self.assertEqual(e['coverage_registration_status'], 'NOT_REGISTERED_IN_LEGACY_AGGREGATE')
        for p, h in e['inputs'].items():
            self.assertEqual(sha(R / p), h)
        doc = (R / 'audit/STAGE341_TIME_SOURCE_TASK_SIM.md').read_text()
        for x in ['TaskSim', '不是ProgSim', '不是GOOD_OS', '不是OSInit可达性',
                  '不是经验证C前端', 'ADR0005', '两个CPU hook', 'K1–K4', 'uCOS3',
                  '不是规范初始化表', '入口早拒绝', '总目标保持active']:
            self.assertIn(x, doc)
        self.assertTrue(read('adversarial-review.json')['completed'])
