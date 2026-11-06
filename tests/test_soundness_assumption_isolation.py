"""第342步证据一致性；定理与契约由Coq内核检查，不以文本匹配代替。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage342-soundness-assumption-isolation'
PS = ['certiucos/v293/proofs/V293CallSoundness.v',
      'certiucos/v293/proofs/V293Soundness.v',
      'certiucos/v293/proofs/V293TimeTaskSimulation.v']
Q = 'audit/probes/V293SoundnessBridgeProbe.v'
ALLOWED = {'Classical_Prop.classic',
           'FunctionalExtensionality.functional_extensionality_dep'}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class SoundnessAssumptionIsolationTests(unittest.TestCase):
    def test_prospective_single_bridge_factor(self):
        for n in ['protocol', 'regression-plan', 'cache-handling-protocol']:
            self.assertEqual((D / (n + '.sha256')).read_text().split(),
                             [sha(D / (n + '.json')), n + '.json'])
        p = read('protocol.json')
        self.assertTrue(p['prospective'])
        self.assertEqual(set(p['allowed']), ALLOWED)
        self.assertIn('replace only the rule-soundness bridge', p['ablation']['factor'])
        self.assertFalse(read('regression-plan.json')['gate_waived'])

    def test_real_old_negative_control_and_clean_full_chain(self):
        self.assertEqual(read('negative-control-01.json')['exit'], 0)
        ablation = read('ablation.json')
        self.assertEqual(len(ablation['old_rules']), 40)
        self.assertEqual(set(ablation['old_contaminated_rules']),
                         {'call_rule_sound', 'calle_rule_sound', 'calle_rule_lvar_sound'})
        self.assertEqual(len(ablation['new_bridge_roots']), 7)
        log = (D / 'negative-control-01.log').read_text()
        self.assertEqual(log.count('Eqdep.Eq_rect_eq.eq_rect_eq'), 4)
        old = json.loads((R / 'audit/logs/stage341-time-source-task-simulation/trust.json').read_text())
        self.assertFalse(old['passed'])
        self.assertIn('Eqdep.Eq_rect_eq.eq_rect_eq', old['unexpected_assumptions'])
        t = read('trust.json')
        self.assertTrue(t['passed'])
        for n in ['V293Soundness.V293_rule_sound',
                  'V293TimeTaskSimulation.V293_time_source_tasksim_sound',
                  'V293SoundnessBridgeProbe.V293_get_set_sim_checked']:
            self.assertLessEqual(set(read('assumptions-by-root.json')[n]), ALLOWED)

    def test_all_rules_and_exact_kernel_checked_contracts(self):
        p = (R / PS[1]).read_text().split('Local Hint Resolve', 1)[0]
        self.assertEqual(len(re.findall(r'eapply \w+\b', p)), 40)
        self.assertIn('InfRules Spec sd lasrt I r ri pre s post tid ->', p)
        self.assertIn('RuleSem Spec sd lasrt I r ri pre s post tid.', p)
        q = (R / Q).read_text()
        self.assertEqual(len(re.findall(r'^Theorem Contract_\d+ :', q, re.M)), 11)
        self.assertEqual(q.count('let T := type of '), 11)
        self.assertEqual(q.count('in exact T).'), 11)
        self.assertIn('exact V293_time_source_tasksim_sound.', q)
        self.assertIn('exact V293_get_set_sim_checked.', q)
        s = (R / PS[0]).read_text().split('Lemma V293_call_rule_sound', 1)[0]
        self.assertIn('revert ge le M v vl\' tl\'.', s)
        self.assertIn('induction Heval;', s)
        self.assertNotIn('inductions Heval', s)
        self.assertEqual(sha(R / 'framework/proof/fcallsound.v'),
                         read('call-proof-provenance.json')['original_sha256'])

    def test_actual_nonempty_task_client_not_assumed_execution(self):
        p = (R / PS[2]).read_text()
        s = p.split('Theorem V293_time_source_tasksim_sound :', 1)[1]
        pre = s.split('  TaskSim ', 1)[0]
        self.assertNotRegex(pre, r'\b(?:TaskSim|MethSimAsrt|MethSim|ltstep|lpstep|V293_local_steps|V293_global_steps)\b')
        self.assertIn('eapply V293_ApiMethSim', s)
        self.assertIn('eapply SmCTaskSim', s)
        q = (R / Q).read_text()
        for x in ['apply V293_OSSchedNew_WFFunEnv', 'TSnonempty_joint_entry',
                  'join Ml Ms (TRmemory t clock)', 'join Ol Os (TRabstract t clock)',
                  'satp (TSstate JGE Ms) Os (INV TSinv)',
                  'TaskSim (TSpc n,(TSapi,RAinternal,ip))']:
            self.assertIn(x, q)

    def test_repeat_compile_recursive_kernel_and_unchanged_allowlist(self):
        for label, p in zip(['calls', 'bridge', 'time', 'probe'], PS + [Q]):
            for i in [1, 2]:
                row = read(f'stable-{label}-{i}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / p))
                self.assertEqual(row['source_sha256'], sha(R / p))
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
        t = read('trust.json')
        roots = [Path(p).stem + '.' + n for p in PS + [Q] for n in
                 re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', (R / p).read_text(), re.M)]
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 22)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in t['commands']))
        self.assertEqual(set(t['allowed']), ALLOWED)
        self.assertLessEqual(set(t['assumptions']), ALLOWED)
        for p in PS:
            self.assertNotIn('Require Import CertiOS.audit.', (R / p).read_text())

    def test_frozen_inputs_and_append_only_registration(self):
        self.assertEqual([p for p, h in read('baseline.json').items()
                          if not (R / p).is_file() or sha(R / p) != h], [])
        old = json.loads((R / 'audit/logs/stage341-time-source-task-simulation/checkpoint-evidence-manifest.json').read_text())
        self.assertEqual([p for p, row in old.items()
                          if p not in {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject'}
                          and sha(R / p) != row['sha256']], [])
        prefix = (D / '_CoqProject.baseline').read_bytes() + ''.join(p + '\n' for p in PS).encode()
        self.assertTrue((R / '_CoqProject').read_bytes().startswith(prefix))
        for p in PS:
            self.assertEqual((R / '_CoqProject').read_text().splitlines().count(p), 1)
        for n in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / n).read_bytes().endswith((D / (n + '.baseline')).read_bytes()))

    def test_fixed_source_identity_and_bounded_claims(self):
        e = json.loads((R / 'audit/soundness-assumption-isolation-evidence-stage342.json').read_text())
        self.assertTrue(e['task_sim_accepted'])
        self.assertFalse(e['full_target_linked'])
        self.assertEqual(e['source_correspondence']['mode'], 'reuse_frozen_not_fresh_replay')
        self.assertEqual(e['source_identity_sha256'], '74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da')
        self.assertEqual(e['coverage_registration_status'], 'NOT_REGISTERED_IN_LEGACY_AGGREGATE')
        for p, h in e['inputs'].items():
            self.assertEqual(sha(R / p), h)
        doc = (R / 'audit/STAGE342_SOUNDNESS_ASSUMPTION_ISOLATION.md').read_text()
        for x in ['不是ProgSim', '不是GOOD_OS', '不是OSInit可达性', '不是经验证C前端',
                  'ADR0005', '两个CPU hook', 'K1–K4', 'uCOS3', '不是规范初始化表', '总目标保持active']:
            self.assertIn(x, doc)

    def test_adversarial_review_and_build(self):
        self.assertTrue(read('adversarial-review.json')['completed'])
        self.assertEqual(read('build.json')['exit'], 0)
        self.assertEqual(set(read('cache-restoration.json')['after']),
                         set(read('cache-baseline.json')))
        for p, row in read('cache-baseline.json').items():
            self.assertEqual(read('cache-restoration.json')['after'][p], row['sha256'])
