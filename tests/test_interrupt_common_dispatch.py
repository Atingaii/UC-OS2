"""统一 changed/same 抽象入口的结构回归；语义结论以 Coq 检查为准。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage245-common-dispatch-spec'
SOURCES = {'common': 'certiucos/v293/proofs/V293InterruptCommonDispatch.v',
           'probe': 'audit/probes/V293InterruptCommonDispatchProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class CommonDispatchTests(unittest.TestCase):
    def test_fixed_source_and_prospective_protocol(self):
        s = read('source-check.json')
        self.assertTrue(s['passed'])
        self.assertEqual([x['function']['name'] for x in s['functions']],
                         ['OSIntEnter', 'OSIntExit', 'OS_SchedNew', 'OS_Sched'])
        for p, h in s['files'].items():
            self.assertEqual(sha(R / p), h)
        self.assertEqual(s['previous_manifest_sha256'],
                         '6e23b5603f1a3903326789a59b0fd09dc28722a68abca5024896c10cb24549f6')
        self.assertEqual(sha(D / 'protocol.json'), (D / 'protocol.sha256').read_text().split()[0])
        for x in s['functions']:
            self.assertEqual(sha(D / (x['function']['name'] + '.configured.c.txt')),
                             x['function']['preprocessed_definition_sha256'])
        old = read('baseline.json')['files']
        for p in ['framework/logic/inferules.v',
                  'certiucos/v293/proofs/V293InterruptBoundDispatchContinuous.v',
                  'certiucos/v293/proofs/V293OSIntExitBoundDynamic.v',
                  'audit/probes/V293InterruptBoundDispatchContinuousProbe.v']:
            self.assertEqual(sha(R / p), old[p])

    def test_native_schedule_and_branch_local_validity(self):
        src = (R / SOURCES['common']).read_text()
        reduce = src.split('Lemma V293_same_schedule_reduce :', 1)[1].split('Qed.', 1)[0]
        for token in ['V293_current_task tasks t nc', 'V293_same_resources_sched',
                      'absinfer_sched\'', 'absinfer_seq\'', 'absinfer_seq_end\'']:
            self.assertIn(token, reduce)
        self.assertNotIn('spec_choice', src)
        entry = src.split('Definition V293_common_dispatch_entry', 1)[1].split('Theorem', 1)[0]
        self.assertIn('V293_changed_builder_valid', entry.split('\\\\//')[0])
        self.assertIn('V293_same_exit_valid', entry.split('\\\\//')[1])
        self.assertIn('V293_current_task tasks t nc', entry.split('\\\\//')[1])
        wrapper = src.split('Theorem V293_interrupt_common_dispatch_continuous :', 1)[1]
        self.assertIn('apply disj_rule;apply pure_split_rule', wrapper)
        self.assertIn('V293_interrupt_common_same_continuous', wrapper)
        builder = src.split('Theorem V293_common_dispatch_BuildintPre :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('intspec 0=Some(sched;;spec_done None)', builder)
        self.assertIn('V293_common_dispatch_entry 0 si t ==>pre', builder)
        self.assertNotIn('InfRules', builder)

    def test_actual_builders_typed_nonempty_and_common_wrappers(self):
        src = (R / SOURCES['probe']).read_text()
        builders = src.split('Theorem CDbuilders :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(builders.count('BuildintPre 0 BCintspec'), 2)
        self.assertEqual(builders.count('BuildintRet 0 BCintspec'), 2)
        for path, state, pre in [('changed', 'CCstate', 'BCpre'), ('same', 'CDstate', 'CDpre')]:
            nonempty = src.split('Theorem CD' + path + '_nonempty :', 1)[1].split('Qed.', 1)[0]
            self.assertIn(state + ' M O|=CD' + path, nonempty)
            self.assertIn(state + ' M O|=' + pre, nonempty)
            self.assertIn('join M Mf', nonempty)
            self.assertIn('join O Of', nonempty)
            wrapper = src.split('Theorem CD' + path + '_wrapper :', 1)[1].split('Qed.', 1)[0]
            self.assertIn('InfRules BDspec V293_scheduler LDli RDinv', wrapper)
            self.assertIn('V293_irq_source_wrapper 301%Z 300%Z Int.zero', wrapper)
            self.assertIn('V293_interrupt_common_dispatch_continuous', wrapper)
        self.assertIn('Proof. exact BCenvironment. Qed.', src)

    def test_single_factor_current_and_bounded_claims(self):
        src = (R / SOURCES['probe']).read_text()
        for token in ['Theorem CDcurrent_ablation', '~sched_self',
                      'Theorem CDcurrent_only', 'key<>curtid',
                      'Theorem CDsame_abstract_steps', 'spec_seq_step2', 'spec_sched_step', 'spec_seq_step1']:
            self.assertIn(token, src)
        a = read('scheduler-ablation.json')
        self.assertFalse(a['two_executions'])
        self.assertEqual(a['proof_source_sha256'], sha(R / SOURCES['probe']))
        self.assertEqual(read(a['compile'] + '.json')['exit'], 0)
        for p, h in read('adversarial-review.json')['source_sha256'].items():
            self.assertEqual(sha(R / p), h)
        doc = (R / 'audit/STAGE245_COMMON_DISPATCH_SPEC.md').read_text()
        for text in ['显式增加', '单向蕴含', '不是所有 BuildintPre', '不是 `WFInt`',
                     '不是 `GOOD_OS`', '不是初始化可达', '不是两次完整执行',
                     'quiet 尚未合并', 'uCOS3 未开始', '旧423失败、1错误']:
            self.assertIn(text, doc)

    def test_independent_roots_and_stable_sources(self):
        roots = []
        for kind, p in SOURCES.items():
            src = (R / p).read_text()
            label = read('stable-compiles.json')[kind]
            row = read(label + '.json')
            self.assertEqual(row['exit'], 0)
            self.assertEqual(sha(R / p), row['initial_source_sha256'])
            self.assertEqual(sha(R / p), row['source_sha256'])
            self.assertEqual(sha(R / p), sha(D / (label + '.v.snapshot.txt')))
            self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
            if kind != 'probe':
                self.assertNotIn('CertiOS.audit.', src)
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', src, re.M)]
        t = read('trust.json')
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 20)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in t['commands']))
        self.assertTrue(set(t['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
