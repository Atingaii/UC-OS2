"""结构与来源回归；语义验证由独立 Coq/coqchk 完成。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage243-bound-dispatch-continuous'
SOURCES = {'entry': 'certiucos/v293/proofs/V293InterruptBoundDispatchContinuous.v',
           'probe': 'audit/probes/V293InterruptBoundDispatchContinuousProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


class BoundDispatchContinuousTests(unittest.TestCase):
    def test_fixed_source_and_protocol(self):
        s = read('source-check.json')
        self.assertTrue(s['passed'])
        self.assertEqual([x['function']['name'] for x in s['functions']],
                         ['OSIntEnter', 'OSIntExit', 'OS_SchedNew', 'OS_Sched'])
        for p, h in s['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
        for x in s['functions']:
            p = D / (x['function']['name'] + '.configured.c.txt')
            self.assertEqual(hashlib.sha256(p.read_bytes()).hexdigest(),
                             x['function']['preprocessed_definition_sha256'])
        self.assertEqual(s['previous_manifest_sha256'],
                         'de31c47b82b2d6a72e0f8dd98a1dd18c0341467ce9180b65d0c7c9a5d7a5181f')
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])

    def test_actual_calls_without_hoare_oracles(self):
        src = (R / SOURCES['entry']).read_text()
        for path in ['changed', 'same']:
            for suffix in ['enter', 'exit', 'continuous']:
                name = 'V293_interrupt_bound_' + path + '_' + suffix
                header = src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]
                self.assertEqual(header.count('InfRules'), 1)
                self.assertNotIn('==>', header)
                self.assertNotIn('CurLINV', header)
        for token in ['apply V293_OSIntExit_bound_dynamic_call',
                      'V293_OSIntEnter_bound_call', 'apply eoi_ieoff_rule',
                      'apply iret_rule', 'BuildintRet', 'V293_irq_source_wrapper',
                      'V293_irq_bound_li running nesting lock brun bn bl']:
            self.assertIn(token, src)
        old = read('baseline.json')['files']
        for p in ['framework/logic/inferules.v',
                  'certiucos/v293/proofs/V293InterruptBindings.v',
                  'certiucos/v293/proofs/V293OSIntExitBoundDynamic.v',
                  'certiucos/v293/proofs/V293InterruptChangedContinuous.v',
                  'certiucos/v293/proofs/V293InterruptSameContinuous.v']:
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), old[p])

    def test_assertion_closure_and_import_ablation(self):
        src = (R / SOURCES['entry']).read_text()
        for token in ['V293_changed_enter_split', 'V293_changed_enter_combine',
                      'V293_irq_bound_local_close', 'V293_irq_bound_local_open',
                      'V293_same_irq_resources_close', 'V293_bound_irq_closed_pack',
                      'V293_bound_dispatch_add_globals']:
            self.assertIn(token, src)
        for name in ['V293_enter_open_to_bound', 'V293_enter_bound_to_open',
                     'V293_bound_changed_post', 'V293_same_external_bound_pack',
                     'V293_same_external_bound_open', 'V293_bound_same_post']:
            body = src.split('Lemma ' + name + ' :', 1)[1].split('Qed.', 1)[0]
            self.assertNotIn('InfRules', body)
        review = read('adversarial-review.json')
        for p, h in review['source_sha256'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
        a = read('import-ablation.json')
        bodies = []
        for phase in ['before', 'after']:
            label = a[phase + '_compile']
            row = read(label + '.json')
            raw = (D / (label + '.v.snapshot.txt')).read_bytes()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(hashlib.sha256(raw).hexdigest(), a[phase + '_source_sha256'])
            bodies.append(b''.join(x for x in raw.splitlines(keepends=True)
                                   if not x.startswith(b'Require Import ')))
        self.assertEqual(bodies[0], bodies[1])
        self.assertEqual(len(a['removed_imports']), 10)

    def test_typed_entries_builders_and_limits(self):
        src = (R / SOURCES['probe']).read_text()
        for name in ['BCbuilders', 'BSbuilders', 'BCtyped_entry_nonempty',
                     'BStyped_entry_nonempty', 'BCenvironment',
                     'BCactual_wrapper', 'BSactual_wrapper',
                     'BCnonempty_actual_wrapper', 'BSnonempty_actual_wrapper',
                     'BCreturn_literal', 'BSreturn_literal',
                     'BCreturn_forget', 'BSreturn_forget', 'BCreturn_nonempty',
                     'BCabstract_entry_differs', 'BCruntime_unchanged']:
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        for token in ['WFFunEnv RDprogram BDspec', 'RDprogram 300%Z=XIprogram 300%Z',
                      'BCintspec 0<>QCintspec 0', 'exact CCentry_nonempty',
                      'exact SCentry_nonempty']:
            self.assertIn(token, src)
        doc = (R / 'audit/STAGE243_BOUND_DISPATCH_CONTINUOUS.md').read_text()
        for token in ['不是所有 BuildintPre', '不是 `WFInt`', '不是 `GOOD_OS`',
                      '不是初始化可达', '不是两次完整执行', '旧423失败、1错误',
                      'uCOS3 未开始', 'all-clear', '没有另证 Ready 返回侧',
                      '同一状态成立', '不是运行时性能实验']:
            self.assertIn(token, doc)

    def test_independent_roots_and_stable_sources(self):
        roots = []
        for kind, p in SOURCES.items():
            src = (R / p).read_text()
            label = read('stable-compiles.json')[kind]
            row = read(label + '.json')
            h = hashlib.sha256((R / p).read_bytes()).hexdigest()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(h, row['initial_source_sha256'])
            self.assertEqual(h, row['source_sha256'])
            self.assertEqual(h, hashlib.sha256((D / (label + '.v.snapshot.txt')).read_bytes()).hexdigest())
            self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
            if kind != 'probe':
                self.assertNotIn('CertiOS.audit.', src)
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', src, re.M)]
        t = read('trust.json')
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 32)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in t['commands']))
        self.assertTrue(set(t['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
