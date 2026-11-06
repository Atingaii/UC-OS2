"""结构与来源回归；语义证明由独立 Coq/coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage242-bound-quiet-continuous'
SOURCES = {'entry': 'certiucos/v293/proofs/V293InterruptBoundQuietContinuous.v',
           'probe': 'audit/probes/V293InterruptBoundQuietContinuousProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


class BoundQuietContinuousTests(unittest.TestCase):
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
                         '52db18eccc9071a59888df8116f830240d6d865415ce89b9c2a7fcdf674f5f0f')
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])

    def test_real_continuous_calls_without_hoare_oracles(self):
        src = (R / SOURCES['entry']).read_text()
        for name in ['V293_interrupt_bound_quiet_exit',
                     'V293_interrupt_bound_quiet_pair',
                     'V293_interrupt_bound_quiet_continuous']:
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
                  'certiucos/v293/proofs/V293InterruptQuietContinuous.v']:
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), old[p])

    def test_permissions_and_assertion_only_closure(self):
        src = (R / SOURCES['entry']).read_text()
        for token in ['separate_rw2ro', 'combine_ro2rw_p1',
                      'V293_bound_dispatch_add_globals', 'V293_irq_bound_local_open',
                      'V293_irq_bound_local_close', 'V293_irq_ready_return_resources',
                      'V293_quiet_irq_snapshot_close']:
            self.assertIn(token, src)
        closure = src.split('Lemma V293_bound_quiet_snapshot_shared :')[1].split(
            'Theorem V293_interrupt_bound_quiet_continuous :')[0]
        self.assertNotIn('InfRules', closure)
        self.assertEqual(closure.count('Qed.'), 2)
        review = read('adversarial-review.json')
        for p, h in review['source_sha256'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)

    def test_nonempty_builder_return_and_limits(self):
        src = (R / SOURCES['probe']).read_text()
        for name in ['BQbuilders', 'BQentry_nonempty', 'BQenvironment',
                     'BQactual_wrapper', 'BQnonempty_actual_wrapper',
                     'BQreturn_literal', 'BQreturn_forget', 'BQreturned_nonempty',
                     'BQroom_is_necessary', 'BQquiet_is_not_all',
                     'BQother_bit_survives', 'BQruntime_unchanged']:
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        for token in ['QCstate M O|=BQentry /\\QCstate M O|=BQpre',
                      'BQreturned_state M O|=BQreturned /\\BQreturned_state M O|=BQret',
                      'WFFunEnv RDprogram BDspec', 'RDprogram 300%Z=XIprogram 300%Z']:
            self.assertIn(token, src)
        doc = (R / 'audit/STAGE242_BOUND_QUIET_CONTINUOUS.md').read_text()
        for token in ['不是所有 BuildintPre', '不是 `WFInt`', '不是 `GOOD_OS`',
                      '不是初始化可达', '不是两次完整执行', '旧423失败、1错误',
                      'uCOS3 未开始', 'Room', 'Quiet', 'all-clear']:
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
        self.assertEqual(t['roots_printed'], len(roots))
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in t['commands']))
        self.assertTrue(set(t['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
