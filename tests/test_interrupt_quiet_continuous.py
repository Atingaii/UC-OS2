"""连续 quiet ISR 的结构与冻结身份；语义结论由 Coq 而非文本扫描给出。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage233-interrupt-quiet-continuous'
SOURCES = {'enter': 'certiucos/v293/proofs/V293OSIntEnterOpenExact.v',
           'continuous': 'certiucos/v293/proofs/V293InterruptQuietContinuous.v',
           'probe': 'audit/probes/V293InterruptQuietContinuousProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


class InterruptQuietContinuousTests(unittest.TestCase):
    def test_source_and_prospective_protocol(self):
        s = read('source-check.json')
        self.assertTrue(s['passed'])
        self.assertEqual([x['function']['name'] for x in s['functions']],
                         ['OSIntEnter', 'OSIntExit', 'OS_SchedNew', 'OS_Sched'])
        for x in s['functions']:
            self.assertEqual(hashlib.sha256((D / (x['function']['name'] + '.configured.c.txt')).read_bytes()).hexdigest(),
                             x['function']['preprocessed_definition_sha256'])
        for p, h in s['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
        self.assertEqual(s['previous_manifest_sha256'],
                         '87002351778ac7822f4ef8293c6be66da7411d75330083333f7873dd922fe643')
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])

    def test_compiles_and_recursive_trust(self):
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
        self.assertEqual(t['roots_printed'], 28)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(x['exit'] == 0 for x in t['commands']))
        self.assertTrue(set(t['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})

    def test_actual_enter_builders_and_exact_values(self):
        s = (R / SOURCES['enter']).read_text()
        for token in ['V293_quiet_exit_index', 'V293_interrupt_nest_after', 'p_local V293_shared_li t nil',
                      'V293_OSIntEnter_open_updates', 'V293_OSIntEnter_body', 'BuildPreI', 'BuildRetI',
                      'V293_OSIntEnter_open_contract', 'eapply call_rule', 'GoodFrm callerframe']:
            self.assertIn(token, s)
        external = s.split('Definition V293_enter_open_external', 1)[1].split('Lemma V293_enter_open_good', 1)[0]
        self.assertNotIn('Atrue', external)

    def test_continuous_original_wrapper_and_permissions(self):
        s = (R / SOURCES['continuous']).read_text()
        for token in ['V293_ready_irq_unit', 'WFFunEnv', 'WFIFun', 'V293_OSIntEnter_open_contract',
                      'V293_OSIntExit_all_exact_dynamic_contract', 'separate_rw2ro', 'combine_ro2rw_p1',
                      'V293_quiet_pair_half run ** callerframe', 'V293_OSIntExit_all_exact_quiet_call',
                      'V293_irq_source_wrapper enter exit id', 'eoi_ieoff_rule',
                      'V293_quiet_irq_snapshot_close', 'V293_irq_ready_exint',
                      'V293ReadyTaskInvariant.V293_ready_core', 'V293_storage_append']:
            self.assertIn(token, s)
        self.assertNotIn('Definition V293_irq_source_wrapper', s)
        main = s.split('Theorem V293_interrupt_quiet_continuous :', 1)[1].split('Proof.', 1)[0]
        self.assertNotIn('==>', main)
        self.assertIn('(run=1 ->nest<255)', main)

    def test_nonempty_typed_fixture_and_honest_limits(self):
        s = (R / SOURCES['probe']).read_text()
        for name in ['QCraw_heap', 'QCentry_nonempty', 'QCenvironment', 'QCactual_wrapper',
                     'QCreturn_builder_exists', 'QCdispatch_entry_not_quiet']:
            self.assertRegex(s, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        self.assertIn('V293_retained_arrays_ready', s)
        self.assertIn('JBmemory 1 Int.zero Int.zero', s)
        doc = (R / 'audit/STAGE233_INTERRUPT_QUIET_CONTINUOUS.md').read_text()
        for token in ['255', '强入口', '常 Aemp LocalInv', '不是初始化可达',
                      '不是两次完整执行', '不声称语义 TDD', 'WFInt', 'uCOS3 未开始']:
            self.assertIn(token, doc)
