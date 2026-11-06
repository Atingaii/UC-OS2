"""same 连续中断的身份和结构回归；Coq 独立负责语义检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage235-interrupt-same-continuous'
SOURCES = {'continuous': 'certiucos/v293/proofs/V293InterruptSameContinuous.v',
           'probe': 'audit/probes/V293InterruptSameContinuousProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


class InterruptSameContinuousTests(unittest.TestCase):
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
                         '811be5f9b94be3a19a40849052b8720a26cb28cc57f650dcb08c0e30e8b34e44')
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
        self.assertEqual(t['roots_printed'], 31)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(x['exit'] == 0 for x in t['commands']))
        self.assertTrue(set(t['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})

    def test_fractional_resources_returned_and_real_enter(self):
        s = (R / SOURCES['continuous']).read_text()
        for token in ['V293_same_irq_read_borrow', 'V293_same_irq_read_reunite',
                      'V293_inputs_borrow', 'V293_array_borrow', 'separate_rw2ro',
                      'V293_inputs_reunite', 'V293_array_reunite', 'combine_ro2rw_p1',
                      'V293_same_irq_enter_split', 'V293_same_irq_enter_combine',
                      'V293_OSIntEnter_open_call', 'V293_interrupt_nest_after 1 0',
                      'V293_same_irq_snapshot 0 aop ir si t',
                      'V293_same_irq_snapshot 1 aop ir si t']:
            self.assertIn(token, s)
        self.assertIn('p_local V293_shared_li t nil ** (V293_same_irq_payload t', s)
        self.assertIn('CurTid t ** (V293_shared_fields t tasks events now', s)
        self.assertNotIn('Atrue', s)

    def test_original_codec_wrapper_and_same_invariant(self):
        s = (R / SOURCES['continuous']).read_text()
        for token in ['V293_same_exit_index_roundtrip',
                      'V293_OSIntExit_all_exact_dynamic_same_call',
                      'V293_all_exact_dynamic_fpre', 'V293_all_exact_dynamic_fpost',
                      'V293_ready_dynamic_exit_inv', 'V293_same_irq_resources_close',
                      'V293_irq_source_wrapper enter exit id', 'eoi_ieoff_rule',
                      'V293_irq_clear_update', 'V293_irq_ready_exint',
                      'V293_retained_arrays_ready', 'V293_irq_ready_open_close']:
            self.assertIn(token, s)
        self.assertNotIn('Definition V293_irq_source_wrapper', s)
        self.assertNotIn('<||sched;;aop||>', s)
        main = s.split('Theorem V293_interrupt_same_continuous :', 1)[1].split('Proof.', 1)[0]
        self.assertNotIn('==>', main)
        self.assertEqual(main.count('InfRules'), 1)
        self.assertIn('V293_same_exit_valid(i::si)', main)

    def test_nonempty_typed_fixture_and_honest_limits(self):
        s = (R / SOURCES['probe']).read_text()
        for name in ['SCraw_good', 'SCraw_heap', 'SCentry_nonempty', 'SCenvironment',
                     'SCactual_wrapper', 'SCreturn_builder_exists']:
            self.assertRegex(s, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        for token in ['SCmemory 0 Int.zero Int.zero', 'GoodI RDinv', 'WFFunEnv RDprogram QCspec',
                      'WFIFun RDprogram QCspec', 'V293_interrupt_same_continuous', 'exact SCvalid',
                      'V293_byteval 4', 'Vptr OwnershipReady', 'GV_separate_rw']:
            self.assertIn(token, s)
        controls = s.split('Definition SCcontrols', 1)[1].split('Definition SCinner', 1)[0]
        self.assertNotIn('OwnershipWaiting', controls)
        doc = (R / 'audit/STAGE235_INTERRUPT_SAME_CONTINUOUS.md').read_text()
        for token in ['强入口', '常 Aemp LocalInv', '不是初始化可达',
                      '不是两次完整执行', '不声称语义 TDD', 'WFInt', 'uCOS3 未开始',
                      '指针类型', '全输入覆盖']:
            self.assertIn(token, doc)
