"""changed 连续中断的身份和结构回归；Coq 独立负责语义检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage234-interrupt-changed-continuous'
SOURCES = {'continuous': 'certiucos/v293/proofs/V293InterruptChangedContinuous.v',
           'probe': 'audit/probes/V293InterruptChangedContinuousProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


class InterruptChangedContinuousTests(unittest.TestCase):
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
                         '622765146aaa1792d0bca29c0423e09fef91d2b4cbaac79d3d4a10b14123b964')
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
        self.assertEqual(t['roots_printed'], 20)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(x['exit'] == 0 for x in t['commands']))
        self.assertTrue(set(t['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})

    def test_current_pointer_typed_half_and_real_enter(self):
        s = (R / SOURCES['continuous']).read_text()
        for token in ['GV_separate_rw', 'V293_changed_current_combine', 'GV_combine_ro_p1',
                      'V293_global_cell_type', 'assert(tq=tp)by congruence',
                      'V293_changed_enter_split', 'V293_changed_enter_combine',
                      'V293_OSIntEnter_open_call', 'V293_interrupt_nest_after 1 0',
                      'V293_changed_irq_snapshot 0 aop ir si t',
                      'V293_changed_irq_snapshot 1 aop ir si t']:
            self.assertIn(token, s)
        combine = s.split('Lemma V293_changed_current_combine :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('CurTid t ** GV OSTCBCur@(Tptr tp)|-r->Vptr t', combine)
        self.assertNotIn('Atrue', s)

    def test_original_codec_wrapper_and_same_invariant(self):
        s = (R / SOURCES['continuous']).read_text()
        for token in ['eapply call_rule', 'GoodFrm callerframe', 'V293_changed_codec_roundtrip',
                      'V293_all_exact_dynamic_fpre', 'V293_all_exact_dynamic_fpost',
                      'V293_ready_dynamic_exit_inv', 'V293_exact_builder_post',
                      'V293_irq_source_wrapper enter exit id', 'eoi_ieoff_rule',
                      'V293_irq_clear_update', 'V293_irq_ready_exint',
                      '<||sched;;aop||>', 'SWINV Inv0 ** p_local V293_shared_li t nil']:
            self.assertIn(token, s)
        self.assertNotIn('Definition V293_irq_source_wrapper', s)
        main = s.split('Theorem V293_interrupt_changed_continuous :', 1)[1].split('Proof.', 1)[0]
        self.assertNotIn('==>', main)
        self.assertEqual(main.count('InfRules'), 1)
        self.assertIn('V293_changed_builder_valid tp lo hi nc 1 entries tasks t', main)

    def test_nonempty_typed_fixture_and_honest_limits(self):
        s = (R / SOURCES['probe']).read_text()
        for name in ['CCraw_good', 'CCraw_heap', 'CCentry_nonempty', 'CCenvironment',
                     'CCactual_wrapper', 'CCreturn_builder_exists']:
            self.assertRegex(s, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        for token in ['JBmemory 0 Int.zero Int.zero', 'GoodI RDinv', 'WFFunEnv RDprogram QCspec',
                      'WFIFun RDprogram QCspec', 'V293_interrupt_changed_continuous', 'apply RBvalid']:
            self.assertIn(token, s)
        doc = (R / 'audit/STAGE234_INTERRUPT_CHANGED_CONTINUOUS.md').read_text()
        for token in ['强入口', '常 Aemp LocalInv', '不是初始化可达',
                      '不是两次完整执行', '不声称语义 TDD', 'WFInt', 'uCOS3 未开始',
                      '指针类型', 'same 连续路径']:
            self.assertIn(token, doc)
