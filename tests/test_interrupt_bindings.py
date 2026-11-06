"""地址绑定单因素对照与证据身份检查；语义由 Coq/独立 coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage238-interrupt-bindings'
SOURCES = {'entry': 'certiucos/v293/proofs/V293InterruptBindings.v',
           'probe': 'audit/probes/V293InterruptBindingsProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


class InterruptBindingsTests(unittest.TestCase):
    def test_source_identity_and_prospective_protocol(self):
        s = read('source-check.json')
        self.assertTrue(s['passed'])
        self.assertEqual([x['function']['name'] for x in s['functions']],
                         ['OSIntEnter', 'OSIntExit', 'OS_SchedNew', 'OS_Sched'])
        for x in s['functions']:
            p = D / (x['function']['name'] + '.configured.c.txt')
            self.assertEqual(hashlib.sha256(p.read_bytes()).hexdigest(),
                             x['function']['preprocessed_definition_sha256'])
        for p, h in s['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
        self.assertEqual(s['previous_manifest_sha256'],
                         'c5c2a6eacfa33dbb6b192c08af234c58d0fa18f94bdb83cc3e265b24e29511bd')
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])

    def test_bound_builder_needs_no_external_globals_or_middle_oracle(self):
        src = (R / SOURCES['entry']).read_text()
        main = src.split('Theorem V293_interrupt_bound_entry :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('Some pre=BuildintPre', main)
        self.assertIn('InfRules Spec sd li Inv0 r ri pre', main)
        self.assertNotIn('(pre ** globals)', main)
        self.assertEqual(main.count('InfRules'), 1)
        for token in ['==>', 'forall j', 'run=1', 'nest=0', 'nest<255', 'quiet_exit_valid']:
            self.assertNotIn(token, main)
        for token in ['apply V293_irq_entry_builder_open', 'apply eoi_ieoff_rule',
                      'V293_OSIntEnter_bound_call', '(isrupd(isrupd ir i true)i false)(i::si)nil t']:
            self.assertIn(token, src)
        external = src.split('Definition V293_enter_bound_external ', 1)[1].split('Lemma ', 1)[0]
        self.assertIn('p_local li t nil', external)
        self.assertNotIn('globals', external)

    def test_bound_local_invariant_and_original_body(self):
        src = (R / SOURCES['entry']).read_text()
        for name in ['V293_irq_bound_empty', 'V293_irq_bound_good', 'V293_irq_bound_GoodI',
                     'V293_OSIntEnter_bound_body', 'V293_OSIntEnter_bound_contract',
                     'V293_OSIntEnter_bound_WFFunEnv', 'V293_OSIntEnter_bound_WFIFun']:
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        self.assertIn('GoodI Inv0 sd V293_shared_li ->GoodI Inv0 sd V293_irq_bound_li', src)
        self.assertIn('apply V293_OSIntEnter_updates_hoare', src)
        self.assertIn('Some pre=BuildPreI', src)
        self.assertIn('Some post=BuildRetI', src)
        baseline = read('baseline.json')['files']
        for p in ['framework/logic/assertion.v', 'framework/logic/inferules.v',
                  'certiucos/v293/proofs/V293ReadyStorageInvariant.v',
                  'certiucos/v293/code/V293OSIntEnter.v']:
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), baseline[p])

    def test_same_heap_single_changed_binding_is_not_execution_comparison(self):
        src = (R / SOURCES['probe']).read_text()
        for name in ['EBbuilder', 'EBentry_nonempty', 'EBenvironment', 'EBsame_Enter_body',
                     'EBactual_prefix', 'EBweak_builder_stable', 'EBbad_weak_builder_nonempty',
                     'EBbad_bound_builder_rejected', 'EBsingle_changed_binding']:
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        for token in ['JBmemory 1 Int.zero Int.zero', 'set JBge 112%Z(100%positive,Tint8)',
                      'EGstate M O|=EBpre /\\ EBbadstate M O|=EGpre',
                      'EBbadstate M O|=EBpre', 'V293_interrupt_bound_entry',
                      '(false,[0;1],nil)', 'EBprogram 301%Z=RDprogram 301%Z']:
            self.assertIn(token, src)
        doc = (R / 'audit/STAGE238_INTERRUPT_BINDINGS.md').read_text()
        for token in ['不是两次完整执行', '不是 `WFInt`', '不是初始化可达',
                      '不替换或改写旧三函数环境', '不是 `GOOD_OS`', '旧423失败、1错误',
                      'uCOS3 未开始', '不说明它的逻辑内容等于 Aemp']:
            self.assertIn(token, doc)

    def test_compilation_and_recursive_trust(self):
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
        self.assertEqual(t['roots_printed'], 35)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(x['exit'] == 0 for x in t['commands']))
        self.assertTrue(set(t['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
