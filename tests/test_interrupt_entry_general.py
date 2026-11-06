"""入口要求消融与证据身份检查；语义由 Coq/独立 coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage237-interrupt-entry-general'
SOURCES = {'entry': 'certiucos/v293/proofs/V293InterruptEntryGeneral.v',
           'probe': 'audit/probes/V293InterruptEntryGeneralProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


class InterruptEntryGeneralTests(unittest.TestCase):
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
                         '2624a4f379930396b4b4b5891dc7704823cddedd008aeddc91ca298578749b03')
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])

    def test_no_clear_requirement_or_middle_oracle(self):
        src = (R / SOURCES['entry']).read_text()
        main = src.split('Theorem V293_interrupt_entry_general :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('Some pre=BuildintPre', main)
        self.assertIn('(pre ** globals)', main)
        self.assertEqual(main.count('InfRules'), 1)
        self.assertNotIn('==>', main)
        for token in ['forall j', 'run=1', 'nest=0', 'nest<255', 'quiet_exit_valid']:
            self.assertNotIn(token, main)
        self.assertNotIn('Atrue', src)
        self.assertIn('apply V293_irq_entry_builder_open', src)
        self.assertIn('apply eoi_ieoff_rule', src)
        self.assertIn('V293_OSIntEnter_open_call', src)
        self.assertIn('(isrupd(isrupd ir i true)i false)(i::si)nil t', src)
        self.assertNotIn('rewrite V293_irq_clear_update', src)

    def test_depth_relation_limitation_is_not_blanket_rejection(self):
        src = (R / SOURCES['entry']).read_text()
        theorem = src.split('Theorem V293_irq_inv_depth_relation_empty_at_clear :', 1)[1]
        for token in ['assertion.inv_isr_prop p', 'depth(getmem st)=length(get_is_s st)',
                      'get_isr_s st=empisr', 'Reset st nil', 'Reset st [0]']:
            self.assertIn(token, theorem)
        probe = (R / SOURCES['probe']).read_text()
        self.assertIn('EGheap_only_bound_closure', probe)
        self.assertIn('EGbuilder_allows_depth_mismatch', probe)
        self.assertIn('EGsnapshot_load_nest', probe)
        self.assertIn('eapply V293_mapsto_load', probe)
        baseline = read('baseline.json')['files']
        for p in ['framework/logic/assertion.v', 'framework/logic/inferules.v',
                  'certiucos/v293/proofs/V293ReadyStorageInvariant.v']:
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), baseline[p])

    def test_real_nonempty_builder_and_same_environment(self):
        src = (R / SOURCES['probe']).read_text()
        for name in ['EGbuilder', 'EGsnapshot_nonempty', 'EGsnapshot_to_builder', 'EGentry_nonempty',
                     'EGenvironment', 'EGactual_prefix', 'EGnot_all_clear', 'EGother_active_survives',
                     'EGEOI_exact', 'EGbuilder_allows_depth_mismatch']:
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        for token in ['JBmemory 1 Int.zero Int.zero', 'pose proof QCraw_heap', 'exact ECenvironment',
                      'V293_interrupt_entry_general', 'isrupd EGactive 0 false 1=true']:
            self.assertIn(token, src)
        doc = (R / 'audit/STAGE237_INTERRUPT_ENTRY_GENERAL.md').read_text()
        for token in ['显式附加 frame', '不是 `WFInt`', '常 Aemp LocalInv', '不是初始化可达',
                      '不是两次完整执行', '不否定框架 soundness', '旧423失败、1错误', 'uCOS3 未开始']:
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
        self.assertEqual(t['roots_printed'], 16)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(x['exit'] == 0 for x in t['commands']))
        self.assertTrue(set(t['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
