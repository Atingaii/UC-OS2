"""实际入口控制值连接的结构/身份回归；语义由独立 Coq 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage236-interrupt-entry-control'
SOURCES = {'entry': 'certiucos/v293/proofs/V293InterruptEntryControl.v',
           'probe': 'audit/probes/V293InterruptEntryControlProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


class InterruptEntryControlTests(unittest.TestCase):
    def test_source_and_prospective_protocol(self):
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
                         '05515d21c188828daa88fed28d6d0b572b77c2440cca7087e8206cf9fb1d4f61')
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
        self.assertEqual(t['roots_printed'], 13)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(x['exit'] == 0 for x in t['commands']))
        self.assertTrue(set(t['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})

    def test_actual_builder_and_no_control_initialization_oracle(self):
        s = (R / SOURCES['entry']).read_text()
        for token in ['V293_irq_ready_builder_resources', 'V293_irq_entry_controls_open',
                      'V293_storage_byte_open', 'V293_storage_split',
                      'V293_local_witness_identity', 'V293_irq_entry_builder_open']:
            self.assertIn(token, s)
        main = s.split('Theorem V293_interrupt_entry_control :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('Some pre=BuildintPre', main)
        self.assertIn('(pre ** globals)', main)
        self.assertNotIn('==>', main)
        self.assertEqual(main.count('InfRules'), 1)
        for token in ['run=1', 'nest=0', 'nest<255', 'quiet_exit_valid']:
            self.assertNotIn(token, main)
        self.assertNotIn('Atrue', s)

    def test_exact_prefix_and_old_new_relation(self):
        s = (R / SOURCES['entry']).read_text()
        for token in ['eoi_ieoff_rule', 'V293_irq_clear_update', 'V293_OSIntEnter_open_call',
                      'sseq(sprim(eoi id))(scall enter nil)',
                      'EX run,EX oldnest,EX locked',
                      'snapshot run(V293_interrupt_nest_after run oldnest)locked',
                      'V293_quiet_irq_kept_good', 'V293_quiet_irq_physical_good']:
            self.assertIn(token, s)
        self.assertNotIn('V293_irq_ready_exint', s)

    def test_nonempty_actual_builder_and_honest_limits(self):
        s = (R / SOURCES['probe']).read_text()
        for name in ['ECbuilder', 'ECsnapshot_to_builder', 'ECentry_nonempty', 'ECenvironment',
                     'ECactual_prefix', 'ECincrement', 'ECsaturated', 'ECnotrunning', 'ECnot_zero_initial']:
            self.assertRegex(s, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        for token in ['JBmemory 1 Int.zero Int.zero', 'QCentry_nonempty',
                      'WFFunEnv RDprogram QCspec', 'WFIFun RDprogram QCspec',
                      'V293_interrupt_entry_control', 'getinv(RDinv 0)',
                      'V293_interrupt_nest_after 1 255=255', 'V293_interrupt_nest_after 0 254=254']:
            self.assertIn(token, s)
        doc = (R / 'audit/STAGE236_INTERRUPT_ENTRY_CONTROL.md').read_text()
        for token in ['显式附加 frame', '不是 `WFInt`', '常 Aemp LocalInv', '不是初始化可达',
                      '不是两次完整执行', 'uCOS3 未开始', '423失败、1错误']:
            self.assertIn(token, doc)
