"""中断两端的结构回归；语义结论来自 Coq，不声称语义 TDD。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage221-interrupt-builder-boundary'
SOURCES = {'internal': 'certiucos/v293/proofs/V293InterruptReadyBoundary.v',
           'probe': 'audit/probes/V293InterruptReadyBoundaryProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return re.split(r'\b' + re.escape(name) + r'\s*:', src, maxsplit=1)[1].split('Proof.', 1)[0]


class InterruptReadyBoundaryTests(unittest.TestCase):
    def test_source_identity_and_prospective_protocol(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        self.assertEqual([x['function']['name'] for x in source['functions']],
                         ['OSIntEnter', 'OSIntExit', 'OS_SchedNew', 'OS_Sched'])
        for row in source['functions']:
            p = D / (row['function']['name'] + '.configured.c.txt')
            self.assertEqual(hashlib.sha256(p.read_bytes()).hexdigest(),
                             row['function']['preprocessed_definition_sha256'])
        for p, h in source['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])

    def test_actual_entry_builder_and_eoi_rule(self):
        src = (R / SOURCES['internal']).read_text()
        entry = statement(src, 'V293_irq_ready_eoi')
        self.assertIn('Some pre=BuildintPre', entry)
        self.assertEqual(entry.count('InfRules'), 1)
        self.assertIn('(forall j,ir j=false)', entry)
        self.assertIn('Z.of_nat INUM', entry)
        self.assertIn('V293_irq_ready_builder_resources', src)
        self.assertIn('apply eoi_ieoff_rule', src)
        self.assertIn('unfold ipreasrt\',invlth_noisr', src)
        self.assertIn('V293_ready_storage_noisr_core', src)
        self.assertIn('starinv_noisr includes its low index', src)
        self.assertIn('V293_ready_storage_switch_close', src)

    def test_actual_return_builder_not_whole_isr_oracle(self):
        src = (R / SOURCES['internal']).read_text()
        tail = statement(src, 'V293_irq_ready_exint')
        self.assertIn('Some ret=BuildintRet', tail)
        self.assertEqual(tail.count('InfRules'), 1)
        self.assertIn('(sprim exint)Afalse', tail)
        self.assertIn('apply iret_rule', src)
        self.assertIn('V293_irq_ready_return_resources', src)
        self.assertIn('IRINV Inv0', src)
        self.assertIn('p_local V293_shared_li t lg', src)
        self.assertNotIn('CertiOS.audit.', src)
        self.assertNotIn('WFInt', src)
        self.assertNotIn('GOOD_OS', src)

    def test_nonempty_typed_resources_and_single_bit_control(self):
        src = (R / SOURCES['probe']).read_text()
        self.assertIn('V293_tcb_type PPcells', src)
        self.assertIn('destruct(PPnonempty true nil)', src)
        self.assertIn('V293_ready_storage_core_aux', src)
        self.assertIn('exists pre M O', statement(src, 'IQbuilders_nonempty'))
        self.assertIn('exists ret M O', statement(src, 'IQreturn_builder'))
        self.assertIn('BuildintPre', statement(src, 'IQbuilders_nonempty'))
        self.assertIn('BuildintRet', statement(src, 'IQreturn_builder'))
        control = statement(src, 'IQsingle_bit_control')
        self.assertIn('0<INUM /\\ 1<INUM', control)
        self.assertIn('IQother 0 true)0 false 1=true', control)
        self.assertIn('forall j,j<>1', control)
        self.assertNotIn('cstepstar', control)
        endpoints = statement(src, 'IQactual_endpoints')
        self.assertEqual(endpoints.count('InfRules'), 2)
        self.assertIn('sprim(eoi Int.zero)', endpoints)
        self.assertIn('sprim exint', endpoints)

    def test_stable_compiles_and_recursive_trust(self):
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
            roots += [Path(p).stem + '.' + n for n in
                      re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', src, re.M)]
        trust = read('trust.json')
        self.assertTrue(trust['passed'])
        self.assertTrue(trust['recursive'])
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(set(trust['assumptions']) <= set(trust['allowed']))
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))
