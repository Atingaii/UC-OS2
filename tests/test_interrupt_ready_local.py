"""精确局部资源贯穿Enter和真实EOI前缀的结构回归；语义来自Coq，不声称语义TDD。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage224-interrupt-ready-local'
SOURCES = {'internal': 'certiucos/v293/proofs/V293InterruptReadyLocal.v',
           'probe': 'audit/probes/V293InterruptReadyLocalProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return re.split(r'\b' + re.escape(name) + r'\s*:', src, maxsplit=1)[1].split('Proof.', 1)[0]


class InterruptReadyLocalTests(unittest.TestCase):
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

    def test_exact_local_kept_through_full_body_and_builders(self):
        src = (R / SOURCES['internal']).read_text()
        boundary = src.split('Definition V293_enter_local_boundary', 1)[1].split('Definition', 1)[0]
        self.assertIn('p_local V293_shared_li tid nil', boundary)
        self.assertNotIn('CurLINV', boundary)
        self.assertIn('apply V293_OSIntEnter_updates_hoare', src)
        self.assertIn('apply V293_OSIntEnter_local_updates', src)
        contract = statement(src, 'V293_OSIntEnter_local_contract')
        self.assertIn('BuildPreI', contract)
        self.assertIn('BuildRetI', contract)
        self.assertIn('(V293_OSIntEnter_body running nesting)', contract)
        self.assertEqual(contract.count('InfRules'), 1)
        self.assertIn('[|result=None|]', src)
        self.assertIn('V293_enter_ready_args lg', src)
        self.assertNotIn('Definition V293_enter_local_args', src)
        self.assertNotIn('CertiOS.audit.', src)
        self.assertNotIn('GOOD_OS', src)
        self.assertNotIn('WFInt', src)

    def test_same_environment_actual_prefix_and_return_resources(self):
        src = (R / SOURCES['internal']).read_text()
        self.assertIn('V293_ready_dynamic_exit_inv', src)
        self.assertIn('V293_ready_irq_unit unmap group rows', src)
        self.assertIn('rewrite <-V293_ready_irq_inv_layout', src)
        for name in ['V293_ready_local_WFFunEnv', 'V293_ready_local_WFIFun']:
            self.assertNotIn('InfRules', statement(src, name))
        for name in ['V293_OSIntExit_ready_dynamic_builder_contract',
                     'V293_OSIntEnter_local_contract', 'V293_OSSchedNew_joint_contract']:
            self.assertIn(name, src)
        for name in ['V293_irq_local_enter_pre', 'V293_irq_local_enter_post']:
            self.assertIn('V293_irq_ready_closed', statement(src, name))
            self.assertIn('V293_enter_local_boundary', statement(src, name))
        prefix = statement(src, 'V293_irq_local_eoi_enter')
        self.assertEqual(prefix.count('InfRules'), 1)
        self.assertIn('(sseq(sprim(eoi id))(scall enter nil))', prefix)
        self.assertIn('BuildintPre', prefix)
        self.assertNotIn('scall exit', prefix)
        self.assertIn('apply eoi_ieoff_rule', src)
        self.assertIn('call_rule', src)
        ret = statement(src, 'V293_irq_local_return_resources')
        self.assertIn("iretasrt' i ir si Inv0 ** p_local V293_shared_li tid lg", ret)

    def test_real_subheap_and_local_only_single_factor_control(self):
        src = (R / SOURCES['probe']).read_text()
        entry = statement(src, 'RLentry_nonempty')
        self.assertIn('join M Mf(JBmemory 0 Int.zero Int.zero)', entry)
        self.assertIn('join O Of(RIabstract OwnershipWaiting)', entry)
        self.assertIn('RLstate M O |=RLboundary ** A_dom_lenv nil', entry)
        self.assertIn('pose proof REheap', src)
        self.assertIn('apply sat_split in Entry', src)
        self.assertIn('REstate |=CurLINV V293_shared_li OwnershipWaiting',
                      statement(src, 'RLlocal_exactness_control'))
        self.assertIn('~REstate |=p_local V293_shared_li OwnershipWaiting nil',
                      statement(src, 'RLlocal_exactness_control'))
        self.assertNotIn('cstepstar', statement(src, 'RLlocal_exactness_control'))
        self.assertIn('O=emp', statement(src, 'RLlocal_empty_abstract'))
        self.assertIn('RLspec f=REspec f', statement(src, 'RLunchanged_entries'))
        for name in ['RLactual_call', 'RLclosed_call', 'RLeoi_enter']:
            t = statement(src, name)
            self.assertIn('InfRules RLspec V293_scheduler V293_shared_li RDinv', t)
            self.assertEqual(t.count('InfRules'), 1)
        self.assertIn('GoodI RDinv', statement(src, 'RLenvironment'))
        self.assertIn('WFFunEnv RDprogram RLspec', statement(src, 'RLenvironment'))
        self.assertIn('WFIFun RDprogram RLspec', statement(src, 'RLenvironment'))
