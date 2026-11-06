"""同一就绪不变量下的三函数联合环境的结构回归；语义来自Coq，不声称语义TDD。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage223-interrupt-ready-environment'
SOURCES = {'internal': 'certiucos/v293/proofs/V293InterruptReadyEnvironment.v',
           'probe': 'audit/probes/V293InterruptReadyEnvironmentProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return re.split(r'\b' + re.escape(name) + r'\s*:', src, maxsplit=1)[1].split('Proof.', 1)[0]


class InterruptReadyEnvironmentTests(unittest.TestCase):
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

    def test_same_inv_same_program_and_three_body_contracts(self):
        src = (R / SOURCES['internal']).read_text()
        self.assertIn('V293_ready_irq_prefix++', src)
        self.assertIn('++V293_ready_irq_suffix)=Inv0', src)
        self.assertIn('V293_ready_dynamic_exit_inv', src)
        self.assertIn('V293_exit_env_unit exit enter sched', src)
        self.assertIn('V293_exit_boundary_body running nesting lock saved', src)
        self.assertIn('Some(xfp,xfq,(Tvoid,nil))', src)
        self.assertIn('Some(efp,efq,(Tvoid,nil))', src)
        self.assertIn('Some(sfp,sfq,(Tvoid,nil))', src)
        self.assertIn('V293_OSIntExit_ready_dynamic_builder_contract', src)
        self.assertIn('V293_OSIntEnter_ready_contract', src)
        self.assertIn('V293_OSSchedNew_joint_contract', src)
        for n in ['V293_ready_irq_WFFunEnv', 'V293_ready_irq_WFIFun']:
            t = statement(src, n)
            self.assertNotIn('InfRules', t)
            self.assertIn('exit<>enter ->exit<>sched ->enter<>sched', t)
            self.assertIn('GoodFrm extra', t)
        self.assertNotIn('CertiOS.audit.', src)
        self.assertNotIn('GOOD_OS', src)
        self.assertNotIn('WFInt', src)

    def test_actual_call_not_a_callee_oracle(self):
        src = (R / SOURCES['internal']).read_text()
        t = statement(src, 'V293_ready_irq_Enter_call')
        self.assertEqual(t.count('InfRules'), 1)
        self.assertIn('InfRules(V293_ready_irq_spec exit enter sched)', t)
        self.assertIn('(scall enter nil)', t)
        self.assertIn('rewrite <-V293_ready_irq_inv_layout', src)
        self.assertIn('apply V293_OSIntEnter_ready_call', src)
        probe = (R / SOURCES['probe']).read_text()
        env = statement(probe, 'REenvironment')
        self.assertIn('GoodI RDinv', env)
        self.assertIn('WFFunEnv RDprogram REspec', env)
        self.assertIn('WFIFun RDprogram REspec', env)
        call = statement(probe, 'REactual_call')
        self.assertIn('InfRules REspec V293_scheduler V293_shared_li RDinv', call)
        self.assertEqual(call.count('InfRules'), 1)

    def test_real_nonempty_builder_and_single_spec_entry_control(self):
        src = (R / SOURCES['probe']).read_text()
        self.assertIn('JBmemory 0 Int.zero Int.zero', src)
        self.assertIn('pose proof(JBentry', src)
        self.assertIn('V293_retained_arrays_ready', src)
        self.assertIn('RTliteral_rel', src)
        self.assertIn('V293_ready_storage_core_aux', src)
        for n in ['BuildPreI', 'BuildRetI']:
            self.assertIn(n, statement(src, 'REbuilder'))
        self.assertIn('REstate |=REboundary ** A_dom_lenv nil',
                      statement(src, 'REentry_nonempty'))
        control = statement(src, 'REsingle_entry_control')
        self.assertIn('REstate |=Aemp ** (REboundary ** A_dom_lenv nil)', control)
        self.assertIn('~st|=pre', control)
        self.assertIn('forall f,f<>301%Z ->REspec f=RDspec f', control)
        self.assertIn('Some pre=Some(Aemp ** (Afalse ** A_dom_lenv nil))', src)
        self.assertNotIn('cstepstar', control)
        exit_entry = statement(src, 'REexit_nonempty')
        self.assertIn('nest<=1', exit_entry)
        self.assertIn('REspec 300%Z=Some(RDfp,RDfq,(Tvoid,nil))', exit_entry)
        self.assertIn('apply RDchanged_nonempty', src)

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
