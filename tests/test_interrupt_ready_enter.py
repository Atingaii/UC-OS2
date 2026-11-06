"""共享边界到真实Enter调用的结构回归；语义来自Coq，不声称语义TDD。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage222-interrupt-ready-enter'
SOURCES = {'internal': 'certiucos/v293/proofs/V293InterruptReadyEnter.v',
           'probe': 'audit/probes/V293InterruptReadyEnterProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return re.split(r'\b' + re.escape(name) + r'\s*:', src, maxsplit=1)[1].split('Proof.', 1)[0]


class InterruptReadyEnterTests(unittest.TestCase):
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

    def test_arbitrary_bytes_from_the_same_storage_invariant(self):
        src = (R / SOURCES['internal']).read_text()
        extract = statement(src, 'V293_enter_ready_extract')
        self.assertIn('EX run,EX nest,[|run<256 /\ nest<256|]', extract)
        self.assertNotIn('run=1', extract)
        self.assertNotIn('nest=0', extract)
        self.assertIn('prefix++', src)
        self.assertIn('++suffix', src)
        self.assertIn('V293_storage_byte_value', src)
        self.assertIn('rule_type_val_match Tint8 v=true', src)
        self.assertIn('V293_enter_ready_close', src)
        self.assertIn('V293_OSIntEnter_updates_hoare', src)
        self.assertIn('V293_enter_ready_env', src)
        self.assertNotIn('CertiOS.audit.', src)

    def test_real_body_builders_and_context_inside_contract(self):
        src = (R / SOURCES['internal']).read_text()
        body = statement(src, 'V293_OSIntEnter_ready_body')
        self.assertIn('(V293_OSIntEnter_body running nesting)', body)
        self.assertEqual(body.count('InfRules'), 1)
        contract = statement(src, 'V293_OSIntEnter_ready_contract')
        self.assertIn('Some pre=BuildPreI', contract)
        self.assertIn('Some post=BuildRetI', contract)
        self.assertIn('apply V293_OSIntEnter_ready_body', src)
        self.assertIn('WFFunEnv(V293_OSIntEnter_unit', src)
        self.assertIn('(SWINV Inv0 ** (Ais si ** Acs ci))', src)
        self.assertIn('V293_sched_critical_good', src)
        self.assertIn('eapply call_rule', src)
        call = statement(src, 'V293_OSIntEnter_ready_call')
        self.assertIn('(scall enter nil)', call)
        self.assertEqual(call.count('InfRules'), 1)
        self.assertNotIn('->\n InfRules', call.split('Spec enter=', 1)[0])
        bridge = statement(src, 'V293_irq_ready_enter_call')
        self.assertIn('V293_irq_ready_closed', bridge)
        self.assertEqual(bridge.count('InfRules'), 1)
        self.assertNotIn('GOOD_OS', src)
        self.assertNotIn('WFInt', src)

    def test_real_tcb_entries_and_only_running_byte_control(self):
        src = (R / SOURCES['probe']).read_text()
        self.assertIn('V293_tcb_type ENprefix nil', src)
        self.assertIn('destruct(IQreturn_nonempty 0)', src)
        builders = statement(src, 'ENbuilders_nonempty')
        self.assertIn('BuildPreI', builders)
        self.assertIn('BuildRetI', builders)
        self.assertIn('ENstate M O |=pre', builders)
        control = statement(src, 'ENsingle_running_control')
        self.assertIn('ENopen 0 0', control)
        self.assertIn('ENopen 1 0', control)
        self.assertEqual(control.count('ENboundary ** A_dom_lenv nil'), 2)
        self.assertIn('evalval(V293_OSIntEnter_running', control)
        self.assertIn('forall a,a<>(96%positive,0%Z)', control)
        self.assertIn('V293_interrupt_nest_after 1 255=255', control)
        self.assertIn('V293_owned_byte_update', src)
        self.assertIn('V293_interrupt_owned_eval', src)
        self.assertNotIn('cstepstar', control)
        self.assertIn('InfRules Spec sd V293_shared_li PPinv', statement(src, 'ENactual_call'))

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
