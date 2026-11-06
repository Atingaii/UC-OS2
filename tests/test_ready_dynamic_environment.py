"""动态就绪规格的结构回归；语义证据为 Coq 根，非语义 TDD。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage220-ready-dynamic-environment'
SOURCES = {'internal': 'certiucos/v293/proofs/V293OSIntExitReadyDynamic.v',
           'probe': 'audit/probes/V293OSIntExitReadyDynamicProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return re.split(r'\b' + re.escape(name) + r'\s*:', src, maxsplit=1)[1].split('Proof.', 1)[0]


class ReadyDynamicEnvironmentTests(unittest.TestCase):
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

    def test_dynamic_uses_actual_ready_builders_without_length_factor(self):
        src = (R / SOURCES['internal']).read_text()
        self.assertIn('V293_ready_builder_inv target bt bg br bh bp bc bk brun bn bl rest', src)
        self.assertIn('Let tp:=V293_tcb_type', src)
        self.assertIn('Let changedfp x:=V293_ready_builder_fpre', src)
        self.assertIn('Let changedfq x:=V293_ready_builder_fpost', src)
        self.assertIn('match V293_changed_decode lg with', src)
        self.assertIn('| Some x=>changedfp x vl nil t', src)
        self.assertNotIn('table_length', src)
        self.assertNotIn('Record V293_changed_snapshot', src)
        self.assertNotIn('Definition V293_changed_decode', src)
        self.assertNotIn('Invtransport', src)
        stmt = statement(src, 'V293_ready_dynamic_changed_builder_contract')
        self.assertEqual(stmt.count('InfRules'), 1)
        self.assertIn('Some pre=BuildPreI', stmt)
        self.assertIn('Some post=BuildRetI', stmt)
        self.assertIn('eapply (V293_OSIntExit_ready_builder_contract', src)

    def test_single_spec_real_body_and_function_environment(self):
        src = (R / SOURCES['internal']).read_text()
        stmt = statement(src, 'V293_OSIntExit_ready_dynamic_builder_contract')
        self.assertEqual(stmt.count('InfRules'), 1)
        for token in ['InfRules Spec V293_scheduler V293_shared_li Inv0',
                      'V293_exit_boundary_function', 'V293_exit_boundary_body',
                      'V293_ready_dynamic_exit_fpre', 'V293_ready_dynamic_exit_fpost']:
            self.assertIn(token, stmt)
        for token in ['V293_InfRules_spec_embedding', 'V293_critical_to_joint',
                      'V293_ISR_to_joint', 'V293_OSIntExit_unified_builder_contract',
                      'V293_OSSchedNew_joint_contract', 'V293_OSIntEnter_internal_contract',
                      'Some(jfp,jfq,(Tvoid,nil))', 'V293_exit_handoff_void_calls']:
            self.assertIn(token, src)
        self.assertIn('GoodI Inv0', statement(src, 'V293_ready_dynamic_exit_inv_good'))
        self.assertIn('WFFunEnv(unit', statement(src, 'V293_ready_dynamic_exit_env_WFFunEnv'))
        self.assertIn('WFIFun(unit', statement(src, 'V293_ready_dynamic_exit_env_WFIFun'))

    def test_typed_entry_counter_control_and_post_snapshot_erasure(self):
        src = (R / SOURCES['probe']).read_text()
        for token in ['GoodI RDinv', 'WFFunEnv RDprogram RDspec', 'WFIFun RDprogram RDspec']:
            self.assertIn(token, statement(src, 'RDenvironment'))
        self.assertIn('forall lg', statement(src, 'RDactual_contract'))
        self.assertEqual(statement(src, 'RDactual_contract').count('InfRules'), 1)
        for token in ['JBstate(JBmemory nest c old)', 'nest<=1']:
            self.assertIn(token, statement(src, 'RDchanged_nonempty'))
        self.assertIn('V293_highest_ready OwnershipTasks OwnershipReady', statement(src, 'RDentry_nonempty'))
        self.assertIn('Int.repr Int.max_unsigned', statement(src, 'RDzero_max_entry'))
        control = statement(src, 'RDcounter_dynamic_control')
        self.assertEqual(control.count('JBstate(JBmemory 1(Int.repr Int.max_unsigned)old)'), 2)
        self.assertIn('~(JBstate', control)
        self.assertEqual(control.count('V293_changed_decode'), 2)
        self.assertNotIn('cstepstar', control)
        self.assertIn('load Tint32(getmem st)(95%positive,0%Z)', statement(src, 'RDcounter_load'))
        self.assertIn('RDcounter_load 1 Int.one', src)
        self.assertIn('RDpost(RDlg nest c aop ci)result=RDpost(RDlg nest c\' aop ci)result',
                      statement(src, 'RDpost_forgets_counter'))
        self.assertIn('=Afalse', statement(src, 'RDmalformed'))

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
            self.assertNotRegex(src, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            if kind != 'probe':
                self.assertNotIn('CertiOS.audit.', src)
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', src, re.M)]
        trust = read('trust.json')
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(roots, trust['roots'])
        self.assertEqual(len(roots), trust['roots_printed'])
        self.assertTrue(set(trust['assumptions']) <= set(trust['allowed']))
