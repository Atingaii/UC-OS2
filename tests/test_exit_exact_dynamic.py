"""动态精确 Exit 的结构／身份回归；语义来自 Coq，不是语义 TDD。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage229-exit-exact-dynamic'
SOURCES = {'joint': 'certiucos/v293/proofs/V293OSSchedExactJoint.v',
           'dynamic': 'certiucos/v293/proofs/V293OSIntExitExactDynamic.v',
           'probe': 'audit/probes/V293OSIntExitExactDynamicProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return re.split(r'\b' + re.escape(name) + r'\s*:', src, maxsplit=1)[1].split('Proof.', 1)[0]


class ExitExactDynamicTests(unittest.TestCase):
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
        self.assertEqual(source['previous_manifest_sha256'],
                         '0092c2a642f018c9c950652cf7ad54419e2b10127bbe00ff5d449eb4ecdfae7d')

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
            if kind != 'probe':
                self.assertNotIn('CertiOS.audit.', src)
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', src, re.M)]
        trust = read('trust.json')
        self.assertEqual(len(roots), 23)
        self.assertTrue(trust['passed'])
        self.assertTrue(trust['recursive'])
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))
        self.assertEqual(trust['single_factor_counter_boundary_control'],
                         'V293OSIntExitExactDynamicProbe.XDcounter_control')

    def test_original_entry_codec_inv_and_changed_exact_post(self):
        src = (R / SOURCES['dynamic']).read_text()
        for token in ['Let changedpre:=V293_ready_dynamic_changed_fpre',
                      'Let exitpre:=V293_ready_dynamic_exit_fpre',
                      'Let Inv0:=V293_ready_dynamic_exit_inv',
                      'match V293_changed_decode lg with',
                      'Let changedfq x:=V293_exact_builder_fpost',
                      'V293_OSIntExit_exact_builder_contract',
                      'V293_OSIntExit_unified_builder_contract']:
            self.assertIn(token, src)
        post = src.split('Definition V293_exact_dynamic_exit_fpost', 1)[1].split('Lemma', 1)[0]
        self.assertIn('Some(true,args)=>V293_exact_dynamic_changed_fpost', post)
        self.assertIn('Some(false,args)=>quietsamefq', post)
        kept = statement(src, 'V293_exact_dynamic_quiet_same_post')
        self.assertIn('V293_ready_dynamic_exit_fpost', kept)
        self.assertIn('logic_ie false::args', kept)
        for name in ['V293_exact_dynamic_changed_builder_contract',
                     'V293_OSIntExit_exact_dynamic_builder_contract',
                     'V293_OSIntExit_exact_dynamic_changed_call']:
            self.assertEqual(statement(src, name).count('InfRules'), 1)

    def test_same_three_function_spec_and_actual_call(self):
        src = (R / SOURCES['dynamic']).read_text()
        env = src.split('Theorem V293_exact_dynamic_WFFunEnv', 1)[1].split('Qed.', 1)[0]
        for token in ['V293_ready_irq_unit', 'V293_exact_dynamic_spec',
                      'V293_OSIntExit_exact_dynamic_builder_contract',
                      'V293_OSIntEnter_local_contract', 'V293_OSSchedNew_exact_joint_contract']:
            self.assertIn(token, env)
        call = src.split('Theorem V293_OSIntExit_exact_dynamic_changed_call', 1)[1].split('Qed.', 1)[0]
        self.assertIn('eapply call_rule', call)
        self.assertIn('V293_exact_builder_pre_local', call)
        self.assertIn('V293_exact_builder_post_local', call)
        joint = (R / SOURCES['joint']).read_text()
        for token in ['V293_OSSchedNew_exact_contract', 'V293_OSSchedNew_ISR_contract',
                      'V293_exact_critical_to_joint', 'V293_ISR_to_exact_joint']:
            self.assertIn(token, joint)
        self.assertEqual(joint.count('V293_override_embedding'), 2)
        self.assertEqual(joint.count('[exact H|intros;reflexivity|intros;reflexivity]'), 2)
        probe = (R / SOURCES['probe']).read_text()
        self.assertIn('WFFunEnv RDprogram XDspec', probe)
        for name in ['XDactual_contract', 'XDactual_call']:
            self.assertIn('InfRules XDspec', statement(probe, name))

    def test_same_physical_entry_literal_post_and_bounded_control(self):
        src = (R / SOURCES['probe']).read_text()
        for name in ['XDentry_owned', 'XDcall_entry_owned']:
            self.assertIn('JBstate(JBmemory nest c old)ci(sched;;aop)', statement(src, name))
        self.assertIn('Proof. apply RDchanged_nonempty. Qed.', src)
        self.assertIn('getasrt(XDfq nil result(RDlg nest c aop ci)OwnershipWaiting)=XIpost aop ci result', src)
        self.assertIn('Proof. apply RDcounter_dynamic_control. Qed.', src)
        self.assertIn('XDpost(RDlg nest c aop ci)result=XDpost(RDlg nest c\' aop ci)result', src)
        doc = (R / 'audit/STAGE229_EXIT_EXACT_DYNAMIC.md').read_text()
        for token in ['不是两次完整执行', '不是初始化可达', '不声称语义 TDD',
                      'quiet/same 后置仍是原弱契约', '不冻结', '常 Aemp', 'assertion equality']:
            self.assertIn(token, doc)
