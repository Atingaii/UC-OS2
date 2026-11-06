"""动态 same 精确合同的结构与证据身份；不以文本扫描代替 Coq。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage232-exit-same-exact-dynamic'
SOURCES = {'joint': 'certiucos/v293/proofs/V293OSSchedAllExactJoint.v',
           'internal': 'certiucos/v293/proofs/V293OSIntExitSameExactInternal.v',
           'dynamic': 'certiucos/v293/proofs/V293OSIntExitAllExactDynamic.v',
           'probe': 'audit/probes/V293OSIntExitSameExactDynamicProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


class ExitSameExactDynamicTests(unittest.TestCase):
    def test_source_and_prospective_protocol_identity(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        self.assertEqual([x['function']['name'] for x in source['functions']],
                         ['OSIntEnter', 'OSIntExit', 'OS_SchedNew', 'OS_Sched'])
        for row in source['functions']:
            self.assertEqual(hashlib.sha256((D / (row['function']['name'] + '.configured.c.txt')).read_bytes()).hexdigest(),
                             row['function']['preprocessed_definition_sha256'])
        for p, h in source['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])
        self.assertEqual(source['previous_manifest_sha256'],
                         'cd609fdde367120acd1b64026be0bb33c296cc0d5e9d8dfa68b28c56cedf6ca1')

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
        self.assertTrue(trust['passed'])
        self.assertTrue(trust['recursive'])
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertEqual(len(roots), 44)
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))
        self.assertEqual(trust['single_factor_local_assertion_boundary_control'],
                         'V293OSIntExitSameExactDynamicProbe.SElocal_control')

    def test_same_exact_resources_through_real_builders(self):
        src = (R / SOURCES['internal']).read_text()
        memory = src.split('Definition V293_same_exact_exit_memory', 1)[1].split('Lemma V293_same_exact_exit_memory_good', 1)[0]
        self.assertIn('p_local li t nil', memory)
        self.assertNotIn('CurLINV', memory)
        self.assertNotIn('Atrue', memory)
        for token in ['V293_same_exit_index lg', 'V293_same_exit_valid si x',
                      'V293_same_exact_exit_builder_unpack', 'V293_same_exact_exit_builder_pack',
                      'BuildPreI', 'BuildRetI', 'V293_OSIntExit_same_exact_priority_body',
                      'OS[ir,enabled,si,ci]', 'V293_ISR_exact_sched_fpre']:
            self.assertIn(token, src)
        self.assertNotIn('Definition V293_same_exit_index', src)
        self.assertNotIn('apply V293_OSIntExit_same_builder_contract', src)

    def test_same_program_joint_exact_and_literal_branch_preservation(self):
        joint = (R / SOURCES['joint']).read_text()
        for token in ['V293_sched_exact_fpre', 'V293_ISR_exact_sched_fpre',
                      'V293_exact_critical_to_all_joint', 'V293_exact_ISR_to_all_joint',
                      'embed:=fun lg=>logic_ie true::lg', 'embed:=fun lg=>logic_ie false::lg',
                      'V293_OSSchedNew_exact_contract', 'V293_OSSchedNew_ISR_exact_contract']:
            self.assertIn(token, joint)
        src = (R / SOURCES['dynamic']).read_text()
        for token in ['V293_all_exact_dynamic_changed_kept', 'V293_all_exact_dynamic_quiet_kept',
                      'V293_quiet_exact_dynamic_fpre', 'V293_quiet_exact_dynamic_fpost',
                      'V293_OSIntExit_same_exact_builder_contract', 'V293_exact_ISR_to_all_joint',
                      'V293_exact_critical_to_all_joint', 'V293_ready_irq_unit',
                      'V293_ready_dynamic_exit_inv', 'WFFunEnv', 'WFIFun', 'eapply call_rule',
                      'V293_exit_handoff_void_calls']:
            self.assertIn(token, src)
        self.assertNotIn('Definition V293_exit_path', src)
        self.assertNotIn('apply V293_OSIntExit_same_builder_contract', src)

    def test_actual_typed_dynamic_entry_call_and_bounded_claims(self):
        src = (R / SOURCES['probe']).read_text()
        for name in ['SEpointer_bytes', 'SEcurrent', 'SEjoint_owned', 'SEbig_owned',
                     'SEbuilders', 'SEenvironment', 'SEentry_nonempty', 'SEliteral',
                     'SEactual_contract', 'SEactual_call', 'SEcall_entry_nonempty',
                     'SEie_control', 'SElocal_control', 'SEarity_control', 'SEreturn_arity_observation']:
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        self.assertNotIn('pose proof(BIowned', src)
        self.assertNotIn('apply BIpre_nonempty', src)
        self.assertIn('Tarray(Tptr V293_tcb_type)13', src)
        self.assertIn('RCbigmemory 12 nest c 1 old', src)
        self.assertIn('Proof. apply RLlocal_exactness_control. Qed.', src)
        doc = (R / 'audit/STAGE232_EXIT_SAME_EXACT_DYNAMIC.md').read_text()
        for token in ['same 的新前置也更强', '常 Aemp LocalInv', '不是初始化可达',
                      '不是两次完整执行', '不声称语义 TDD', 'BuildRetI 本身不检查参数个数',
                      'uCOS3 未开始', 'changed 与 quiet 的入口、返回字面保持']:
            self.assertIn(token, doc)
