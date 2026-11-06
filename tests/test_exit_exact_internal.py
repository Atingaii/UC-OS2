"""精确 Exit 的 builders/环境结构回归；Coq 负责程序推导，不是语义 TDD。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage228-exit-exact-internal'
SOURCES = {'internal': 'certiucos/v293/proofs/V293OSIntExitExactInternal.v',
           'probe': 'audit/probes/V293OSIntExitExactInternalProbe.v'}
CONTROL = 'V293OSIntExitReadyInternalProbe.RBshadow_control'


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return re.split(r'\b' + re.escape(name) + r'\s*:', src, maxsplit=1)[1].split('Proof.', 1)[0]


class ExitExactInternalTests(unittest.TestCase):
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
                         '3397835bd50d8a8aae1dce501cb2a32ce3f1cf1dddf34ba08a03c5a056e838e2')

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
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', src, re.M)]
        trust = read('trust.json')
        self.assertTrue(trust['passed'])
        self.assertTrue(trust['recursive'])
        self.assertEqual(trust['roots'], roots + [CONTROL])
        self.assertEqual(trust['roots_printed'], len(roots) + 1)
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))
        self.assertEqual(trust['reused_shadow_boundary_control'], CONTROL)

    def test_builders_reuse_entry_and_retain_exact_resources(self):
        src = (R / SOURCES['internal']).read_text()
        contract = statement(src, 'V293_OSIntExit_exact_builder_contract')
        for token in ['BuildPreI', 'BuildRetI', 'V293_sched_exact_fpre', 'V293_sched_exact_fpost']:
            self.assertIn(token, contract)
        self.assertEqual(contract.count('InfRules'), 1)
        for token in ['Let entry t:=V293_ready_builder_pre', 'Let fp:=V293_ready_builder_fpre',
                      'apply V293_ready_builder_unpack', 'apply V293_OSIntExit_exact_body',
                      'apply V293_exact_builder_pack', 'apply V293_exit_builder_forget_names',
                      'apply agvarenv_elim in Bind;exact(proj2 Bind)']:
            self.assertIn(token, src)
        post = src.split('Definition V293_exact_builder_post', 1)[1].split('Lemma', 1)[0]
        for token in ['p_local V293_shared_li t nil', 'SWINV inv', '<||aop||>',
                      'Ais si ** Acs ci', 'globals ** extra']:
            self.assertIn(token, post)
        self.assertNotIn('Atrue', post)
        pack = src.split('Lemma V293_exact_builder_pack', 1)[1].split('Qed.', 1)[0]
        self.assertNotIn('Atrue', pack)
        self.assertNotIn('CurLINV', pack)
        for token in ['CertiOS.audit.', 'V293_OSIntExit_ready_builder_contract;', 'apply V293_ready_builder_pack']:
            self.assertNotIn(token, src)

    def test_same_spec_closes_two_original_functions_and_real_call(self):
        src = (R / SOURCES['internal']).read_text()
        unit = src.split('Definition V293_exit_exact_unit', 1)[1].split('Definition', 1)[0]
        self.assertIn('V293_exit_boundary_function', unit)
        self.assertIn('V293_OSSchedNew_function', unit)
        env = src.split('Theorem V293_OSIntExit_exact_WFFunEnv', 1)[1].split('Qed.', 1)[0]
        self.assertIn('V293_OSIntExit_exact_builder_contract', env)
        self.assertIn('V293_OSSchedNew_exact_contract', env)
        self.assertIn('WFFunEnv(V293_exit_exact_unit', env)
        call = src.split('Theorem V293_OSIntExit_exact_call', 1)[1].split('Qed.', 1)[0]
        self.assertIn('eapply call_rule', call)
        self.assertIn('V293_exact_builder_pre_local', call)
        self.assertIn('V293_exact_builder_post_local', call)
        self.assertEqual(statement(src, 'V293_OSIntExit_exact_call').count('InfRules'), 1)
        probe = (R / SOURCES['probe']).read_text()
        self.assertIn('WFFunEnv XIprogram(XIspec nest c aop ci)', probe)
        for name in ['XIactual_contract', 'XIactual_call']:
            self.assertIn('InfRules(XIspec nest c aop ci)', statement(probe, name))

    def test_same_physical_entry_literal_post_and_control_limits(self):
        src = (R / SOURCES['probe']).read_text()
        self.assertIn('getasrt(XIfq aop ci nil result nil OwnershipWaiting)=XIpost aop ci result', src)
        for name in ['XIentry_owned', 'XIcall_entry_owned']:
            self.assertIn('JBstate(JBmemory nest c old)ci(sched;;aop)', statement(src, name))
        self.assertIn('apply RBpre_owned', src)
        post = src.split('Definition XIpost', 1)[1].split('Definition', 1)[0]
        for token in ['JBcells', 'p_local V293_shared_li OwnershipWaiting nil',
                      'Ais nil ** Acs ci', 'RBglobals ** Aemp']:
            self.assertIn(token, post)
        self.assertNotIn('Atrue', post)
        self.assertNotIn('V293_exit_builder_cells', post)
        doc = (R / 'audit/STAGE228_EXIT_EXACT_INTERNAL.md').read_text()
        for token in ['不是两次完整执行', '不是初始化可达', '未替换动态三函数 Spec',
                      '不声称语义 TDD', '不冻结', '常 Aemp', '只改变局部名字及绑定']:
            self.assertIn(token, doc)
