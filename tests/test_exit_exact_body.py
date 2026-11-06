"""精确 Exit 本体的结构/证据回归；语义由 Coq 内核检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage227-exit-exact-body'
SOURCES = {'internal': 'certiucos/v293/proofs/V293OSIntExitExact.v',
           'probe': 'audit/probes/V293OSIntExitExactProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return re.split(r'\b' + re.escape(name) + r'\s*:', src, maxsplit=1)[1].split('Proof.', 1)[0]


class ExitExactBodyTests(unittest.TestCase):
    def test_source_identity_and_prospective_protocol(self):
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
                         'e0f772d0b7ea71f3f9400f3cb3e0bf2ce7307fb4d48577a8846e98775828389c')

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
        roots.extend(['V293InterruptReadyLocalProbe.RLlocal_exactness_control',
                      'V293OSIntExitReadyBodyProbe.JBexcrit_control'])
        trust = read('trust.json')
        self.assertTrue(trust['passed'])
        self.assertTrue(trust['recursive'])
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))

    def test_real_control_flow_uses_exact_callee_without_oracle(self):
        src = (R / SOURCES['internal']).read_text()
        for name in ['V293_OSIntExit_exact_dispatch', 'V293_OSIntExit_exact_body']:
            s = statement(src, name)
            self.assertEqual(s.count('InfRules'), 1)
            self.assertIn('V293_sched_exact_fpre', s)
            self.assertIn('V293_sched_exact_fpost', s)
        for token in ['apply V293_OSSched_exact_storage_prefix_returned',
                      'apply V293_ready_exit_changed_tail', 'apply V293_OSIntExit_exact_dispatch',
                      'V293_OSIntExit_nesting_dispatch_hoare', 'apply encrit2_rule',
                      'apply V293_ready_storage_resumed_excrit', 'apply ret_rule']:
            self.assertIn(token, src)
        for token in ['V293_OSIntExit_ready_body;', 'apply V293_exit_ready_body_lend',
                      'CertiOS.audit.', 'GOOD_OS']:
            self.assertNotIn(token, src)
        s = statement(src, 'V293_OSIntExit_exact_body')
        for token in ['nest<=1', 'V293_ready_select', 'indom tasks tid',
                      'V293_exit_boundary_body', 'OS[(fun _:hid=>false),false,si,ci]']:
            self.assertIn(token, s)

    def test_exact_post_and_private_frame_never_absorb_resources(self):
        src = (R / SOURCES['internal']).read_text()
        self.assertIn('p_local V293_shared_li tid nil ==> CurTid tid', src)
        self.assertIn('CurTid tid ==> p_local V293_shared_li tid nil', src)
        self.assertIn('apply V293_switch_local_empty', src)
        for text in src.split('Let private:=')[1:]:
            self.assertNotIn('Atrue', text.split('.\n', 1)[0])
        post = src.split('Definition V293_exit_exact_body_post critical:=', 1)[1].split('Lemma', 1)[0]
        for token in ['<||aop||>', 'SWINV inv', 'p_local V293_shared_li tid nil',
                      'Ais si', 'Acs critical', 'private']:
            self.assertIn(token, post)
        self.assertNotIn('Atrue', post)
        self.assertNotIn('CurLINV', post)
        pack = src.split('Lemma V293_exit_exact_body_post_pack', 1)[1].split('Qed.', 1)[0]
        self.assertIn('apply V293_current_to_exact_local', pack)
        self.assertNotIn('CurLINV', pack)
        lend = src.split('Lemma V293_exit_exact_body_lend', 1)[1].split('Qed.', 1)[0]
        self.assertIn('GV_separate_rw', lend)
        self.assertIn('apply V293_exact_storage_prefix_lend_value', lend)

    def test_same_typed_nonempty_fixture_literal_post_and_bounded_controls(self):
        src = (R / SOURCES['probe']).read_text()
        entry = statement(src, 'XEnonempty')
        body = statement(src, 'XEactual_body')
        for s in [entry, body]:
            self.assertIn('JBdata nest c old', s)
        self.assertIn('apply JBentry_nonempty', src)
        self.assertIn('InfRules XEspec', body)
        self.assertIn('WFFunEnv XEprogram XEspec', statement(src, 'XEenvironment'))
        self.assertIn('forall sd RI', statement(src, 'XEenvironment'))
        post = src.split('Definition XEpost', 1)[1].split('Theorem', 1)[0]
        for token in ['JBcells', 'V293_tcb_type', 'p_local V293_shared_li OwnershipWaiting nil',
                      'Ais nil ** Acs ci', 'V293_counter_bindings', 'V293_sched_globals',
                      'V293_prefix_bindings', 'V293_time_cell true 120%Z 98%positive(Vint32 Int.zero)']:
            self.assertIn(token, post)
        self.assertNotIn('Atrue', post)
        trust = read('trust.json')
        self.assertEqual(trust['reused_local_only_control'],
                         'V293InterruptReadyLocalProbe.RLlocal_exactness_control')
        self.assertEqual(trust['reused_final_primitive_control'],
                         'V293OSIntExitReadyBodyProbe.JBexcrit_control')
        doc = (R / 'audit/STAGE227_EXIT_EXACT_BODY.md').read_text()
        for token in ['不是两次完整本体执行', '不同 fixture', '不是完整前置反例',
                      '尚未替换原三函数 Spec', '不声称语义 TDD', '不冻结', '不能推广到任意 LocalInv']:
            self.assertIn(token, doc)
