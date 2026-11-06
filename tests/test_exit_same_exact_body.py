"""same 完整本体精确资源的结构与身份回归；语义由 Coq 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage231-exit-same-exact-body'
SOURCES = {'scheduler': 'certiucos/v293/proofs/V293OSSchedISRExact.v',
           'same': 'certiucos/v293/proofs/V293OSIntExitSameExact.v',
           'probe': 'audit/probes/V293OSIntExitSameExactProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


class ExitSameExactBodyTests(unittest.TestCase):
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
                         '9f91056f4781a7ea9f6ed4de5e376603b01381e57e8d47b4eedd4c2f7e359860')

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
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))
        self.assertEqual(trust['single_factor_local_assertion_boundary_control'],
                         'V293OSIntExitSameExactProbe.QElocal_control')

    def test_real_scheduler_payload_builders_environment_call_and_assignment(self):
        src = (R / SOURCES['scheduler']).read_text()
        for token in ['V293_ISR_sched_args', 'V293_ISR_sched_args_roundtrip',
                      'V293_sched_ISR_context', 'V293_sched_exact_payload',
                      'BuildPreI', 'BuildRetI', 'V293_OSSchedNew_ISR_exact_contract',
                      'V293_OSSchedNew_ISR_exact_WFFunEnv', 'eapply call_rule',
                      'V293_OSSchedNew_ISR_exact_call', 'V293_OSSched_exact_target_assign']:
            self.assertIn(token, src)
        self.assertNotIn('apply V293_sched_payload', src)
        self.assertNotIn('apply V293_OSSchedNew_ISR_contract', src)

    def test_exact_resources_through_real_full_same_body(self):
        src = (R / SOURCES['same']).read_text()
        core = src.split('Definition V293_exit_same_exact_core', 1)[1].split('Lemma V293_exit_same_exact_data_good', 1)[0]
        self.assertIn('p_local li tid nil', core)
        self.assertNotIn('CurLINV', core)
        self.assertNotIn('Atrue', core)
        for token in ['V293_exit_ready_exact_decrement', 'V293_OSSched_ISR_exact_prefix',
                      'V293_exact_tail_reads', 'V293_OSSched_priority_comparison',
                      'V293_OSIntExit_same_exact_critical', 'destruct enabled',
                      'OS[ir,enabled,si,ci]', 'V293_time_zero', 'V293_exit_running_eval',
                      'V293_exit_boundary_body', 'apply ret_rule']:
            self.assertIn(token, src)
        self.assertNotIn('apply V293_OSIntExit_same_priority_body', src)
        self.assertNotIn('apply V293_OSIntExit_context_same_dispatch', src)

    def test_nonempty_actual_fixture_and_bounded_claims(self):
        src = (R / SOURCES['probe']).read_text()
        for name in ['QEcurrent', 'QEinternal_owned', 'QEjoint_owned', 'QEphysical_owned',
                     'QEbig_owned', 'QEdata_owned', 'QEpre_nonempty', 'QEbody',
                     'QEboth_ie_and_nonempty_stacks', 'QEsaved_read', 'QEwithout_zero',
                     'QEscheduler_environment', 'QEcallee_nonempty', 'QEactual_scheduler_call']:
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        self.assertNotIn('pose proof(RCbig_owned', src)
        self.assertIn('Proof. apply RLlocal_exactness_control. Qed.', src)
        self.assertIn('RCbigmemory 12 nest c 1 old', src)
        self.assertIn('cons 0 nil', src)
        self.assertIn('cons false nil', src)
        doc = (R / 'audit/STAGE231_EXIT_SAME_EXACT_BODY.md').read_text()
        for token in ['same 的新前置也更强', '尚未替换动态三函数 Spec',
                      '常 Aemp LocalInv', '不是初始化可达', '不是两次完整执行',
                      '不声称语义 TDD', 'uCOS3 未开始']:
            self.assertIn(token, doc)
