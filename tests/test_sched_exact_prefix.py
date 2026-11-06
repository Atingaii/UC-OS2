"""精确调度前缀的结构/证据回归；语义由 Coq 内核检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage226-sched-exact-prefix'
SOURCES = {'internal': 'certiucos/v293/proofs/V293OSSchedExactPrefix.v',
           'probe': 'audit/probes/V293OSSchedExactPrefixProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return re.split(r'\b' + re.escape(name) + r'\s*:', src, maxsplit=1)[1].split('Proof.', 1)[0]


class SchedExactPrefixTests(unittest.TestCase):
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
                         '1c393d3d80903baf37eac6f7479adea0ce108a0a0a4b15ab133d27cb55d96d04')

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
        roots.append('V293InterruptReadyLocalProbe.RLlocal_exactness_control')
        trust = read('trust.json')
        self.assertTrue(trust['passed'])
        self.assertTrue(trust['recursive'])
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))

    def test_real_assignment_and_call_keep_exact_post(self):
        src = (R / SOURCES['internal']).read_text()
        a = statement(src, 'V293_OSSched_exact_target_assign')
        self.assertEqual(a.count('InfRules'), 1)
        self.assertEqual(a.count('V293_sched_exact_post'), 2)
        self.assertIn('V293_OSSched_target_update table high target', a)
        self.assertEqual(src.count('eapply assign_rule'), 1)
        c = statement(src, 'V293_OSSched_exact_critical_prefix')
        self.assertEqual(c.count('InfRules'), 1)
        self.assertIn('V293_sched_exact_fpre', c)
        self.assertIn('InfRules Spec sd li RI', c)
        self.assertIn('V293_OSSchedNew_exact_call', src)
        self.assertIn('apply V293_OSSched_exact_target_assign', src)
        self.assertIn('V293_exact_prefix_read_resource', src)
        self.assertNotIn('V293_retained_OSSched_storage_prefix_returned', src)
        self.assertNotIn('CertiOS.audit.', src)
        self.assertNotIn('GOOD_OS', src)

    def test_lending_and_reuniting_do_not_hide_remaining_resources(self):
        src = (R / SOURCES['internal']).read_text()
        ret = src.split('Definition V293_exact_storage_prefix_returned :=', 1)[1].split('Theorem', 1)[0]
        self.assertIn('p_local V293_shared_li tid nil', ret)
        self.assertNotIn('Atrue', src)
        self.assertNotIn('CurLINV', ret)
        for token in ['V293_retained_prefix_returned', 'Ais stack', 'Acs critical',
                      'V293_sched_globals', 'V293_prefix_bindings', '** px']:
            self.assertIn(token, ret)
        for token in ['V293_inputs_borrow', 'V293_array_borrow',
                      'V293_inputs_reunite', 'V293_array_reunite',
                      'CurTid tid ==> p_local V293_shared_li tid nil',
                      'apply V293_switch_local_empty']:
            self.assertIn(token, src)
        c = statement(src, 'V293_OSSched_exact_storage_closed_prefix')
        self.assertEqual(c.count('InfRules'), 1)
        self.assertIn('V293_retained_storage_prefix_entry', c)
        self.assertIn('V293_exact_storage_prefix_returned', c)
        self.assertIn('V293_opened_inv', c)

    def test_nonempty_joint_storage_and_bounded_control(self):
        src = (R / SOURCES['probe']).read_text()
        c = statement(src, 'SPnonempty')
        self.assertIn('SPentry different events now aop', c)
        self.assertIn('SPborrowed different events now aop', c)
        self.assertIn('V293_storage_closed_prefix_entry_witness', src)
        self.assertIn('apply V293_exact_storage_prefix_lend', src)
        self.assertIn('forall sd RI', statement(src, 'SPenvironment'))
        c = statement(src, 'SPactual_prefix')
        self.assertEqual(c.count('InfRules'), 1)
        self.assertIn('sseq(scall 200%Z nil)(sassign', c)
        self.assertIn('SPreturned', c)
        ret = src.split('Definition SPreturned', 1)[1].split('Theorem', 1)[0]
        for token in ['V293_byteval 12', 'V293_array true', 'p_local', 'V293_storage_open']:
            self.assertIn(token, ret)
        self.assertNotIn('Atrue', ret)
        self.assertEqual(read('trust.json')['reused_local_only_control'],
                         'V293InterruptReadyLocalProbe.RLlocal_exactness_control')
        doc = (R / 'audit/STAGE226_SCHED_EXACT_PREFIX.md').read_text()
        for token in ['不是单因素消融', '不同 fixture', '不是完整前置反例',
                      '尚未替换原三函数 Spec', 'Tptr Tvoid', '不声称语义 TDD']:
            self.assertIn(token, doc)
