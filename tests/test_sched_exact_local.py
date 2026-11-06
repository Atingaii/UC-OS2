"""调度器精确局部资源的结构回归；语义来自Coq，不声称语义TDD。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage225-sched-exact-local'
SOURCES = {'internal': 'certiucos/v293/proofs/V293OSSchedExactLocal.v',
           'probe': 'audit/probes/V293OSSchedExactLocalProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return re.split(r'\b' + re.escape(name) + r'\s*:', src, maxsplit=1)[1].split('Proof.', 1)[0]


class SchedExactLocalTests(unittest.TestCase):
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
        roots.append('V293InterruptReadyLocalProbe.RLlocal_exactness_control')
        trust = read('trust.json')
        self.assertTrue(trust['passed'])
        self.assertTrue(trust['recursive'])
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(set(trust['assumptions']) <= set(trust['allowed']))
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))

    def test_exact_local_kept_in_original_assignments_and_builders(self):
        src = (R / SOURCES['internal']).read_text()
        for name in ['V293_sched_exact_common', 'V293_sched_exact_resource']:
            definition = src.split('Definition ' + name + ' ', 1)[1].split('Definition', 1)[0].split('Lemma', 1)[0]
            self.assertIn('p_local li tid nil', definition)
            self.assertNotIn('CurLINV', definition)
        for name in ['V293_OSSchedNew_exact_row', 'V293_OSSchedNew_exact_priority']:
            self.assertIn('V293_sched_exact_common', statement(src, name))
            self.assertEqual(statement(src, name).count('InfRules'), 1)
        self.assertEqual(src.count('eapply assign_rule'), 2)
        self.assertIn('apply V293_OSSchedNew_exact_row', src)
        self.assertIn('apply V293_OSSchedNew_exact_priority', src)
        self.assertNotIn('Definition V293_OSSchedNew_post', src)
        self.assertIn('V293_OSSchedNew_post common', src)
        c = statement(src, 'V293_OSSchedNew_exact_contract')
        for token in ['BuildPreI', 'BuildRetI', 'V293_OSSchedNew_body']:
            self.assertIn(token, c)
        self.assertEqual(c.count('InfRules'), 1)
        self.assertNotIn('InfRules', statement(src, 'V293_OSSchedNew_exact_WFFunEnv'))
        self.assertNotIn('CertiOS.audit.', src)
        self.assertNotIn('GOOD_OS', src)
        self.assertNotIn('WFInt', src)

    def test_original_codec_call_and_exact_returned_resources(self):
        src = (R / SOURCES['internal']).read_text()
        self.assertIn('V293_critical_args lg', src)
        self.assertIn('V293_critical_call_lg lo hi aop stack critical', src)
        self.assertIn('rewrite V293_critical_args_roundtrip', src)
        self.assertIn('eapply call_rule', src)
        self.assertIn('V293_OSSchedNew_internal_unit', src)
        self.assertNotIn('Definition V293_critical_args', src)
        self.assertNotIn('Definition V293_OSSchedNew_internal_unit', src)
        c = statement(src, 'V293_OSSchedNew_exact_call')
        self.assertEqual(c.count('InfRules'), 1)
        self.assertIn('GoodFrm frame', c)
        self.assertIn('V293_sched_critical I stack critical', c)
        self.assertIn('InfRules Spec sd li RI', c)
        self.assertIn('li I RI', statement(src, 'V293_OSSchedNew_exact_contract'))
        self.assertNotIn('GoodFrm', statement(src, 'V293_sched_exact_payload'))
        ret = statement(src, 'V293_sched_exact_post_retains')
        for token in ['[|result=None|]', 'p_local li tid nil', 'V293_sched_inputs',
                      'V293_sched_globals', 'Aie false', 'V293_ready_select']:
            self.assertIn(token, ret)
        self.assertNotIn('Atrue', ret)
        self.assertNotIn('CurLINV', ret)

    def test_nonempty_builders_and_reused_local_only_control(self):
        src = (R / SOURCES['probe']).read_text()
        c = statement(src, 'ELbuilders_nonempty')
        for token in ['BuildPreI ELprogram', 'BuildRetI ELprogram',
                      'V293_witness_memory |=pre']:
            self.assertIn(token, c)
        self.assertIn('apply ELcurrent', src)
        self.assertIn('apply ELcritical', src)
        self.assertIn('Definition ELCI:Inv:=fun k=>V293_shared_inv(S k).', src)
        for name in ['ELenvironment', 'ELactual_call']:
            self.assertIn('forall sd RI', statement(src, name))
        self.assertEqual(statement(src, 'ELactual_call').count('InfRules'), 1)
        old = (R / 'audit/probes/V293InterruptReadyLocalProbe.v').read_text()
        c = statement(old, 'RLlocal_exactness_control')
        self.assertIn('REstate |=CurLINV V293_shared_li OwnershipWaiting', c)
        self.assertIn('~REstate |=p_local V293_shared_li OwnershipWaiting nil', c)
        self.assertNotIn('cstepstar', c)
        trust = read('trust.json')
        self.assertEqual(trust['reused_local_only_control'],
                         'V293InterruptReadyLocalProbe.RLlocal_exactness_control')
        self.assertIn('CertiOS.audit.probes.V293InterruptReadyLocalProbe', trust['commands'][1]['command'])
        doc = (R / 'audit/STAGE225_SCHED_EXACT_LOCAL.md').read_text()
        for token in ['空尾', '不是两次函数执行', '不同 fixture', '尚未替换原三函数 Spec',
                      'nil', '同一执行者', '不声称语义 TDD']:
            self.assertIn(token, doc)
