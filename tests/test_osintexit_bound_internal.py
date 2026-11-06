"""结构和来源回归；证明结论由独立 Coq 检查，不以文本命中代替。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage240-bound-exit-body'
SOURCES = {'entry': 'certiucos/v293/proofs/V293OSIntExitBoundInternal.v',
           'probe': 'audit/probes/V293OSIntExitBoundInternalProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


class BoundInternalTests(unittest.TestCase):
    def test_source_and_prospective_protocol(self):
        s = read('source-check.json')
        self.assertTrue(s['passed'])
        self.assertEqual([x['function']['name'] for x in s['functions']],
                         ['OSIntEnter', 'OSIntExit', 'OS_SchedNew', 'OS_Sched'])
        for p, h in s['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
        for x in s['functions']:
            p = D / (x['function']['name'] + '.configured.c.txt')
            self.assertEqual(hashlib.sha256(p.read_bytes()).hexdigest(),
                             x['function']['preprocessed_definition_sha256'])
        self.assertEqual(s['previous_manifest_sha256'],
                         '2116fe29d224b0b0860fa8c79739dedb36ad312729fbe5a233f58a30da434b22')
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])

    def test_body_and_builders_do_not_assume_middle_proof(self):
        src = (R / SOURCES['entry']).read_text()
        for name in ['V293_OSIntExit_bound_body', 'V293_OSIntExit_bound_builder_contract',
                     'V293_OSIntExit_bound_call', 'V293_bound_irq_WFFunEnv',
                     'V293_bound_irq_WFIFun']:
            header = src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]
            self.assertLessEqual(header.count('InfRules'), 1)
            self.assertNotIn('==>', header)
            self.assertNotIn('CurLINV', header)
        for token in ['apply(V293_time_zero', 'apply encrit2_rule',
                      'V293_OSIntExit_nesting_dispatch_hoare',
                      'V293OSIntExitLocalDispatch.V293_exit_bound_body_lend',
                      'apply V293_OSIntExit_bound_dispatch',
                      'apply V293_local_storage_resumed_excrit',
                      'apply ret_rule', 'p_local li tid nil',
                      'destruct vl as[ |v vl]', 'BuildPreI', 'BuildRetI',
                      'apply V293_ready_builder_unpack', 'eapply call_rule']:
            self.assertIn(token, src)
        b = read('baseline.json')['files']
        for p in ['framework/logic/inferules.v',
                  'certiucos/v293/proofs/V293OSIntExitExact.v',
                  'certiucos/v293/proofs/V293OSIntExitLocalDispatch.v',
                  'certiucos/v293/proofs/V293ReadyStorageInvariant.v']:
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), b[p])

    def test_same_li_and_original_three_function_bodies(self):
        src = (R / SOURCES['entry']).read_text()
        for token in ['V293_irq_bound_li running nesting lock brun bn bl',
                      'V293_ready_irq_unit unmap group rows high',
                      'eapply V293_OSIntEnter_bound_contract',
                      'eapply V293_OSSchedNew_exact_contract',
                      'eapply V293_OSIntExit_bound_builder_contract']:
            self.assertIn(token, src)
        src = (R / SOURCES['probe']).read_text()
        for token in ['BIprogram=RDprogram', 'LDli=EBli',
                      'BIprogram 300%Z=XIprogram 300%Z',
                      'BIprogram 200%Z=XEprogram 200%Z',
                      'BIbodypost aop ci ==>XEpost aop ci']:
            self.assertIn(token, src)
        doc = (R / 'audit/STAGE240_BOUND_EXIT_BODY.md').read_text()
        for token in ['旧动态三函数环境未迁移', '不是初始化可达',
                      '不是 `WFInt`', '不是 `GOOD_OS`', '不是两次完整执行',
                      '旧423失败、1错误', 'uCOS3 未开始', '不等于逻辑上的 Aemp']:
            self.assertIn(token, doc)

    def test_nonempty_and_literal_bound_return(self):
        src = (R / SOURCES['probe']).read_text()
        for name in ['BIbuilders', 'BIentry_owned', 'BIcall_entry_owned',
                     'BIactual_body', 'BIactual_contract', 'BIactual_call',
                     'BIinternal_environment', 'BIreject_arguments',
                     'BIbody_nonempty', 'BIreturned_local']:
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        for token in ['Definition BIbodypost', 'Definition BIpost',
                      'p_local LDli OwnershipWaiting nil',
                      'apply RBpre_owned', 'apply JBentry_nonempty',
                      'CurLINV LDli OwnershipWaiting',
                      '(scall 300%Z nil)', 'OwnershipReady<>OwnershipWaiting']:
            self.assertIn(token, src)

    def test_independent_trust_and_stable_sources(self):
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
        t = read('trust.json')
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], len(roots))
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in t['commands']))
        self.assertTrue(set(t['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
