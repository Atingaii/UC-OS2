"""结构和来源回归；证明结论由独立 Coq 检查，不以文本命中代替。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage241-bound-exit-dynamic'
SOURCES = {'entry': 'certiucos/v293/proofs/V293OSIntExitBoundDynamic.v',
           'probe': 'audit/probes/V293OSIntExitBoundDynamicProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


class BoundDynamicTests(unittest.TestCase):
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
                         '46e6a72fb4055d1c42eb1ce5c3f700fbee519b7ab526a9071edb7be746ef1c7a')
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])

    def test_body_contracts_and_same_li_embedding(self):
        src = (R / SOURCES['entry']).read_text()
        for name in ['V293_OSIntExit_bound_dynamic_contract',
                     'V293_OSIntExit_bound_dynamic_call',
                     'V293_bound_dynamic_WFFunEnv', 'V293_bound_dynamic_WFIFun']:
            header = src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]
            self.assertLessEqual(header.count('InfRules'), 1)
            self.assertNotIn('==>', header)
            self.assertNotIn('CurLINV', header)
        for token in ['V293_OSIntExit_bound_builder_contract',
                      'V293_OSIntExit_quiet_exact_builder_contract',
                      'V293_OSIntExit_same_exact_builder_contract',
                      'V293_exact_critical_to_all_joint', 'V293_exact_ISR_to_all_joint',
                      'V293_exit_handoff_void_calls', 'eapply call_rule']:
            self.assertIn(token, src)
        b = read('baseline.json')['files']
        for p in ['framework/logic/inferules.v',
                  'certiucos/v293/proofs/V293OSIntExitBoundInternal.v',
                  'certiucos/v293/proofs/V293OSIntExitQuietExact.v',
                  'certiucos/v293/proofs/V293OSIntExitSameExactInternal.v',
                  'certiucos/v293/proofs/V293OSIntExitAllExactDynamic.v']:
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), b[p])

    def test_three_function_environment_and_bounded_claims(self):
        src = (R / SOURCES['entry']).read_text()
        for token in ['V293_irq_bound_li running nesting lock brun bn bl',
                      'V293_ready_irq_unit unmap group rows high',
                      'eapply V293_OSIntEnter_bound_contract',
                      'eapply(V293_OSSchedNew_all_exact_joint_contract',
                      'eapply V293_OSIntExit_bound_dynamic_contract']:
            self.assertIn(token, src)
        doc = (R / 'audit/STAGE241_BOUND_EXIT_DYNAMIC.md').read_text()
        for token in ['候选 Enter', '不是初始化可达', '不是 `WFInt`',
                      '不是 `GOOD_OS`', '不是两次完整执行', '旧423失败、1错误',
                      'uCOS3 未开始', '不等于逻辑上的 Aemp', '两套地址实例',
                      'BuildRetI 本身不检查实参个数']:
            self.assertIn(token, doc)

    def test_nonempty_literals_calls_and_controls(self):
        src = (R / SOURCES['probe']).read_text()
        for name in ['BDbuilders', 'SDbuilders', 'BDenvironment', 'SDenvironment',
                     'BDactual_contract', 'SDactual_contract', 'BDactual_call', 'SDactual_call',
                     'BDchanged_literal', 'BDquiet_literal', 'SDliteral',
                     'BDchanged_nonempty', 'BDquiet_nonempty', 'SDnonempty',
                     'BDcall_nonempty', 'BDreturned_local', 'SDreturned_local',
                     'BDquiet_return_forget', 'SDreturn_forget',
                     'BDinvalid_paths', 'BDreject_arguments', 'BDruntime_control']:
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        for token in ['Definition BDqexternal', 'Definition SDexternal',
                      'apply Qentry_nonempty', 'apply SEentry_nonempty',
                      'apply RBpre_owned', 'V293_bound_dispatch_add_globals',
                      '(scall 300%Z nil)', 'RDprogram 300%Z=XIprogram 300%Z']:
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
