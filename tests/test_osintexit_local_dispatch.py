"""检查边界、来源和证据身份；语义正确性由 Coq 与递归 coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage239-bound-exit-dispatch'
SOURCES = {'entry': 'certiucos/v293/proofs/V293OSIntExitLocalDispatch.v',
           'probe': 'audit/probes/V293OSIntExitLocalDispatchProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


class ExitLocalDispatchTests(unittest.TestCase):
    def test_frozen_source_and_prospective_protocol(self):
        s = read('source-check.json')
        self.assertTrue(s['passed'])
        self.assertEqual([x['function']['name'] for x in s['functions']],
                         ['OSIntEnter', 'OSIntExit', 'OS_SchedNew', 'OS_Sched'])
        for x in s['functions']:
            p = D / (x['function']['name'] + '.configured.c.txt')
            self.assertEqual(hashlib.sha256(p.read_bytes()).hexdigest(),
                             x['function']['preprocessed_definition_sha256'])
        for p, h in s['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
        self.assertEqual(s['previous_manifest_sha256'],
                         '4dfca22588067fff351ddd6756c60c72ef6330bb5d17ef5a8f57d45a217b9b45')
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])

    def test_arbitrary_li_is_not_unconditional_transport(self):
        src = (R / SOURCES['entry']).read_text()
        for name in ['V293_local_exit_increment', 'V293_local_exit_copy',
                     'V293_local_exit_handoff', 'V293_local_exit_changed_tail',
                     'V293_OSSched_local_storage_prefix_returned',
                     'V293_OSIntExit_local_dispatch']:
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        for token in ['Variable li:LocalInv.', 'p_local li tid nil',
                      '(px ==> LINV li tid nil ** Atrue)',
                      '(p_local li tid nil ==>p_local V293_shared_li tid nil)',
                      'V293_OSSched_exact_critical_prefix', 'V293_OSSched_counter_increment',
                      'V293_handoff_byte_copy', 'apply V293_ready_exit_close',
                      'eapply switch_rule']:
            self.assertIn(token, src)
        baseline = read('baseline.json')['files']
        for p in ['framework/logic/assertion.v', 'framework/logic/inferules.v',
                  'certiucos/v293/proofs/V293ReadyStorageInvariant.v',
                  'certiucos/v293/code/V293OSIntExit.v',
                  'certiucos/v293/proofs/V293OSIntExitExact.v',
                  'certiucos/v293/proofs/V293InterruptBindings.v']:
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), baseline[p])

    def test_bound_interface_has_no_middle_oracle_or_added_globals(self):
        src = (R / SOURCES['entry']).read_text()
        dispatch = src.split('Theorem V293_OSIntExit_bound_dispatch :', 1)[1].split('Proof.', 1)[0]
        lend = src.split('Theorem V293_exit_bound_body_lend :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(dispatch.count('InfRules'), 1)
        for token in ['==>', 'globals', 'forall j', 'CurLINV', 'GoodI']:
            self.assertNotIn(token, dispatch)
        self.assertEqual(lend.count('==>'), 1)
        for token in ['InfRules', 'globals', 'LINV']:
            self.assertNotIn(token, lend)
        for token in ['bodydata 0 hv out c(Vint32 Int.zero)',
                      'V293_exit_boundary_dispatch table high target current counter sched_id',
                      '(V293_interrupt_handoff high current target)',
                      'apply V293_bound_dispatch_bindings_local',
                      'apply V293_bound_dispatch_forget',
                      'V293_quiet_forget_names', 'V293_bound_dispatch_add_globals',
                      'V293_exit_bound_dispatch_current']:
            self.assertIn(token, src)

    def test_typed_nonempty_fixture_and_explicit_limitations(self):
        src = (R / SOURCES['probe']).read_text()
        for name in ['LDsame_local_invariant', 'LDsame_scheduler_body',
                     'LDscheduler_environment', 'LDbody_lend', 'LDnonempty',
                     'LDactual_dispatch', 'LDresumed_local']:
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        for token in ['LDli=EBli', 'LDprogram 200%Z=XEprogram 200%Z',
                      'JBentry_nonempty 0 c Int.zero ci aop', 's|=LDpre c aop ci',
                      'OwnershipReady<>OwnershipWaiting', ')(LDpost aop ci)OwnershipWaiting',
                      'apply V293_OSIntExit_bound_dispatch', 'CurLINV LDli OwnershipWaiting']:
            self.assertIn(token, src)
        # 旧单因素状态对照只负责入口绑定的鉴别力，不替代新 dispatch 的证明。
        old = R / 'audit/probes/V293InterruptBindingsProbe.v'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(),
                         read('baseline.json')['files'][str(old.relative_to(R))])
        doc = (R / 'audit/STAGE239_BOUND_EXIT_DISPATCH.md').read_text()
        for token in ['不是初始化可达', '不是整个 Exit', '不是 `WFInt`',
                      '不是 `GOOD_OS`', '不是两次完整执行', '旧423失败、1错误',
                      'uCOS3 未开始', '不等于逻辑上的 Aemp', '旧三函数环境未迁移']:
            self.assertIn(token, doc)

    def test_stable_compilation_and_independent_recursive_trust(self):
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
        self.assertTrue(all(x['exit'] == 0 for x in t['commands']))
        self.assertTrue(set(t['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
