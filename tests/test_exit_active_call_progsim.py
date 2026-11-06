"""条件接口和证据边界；Coq/coqchk 才检查证明有效性。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage265-exit-active-call-progsim'
PROD = 'certiucos/v293/proofs/V293ExitActiveCallProgSim.v'
PROBE = 'audit/probes/V293ExitActiveCallProgSimProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class ExitActiveCallProgSimTests(unittest.TestCase):
    def test_stable_call_boundary_has_only_final_simulation(self):
        src = (R / PROD).read_text()
        body = theorem(src, 'V293_exit_active_call_progsim')
        self.assertEqual(body.split('Proof.', 1)[0].count('ProgSim'), 2)
        for term in ['forall bs,fresh M bs', 'entry=sfexec f nil nil', 'entry=scall f nil',
                     'V293_saved_call_entry_progsim', 'V293_exit_active_body_prefix_progsim',
                     'V293_exit_call_resume_progsim', 'free Tint32 nextbs Msw=Some Mret',
                     'set(set les t(V293_cpu_lenv saved bs))next nextcaller',
                     'set(set aus t(false,si,false::cs))next(false,nsi,ncs)']:
            self.assertIn(term, body)
        self.assertNotIn('CertiOS.audit.', src)
        self.assertIn('Hypothesis Pending:get T next=', src)
        self.assertIn('Hypothesis Match:hpstepstar', src)
        self.assertIn('Hypothesis Active:n<=1.', src)
        self.assertIn(PROD, (R / '_CoqProject').read_text().splitlines())
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h)

    def test_outer_prefix_executes_running_critical_and_nesting(self):
        src = (R / PROD).read_text()
        body = theorem(src, 'V293_exit_active_body_prefix_progsim')
        for term in ['store Tint32 M(bs,0%Z)', 'V293_assign_word_progsim',
                     'evalval(V293_OSIntEnter_running running)', 'Some(Vint32 Int.one)',
                     'V293_exit_ifthen_progsim', 'V293_exit_active_critical_prefix_progsim']:
            self.assertIn(term, body)
        body = theorem(src, 'V293_exit_active_critical_prefix_progsim')
        for term in ['V293_encrit_progsim', 'V293_exit_nesting_progsim',
                     '(locked:=0)', '(cs:=false::cs)', 'V293_exit_enabled_iff']:
            self.assertIn(term, body)

    def test_fresh_saved_real_assignment_and_other_block_frame(self):
        src = (R / PROBE).read_text()
        body = theorem(src, 'APfresh_storage')
        self.assertNotIn('ProgSim', body)
        for term in ['forall M bs target', 'fresh M bs', 'bs<>target',
                     'V293_success_fresh_none', 'V293_success_scheduler_storage',
                     'V293_success_assign_zero', 'V293_load_block_frame',
                     'free Tint32 bs Ms=Some M', 'get Ms(c,i)=get M(c,i)']:
            self.assertIn(term, body)
        body = theorem(src, 'APtyped_resource_family')
        for term in ['n=1 \\/ n=2', 'CPtyped_updated', 'bs<>98%positive',
                     'APfresh_storage', 'load Tint32 Ms(98%positive,0%Z)', 'CPother']:
            self.assertIn(term, body)

    def test_single_factor_nesting_control_is_actual_execution(self):
        body = theorem((R / PROBE).read_text(), 'APnesting_control')
        self.assertNotIn('ProgSim', body)
        self.assertEqual(body.split('Proof.', 1)[0].count('cstepstar'), 2)
        for term in ['(b,i)<>(96%positive,0%Z)', 'get(NPinitial 1)(b,i)=get(NPinitial 2)(b,i)',
                     '(curs dispatch,(kenil,ks))(CGge,CGle,CEM)',
                     '(SKIP,(kenil,ks))(CGge,CGle,NPinitial 1)',
                     'V293_exit_one_decrement_execution', 'V293_exit_zero_guards_enter',
                     'V293_OSIntExit_nested_middle_execution']:
            self.assertIn(term, body)

    def test_stable_compiles_trust_and_honest_limits(self):
        self.assertEqual(sha(D / 'protocol.json'), (D / 'protocol.sha256').read_text().strip())
        stable = read('stable-compiles.json')
        roots = []
        for key, p in [('production', PROD), ('probe', PROBE)]:
            src = (R / p).read_text()
            self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
            row = read(stable[key] + '.json')
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['source_sha256'], row['initial_source_sha256'])
            self.assertEqual(row['source_sha256'], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        for label in stable['repeat_passes']:
            self.assertEqual(read(label + '.json')['exit'], 0)
        trust = read('trust.json')
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertEqual(len(roots), 6)
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']),
                             {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertEqual(read('build.json')['exit'], 0)
        doc = (R / 'audit/STAGE265_EXIT_ACTIVE_CALL_PROGSIM.md').read_text()
        for term in ['不是 `GOOD_OS`', '不是 `WFInt`', 'IE=false', 'ADR-0010',
                     'K1–K4 未闭合', 'uCOS3 未开始', '未提交／推送', 'high=88',
                     '最终 caller 端点模拟', '不能把本步', '不是独立完整函数实例',
                     '守卫拒绝不能证明下游', '每个任意 fresh 分配结果']:
            self.assertIn(term, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- exit-active-call-progsim-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
