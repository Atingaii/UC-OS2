"""新候选实际入口的结构回归；语义依据是独立 Coq 信任检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage250-current-guard-entry'
PROD = 'certiucos/v293/proofs/V293InterruptCurrentEntry.v'
PROBE = 'audit/probes/V293InterruptCurrentEntryProbe.v'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read(n):
    return json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class InterruptCurrentEntryTests(unittest.TestCase):
    def test_fixed_protocol_old_inputs_and_append_registration(self):
        self.assertEqual(sha(D / 'protocol.json'), (D / 'protocol.sha256').read_text().strip())
        base = read('baseline.json')['files']
        for p, h in base.items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md', '_CoqProject']:
                self.assertEqual(sha(R / p), h, p)
        # 保持历史前缀；允许今后继续追加模块，不冻结整个工程尾部。
        project = (R / '_CoqProject').read_bytes()
        before, after = project.split((PROD + '\n').encode(), 1)
        self.assertEqual(hashlib.sha256(before).hexdigest(), base['_CoqProject'])
        self.assertEqual(project.count((PROD + '\n').encode()), 1)
        identity = read('source-identity.json')
        self.assertTrue(identity['passed'])
        self.assertFalse(identity['preprocessor_rerun'])
        for p, h in identity['files'].items():
            self.assertEqual(sha(R / p), h)

    def test_actual_builder_without_extra_guard_or_inv_transport(self):
        src = (R / PROD).read_text()
        self.assertNotIn('Require Import CertiOS.audit.', src)
        stable = theorem(src, 'V293_interrupt_current_entry')
        statement = stable.split('Proof.', 1)[0]
        for term in ['BuildintPre', 'InfRules Spec sd li V293_irq_current_inv',
                     '(sseq(sprim(eoi id))(scall enter nil))']:
            self.assertIn(term, statement)
        for term in ['V293_current_guard', 'V293_current_task', 'snapshot', 'nest<255']:
            self.assertNotIn(term, statement)
        for term in ['V293_irq_current_builder_open', 'V293_irq_current_prefix']:
            self.assertIn(term, stable)
        prefix = theorem(src, 'V293_irq_current_prefix')
        for term in ['eoi_ieoff_rule', 'V293_OSIntEnter_bound_call',
                     'V293_interrupt_nest_after', 'isrupd(isrupd ir i true)i false']:
            self.assertIn(term, prefix)
        separate = theorem(src, 'V293_current_guard_separate')
        for term in ['load_mono', 'V293_current_guard_same', 'exists m1;exists m2',
                     r'(P //\\ V293_current_guard bc t tasks) ** Q']:
            self.assertIn(term, separate)
        self.assertIn('V293_irq_current_enter_environment', src)
        self.assertIn('V293_OSIntEnter_bound_WFFunEnv', src)
        self.assertIn('V293_OSIntEnter_bound_WFIFun', src)

    def test_typed_actual_entry_and_single_byte_negative_control(self):
        src = (R / PROBE).read_text()
        for name in ['CEbuilder', 'CEfrom_snapshot', 'CEbad_rejected',
                     'CEtyped_entry_nonempty', 'CEtyped_single_byte',
                     'CEactual_entry', 'CEgood_and_enter_environment']:
            theorem(src, name)
        ablation = theorem(src, 'CEtyped_single_byte')
        for term in ['CCstate M O|=CEpre', '~CCstate M4 O|=CEpre',
                     'CCstate M O|=BCpre', 'CCstate M4 O|=BCpre',
                     'join M4 Mf F4', 'CCstate M O|=NCsnapshot 6',
                     'CCstate M4 O|=NCsnapshot 4', 'get F4 a=get(JBmemory',
                     'a<>(94%positive,0%Z)', 'store Tint8 M', 'store Tint8(JBmemory']:
            self.assertIn(term, ablation)
        self.assertIn('V293_irq_current_builder_guard', theorem(src, 'CEbad_rejected'))
        self.assertIn('SCbad_rejected', theorem(src, 'CEbad_rejected'))
        self.assertIn('~V293_highest_ready', theorem(src, 'CEtyped_entry_nonempty'))
        self.assertIn('V293_interrupt_current_entry', theorem(src, 'CEactual_entry'))

    def test_all_new_roots_compiled_and_recursively_checked(self):
        roots = []
        for key, p in [('production', PROD), ('probe', PROBE)]:
            src = (R / p).read_text()
            self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
            row = read(read('stable-compiles.json')[key] + '.json')
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})

    def test_chinese_boundaries_and_unchanged_document_tail(self):
        review = read('adversarial-review.json')
        for key in ['claims_bounded', 'actual_BuildintPre', 'Enter_migrated_to_candidate',
                    'new_Waiting_entry_nonempty', 'complete_GoodI']:
            self.assertTrue(review[key], key)
        for key in ['Exit_Sched_environment_migrated', 'full_interrupt_return',
                    'boot_reachability', 'two_C_executions', 'claims_kernel_bug',
                    'WFInt', 'GOOD_OS', 'uCOS3_started']:
            self.assertFalse(review[key], key)
        for p, h in review['source_sha256'].items():
            self.assertEqual(sha(R / p), h)
        doc = (R / 'audit/STAGE250_CURRENT_GUARD_ENTRY.md').read_text()
        for term in ['不是 `WFInt`', '不是 `GOOD_OS`', 'uCOS3 未开始',
                     '不是两次 C 执行', '不是初始化可达', '尚未迁移',
                     '单函数', '普通合取', '构造辅助', '未提交／推送']:
            self.assertIn(term, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- current-guard-entry-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
