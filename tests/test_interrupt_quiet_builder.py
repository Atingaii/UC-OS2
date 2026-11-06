"""实际 builder quiet 返回的结构回归；语义以 Coq 根检查为准。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage248-quiet-builder-return'
PROD = 'certiucos/v293/proofs/V293InterruptQuietBuilder.v'
PROBE = 'audit/probes/V293InterruptQuietBuilderProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class InterruptQuietBuilderTests(unittest.TestCase):
    def test_protocol_identity_and_project_registration(self):
        self.assertEqual(sha(D / 'protocol.json'), (D / 'protocol.sha256').read_text().strip())
        base = read('baseline.json')['files']
        for p, h in base.items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md', '_CoqProject']:
                self.assertEqual(sha(R / p), h, p)
        project = (R / '_CoqProject').read_bytes()
        self.assertTrue(project.endswith((PROD + '\n').encode()))
        self.assertEqual(hashlib.sha256(project[:-len(PROD) - 1]).hexdigest(), base['_CoqProject'])
        identity = read('source-identity.json')
        self.assertTrue(identity['passed'])
        self.assertFalse(identity['preprocessor_rerun'])
        for p, h in identity['files'].items():
            self.assertEqual(sha(R / p), h, p)

    def test_actual_builder_same_heap_and_original_spec(self):
        src = (R / PROD).read_text()
        body = src.split('Theorem V293_interrupt_quiet_builder_continuous :', 1)[1].split('Qed.', 1)[0]
        statement = body.split('Proof.', 1)[0]
        for term in ['BuildintPre', 'BuildintRet', r'pre //\\ filter', 'intspec i=Some(spec_done None)',
                     'V293_irq_source_wrapper', 'Spec enter=Some(efp,efq', 'Spec exit=Some(xfp,xfq']:
            self.assertIn(term, statement)
        self.assertNotIn('snapshot', statement)
        self.assertNotIn('Room', src)
        self.assertNotIn('Require Import CertiOS.audit.', src)
        opening = src.split('Theorem V293_irq_quiet_builder_open :', 1)[1].split('Qed.', 1)[0]
        for term in ['V293_irq_bound_builder_open', 'V293_irq_controls_unique', 'Controls Filtered']:
            self.assertIn(term, opening)
        call = src.split('Theorem V293_interrupt_bound_quiet_exit_depth :', 1)[1].split('Qed.', 1)[0]
        for term in ['V293_exit_quiet_depth run nest', 'V293_bound_quiet_split',
                     'V293_bound_quiet_combine', 'V293_OSIntExit_bound_dynamic_call']:
            self.assertIn(term, call)

    def test_typed_pair_single_byte_and_negative_control(self):
        src = (R / PROBE).read_text()
        for root in ['QJfiltered_nonempty', 'QJactual_wrapper', 'QJtyped_pair',
                     'QJdepth_pair', 'QJdispatch_filter_rejected', 'QJonly_nesting_changes',
                     'QJliteral_nesting_load', 'QJsaturated_return_nonempty']:
            self.assertRegex(src, r'Theorem ' + root + r'\s*:')
        pair = src.split('Theorem QJtyped_pair :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('JBmemory 1 Int.zero Int.zero', pair)
        self.assertIn('JBmemory 255 Int.zero Int.zero', pair)
        self.assertEqual(pair.count('QCstate M O|=QJpre'), 2)
        unchanged = src.split('Theorem QJonly_nesting_changes :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('(b,off)<>(96%positive,0%Z)', unchanged)
        self.assertIn('OwnershipBytesOutside', unchanged)
        negative = src.split('Theorem QJdispatch_filter_rejected :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('1 0 0 ->~st|=QJfilter', negative)
        self.assertIn('V293_irq_controls_unique', negative)

    def test_compiles_all_roots_and_recursive_trust(self):
        stable = read('stable-compiles.json')
        roots = []
        for key, p in [('production', PROD), ('probe', PROBE)]:
            src = (R / p).read_text()
            self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
            row = read(stable[key] + '.json')
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], 27)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})

    def test_chinese_boundaries_and_historical_tail(self):
        review = read('adversarial-review.json')
        self.assertTrue(review['claims_bounded'])
        for p, h in review['source_sha256'].items():
            self.assertEqual(sha(R / p), h)
        for key in ['boot_reachability', 'two_C_executions', 'claims_kernel_bug',
                    'WFInt', 'GOOD_OS', 'global_invariant_repaired', 'uCOS3_started']:
            self.assertFalse(review[key], key)
        doc = (R / 'audit/STAGE248_QUIET_BUILDER_RETURN.md').read_text()
        for term in ['255', '254', '普通合取', '不是 `WFInt`', '不是初始化可达',
                     '不是 `GOOD_OS`', 'uCOS3 未开始', '旧423失败、1错误',
                     '不是两次 C 执行', '统一抽象规格']:
            self.assertIn(term, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- quiet-builder-return-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
