"""真实前缀和闭合反例的结构回归；语义依据为独立 Coq 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage251-current-guard-handoff'
PROD = 'certiucos/v293/proofs/V293CurrentHandoffPrefix.v'
PROBE = 'audit/probes/V293CurrentHandoffPrefixProbe.v'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read(n):
    return json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class CurrentHandoffPrefixTests(unittest.TestCase):
    def test_fixed_protocol_old_inputs_and_append_registration(self):
        self.assertEqual(sha(D / 'protocol.json'), (D / 'protocol.sha256').read_text().strip())
        base = read('baseline.json')['files']
        for p, h in base.items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md', '_CoqProject']:
                self.assertEqual(sha(R / p), h, p)
        project = (R / '_CoqProject').read_bytes()
        before, _ = project.split((PROD + '\n').encode(), 1)
        self.assertEqual(hashlib.sha256(before).hexdigest(), base['_CoqProject'])
        self.assertEqual(project.count((PROD + '\n').encode()), 1)
        identity = read('source-identity.json')
        self.assertTrue(identity['passed'])
        self.assertFalse(identity['preprocessor_rerun'])
        for p, h in identity['files'].items():
            self.assertEqual(sha(R / p), h)

    def test_genuine_generic_inv_prefix_without_claimed_switch_closure(self):
        src = (R / PROD).read_text()
        self.assertNotIn('Require Import CertiOS.audit.', src)
        self.assertIn('Variable RI:Inv.', src)
        prefix = theorem(src, 'V293_current_handoff_prefix')
        for term in ['InfRules Spec V293_scheduler li RI', 'V293_OSSched_increment counter',
                     'sassign(evar current)(evar high)', '(tail nh nh(Int.add c Int.one))',
                     'V293_current_handoff_increment', 'V293_current_handoff_copy']:
            self.assertIn(term, prefix)
        for term in ['SWINVt', 'switch_rule', 'V293_ready_current_inv']:
            self.assertNotIn(term, prefix)
        self.assertIn('V293_OSSched_counter_increment', theorem(src, 'V293_current_handoff_increment'))
        self.assertIn('V293_handoff_byte_copy', theorem(src, 'V293_current_handoff_copy'))
        reject = theorem(src, 'V293_current_handoff_switch_reject')
        for term in ['forall R', '~V293_current_task', '~V293_highest_ready',
                     '~(ge,le,M,ir,aux,O,op)|=SWINVt candidate t ** R',
                     'V293_current_core_guard_frame', 'V293_current_handoff_guard_reject']:
            self.assertIn(term, reject)

    def test_same_typed_actual_copy_and_physical_switch_controls(self):
        src = (R / PROBE).read_text()
        trace = theorem(src, 'GHactual_copy_obstruction')
        for term in ['cstepstar CGprogram', 'store Tint8 M', 'get Mc(b,i)=get M(b,i)',
                     'M(enabled::ci)|=SWINVt GHinv', 'Mc(enabled::ci)|=SWINVt JHinv',
                     '(forall R,~CGstate OwnershipWaiting Mc',
                     '~CGstate OwnershipWaiting Mc(enabled::ci)|=GHguard',
                     'Some(V293_byteval 6)', 'Some(V293_byteval 4)',
                     'CGlocal_ready true', 'V293_handoff_copy_execution', 'GHrejected']:
            self.assertIn(term, trace)
        physical = theorem(src, 'GHphysical_switch_still_works')
        for term in ['JHswitch_result Mc Mf', 'set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady)',
                     'SWINVt GHinv OwnershipReady ** JHprivate',
                     'V293_current_handoff_switch_highest_frame', 'RIhighest']:
            self.assertIn(term, physical)
        self.assertIn('V293_current_handoff_prefix', theorem(src, 'GHprefix_in_new_candidate'))
        self.assertIn('V293_ready_current_good', theorem(src, 'GHcandidate_still_good'))

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
        self.assertEqual(len(roots), 16)
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})

    def test_chinese_bounded_claims_and_unchanged_document_tail(self):
        review = read('adversarial-review.json')
        for key in ['claims_bounded', 'generic_RI_prefix', 'actual_copy_trace',
                    'candidate_pre_switch_closure_refuted', 'candidate_after_physical_switch']:
            self.assertTrue(review[key], key)
        for key in ['all_InfRules_impossible', 'Exit_Sched_environment_migrated',
                    'full_interrupt_return', 'boot_reachability', 'claims_kernel_bug',
                    'WFInt', 'GOOD_OS', 'uCOS3_started']:
            self.assertFalse(review[key], key)
        for p, h in review['source_sha256'].items():
            self.assertEqual(sha(R / p), h)
        doc = (R / 'audit/STAGE251_CURRENT_GUARD_HANDOFF.md').read_text()
        for term in ['不是 `WFInt`', '不是 `GOOD_OS`', 'uCOS3 未开始',
                     '没有证明所有 InfRules 推导不可能', '不是初始化可达',
                     '尚未迁移', '未提交／推送', '任意分离 frame']:
            self.assertIn(term, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- current-guard-handoff-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
