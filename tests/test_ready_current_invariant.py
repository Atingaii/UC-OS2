"""切换兼容候选的结构回归；语义以 Coq 和递归信任检查为准。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage249-switch-compatible-current'
PROD = 'certiucos/v293/proofs/V293ReadyCurrentInvariant.v'
PROBE = 'audit/probes/V293ReadyCurrentInvariantProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class ReadyCurrentInvariantTests(unittest.TestCase):
    def test_protocol_fixed_sources_and_registration(self):
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
            self.assertEqual(sha(R / p), h)

    def test_full_goodi_and_exact_same_scheduler(self):
        src = (R / PROD).read_text()
        self.assertNotIn('Require Import CertiOS.audit.', src)
        self.assertNotIn('V293InterruptCommonDispatch', src)
        self.assertNotIn('spec_choice', src)
        guard = src.split('Definition V293_current_guard', 1)[1].split('Definition V293_ready_current_core', 1)[0]
        for term in ['V293_current_task tasks t nc', 'Amapsto(bc,0%Z)Tint8',
                     'V293_highest_ready tasks t', r'\\//']:
            self.assertIn(term, guard)
        self.assertIn(r'payload t tasks events now //\\ V293_current_guard t tasks', src)
        good = src.split('Theorem V293_ready_current_good :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('GoodI V293_ready_current_inv V293_scheduler V293_shared_li.', good)
        for term in ['NoFrame', 'Current', 'Switch', 'Scheduler', 'Live After',
                     'Dead Release', 'Release Mx Ox MM OO Local JM JO', 'SelfFull',
                     'V293_current_switch_highest']:
            self.assertIn(term, good)
        same = src.split('Theorem V293_current_core_same_sched :', 1)[1].split('Qed.', 1)[0]
        statement = same.split('Proof.', 1)[0]
        self.assertIn('sched_self V293_scheduler O', statement)
        self.assertNotIn('V293_current_task', statement)
        for term in ['V293_current_core_guard_frame', 'V293_current_guard_same',
                     'V293_ready_selection_task', 'V293_OSSched_current_target']:
            self.assertIn(term, same)

    def test_typed_ablation_witnesses_and_limits(self):
        src = (R / PROBE).read_text()
        for name in ['SCleft_required_typed', 'SCright_required_typed',
                     'SCall_required_typed', 'SCsame_from_new_core']:
            self.assertRegex(src, r'Theorem ' + name + r'\s*:')
        right = src.split('Theorem SCright_required_typed :', 1)[1].split('Qed.', 1)[0]
        for term in ['SWINVt PPinv OwnershipWaiting', 'SWINVt SCinv OwnershipReady',
                     '~NCcurrent_relation', 'CSswitch_witness', 'V293_byteval 6',
                     'b<>1%positive', 'V293_current_switch_highest']:
            self.assertIn(term, right)
        whole = src.split('Theorem SCall_required_typed :', 1)[1].split('Qed.', 1)[0]
        self.assertEqual(whole.count('|=BCpre'), 2)
        for term in ['NCtyped_single_byte', 'join M4 Mf F4', '~sched_self',
                     'a<>(94%positive,0%Z)', 'SCbad_rejected']:
            self.assertIn(term, whole)
        self.assertIn('BEchanged_same_state', src)

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
        self.assertEqual(trust['roots_printed'], 27)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})

    def test_chinese_claim_boundaries_and_original_tail(self):
        review = read('adversarial-review.json')
        self.assertTrue(review['claims_bounded'])
        self.assertTrue(review['complete_GoodI'])
        for p, h in review['source_sha256'].items():
            self.assertEqual(sha(R / p), h)
        for key in ['boot_reachability', 'two_C_executions', 'claims_kernel_bug',
                    'WFInt', 'GOOD_OS', 'functions_migrated_to_candidate', 'uCOS3_started']:
            self.assertFalse(review[key], key)
        doc = (R / 'audit/STAGE249_SWITCH_COMPATIBLE_CURRENT.md').read_text()
        for term in ['未证明该 Waiting 入口本身满足新 SWINVt', '尚未迁移函数 Hoare 到新候选 Inv',
                     '不是 `WFInt`', '不是初始化可达', '不是 `GOOD_OS`',
                     'uCOS3 未开始', '不是两次 C 执行', '425失败、1错误', '统一抽象规格']:
            self.assertIn(term, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- switch-compatible-current-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
