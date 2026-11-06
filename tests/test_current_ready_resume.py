"""结构检查固定接口与边界；数学正确性另由实际 Coq 和递归 coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage253-current-ready-resume'
PROD = 'certiucos/v293/proofs/V293CurrentReadyResume.v'
PROBE = 'audit/probes/V293CurrentReadyResumeProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class CurrentReadyResumeTests(unittest.TestCase):
    def test_protocol_and_original_inputs(self):
        self.assertEqual(sha(D / 'protocol.json'), (D / 'protocol.sha256').read_text().strip())
        base = read('baseline.json')['files']
        for p, h in base.items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md', '_CoqProject']:
                self.assertEqual(sha(R / p), h, p)
        before, after = (R / '_CoqProject').read_bytes().split((PROD + '\n').encode(), 1)
        self.assertEqual(hashlib.sha256(before).hexdigest(), base['_CoqProject'])
        self.assertNotIn((PROD + '\n').encode(), after)
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h, p)

    def test_original_transfer_and_explicit_saved_obligation(self):
        src = (R / PROD).read_text()
        self.assertNotIn('CertiOS.audit.', src)
        self.assertNotIn('IsEnd', src)
        self.assertIn('getie(gettaskst st)=false ->', theorem(src, 'V293_current_off_INV'))
        transfer = theorem(src, 'V293_current_ready_transfer')
        for term in ['getie o=false', 'good_is_S S', 'sched_self V293_scheduler Ol',
                     'SWINVt B t\'', 'merge Mr Ms\'=merge Mc Ms',
                     'merge Or Os\'=merge Ol Os', "eapply swi_rdy_inv'", 'RDYINV G t\'']:
            self.assertIn(term, transfer)
        resume = theorem(src, 'V293_current_resume_saved')
        for term in ['(forall Mr Or,', 'TaskSim pl Cl (RdyChange',
                     'disjoint Mr Mp /\\ disjoint Or Op', 'rdyinv_isremp', 'apply Saved']:
            self.assertIn(term, resume)
        review = read('adversarial-review.json')
        self.assertTrue(review['saved_contract_explicit'])
        self.assertFalse(review['arbitrary_suspended_TaskSim_contract_proved'])
        self.assertFalse(review['global_ProgSim'])
        self.assertTrue(review['typed_probe_frame_is_old_current'])
        self.assertFalse(review['typed_probe_target_private_LINV_proved'])

    def test_typed_nonterminal_enabled_resources_and_negative_control(self):
        src = (R / PROBE).read_text()
        actual = theorem(src, 'CRactual_transfer')
        for term in ['GHactual_copy_obstruction', 'V293_ready_storage_switch_step',
                     'V293_current_ready_transfer', '(forall R,~CGstate OwnershipWaiting Mc',
                     'CRtasks Cl', 'CGpending', 'RDYINV GHinv OwnershipReady', 'JHprivate']:
            self.assertIn(term, actual)
        case = theorem(src, 'CRenabled_nonterminal_transfer')
        self.assertIn('CRtasks CRnonterminal', case)
        self.assertIn('true [0%nat] [false]', case)
        progress = theorem(src, 'CRnonterminal_progress')
        self.assertIn('~IsEnd CRnonterminal', progress)
        self.assertIn('cstep p CRnonterminal', progress)
        self.assertIn('apply sseq_step', progress)
        review = read('adversarial-review.json')
        for key in ['target_code_arbitrary', 'target_ie_unrestricted',
                    'nonterminal_enabled_resource_witness', 'physical_and_abstract_totals_preserved']:
            self.assertTrue(review[key], key)

    def test_real_compiles_and_recursive_trust(self):
        roots = []
        for key, p in [('production', PROD), ('probe', PROBE)]:
            src = (R / p).read_text()
            self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
            row = read(read('stable-compiles.json')[key] + '.json')
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        self.assertEqual(len(roots), 12)
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], 12)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})

    def test_bounded_chinese_claims_and_preserved_tails(self):
        doc = (R / 'audit/STAGE253_CURRENT_READY_RESUME.md').read_text()
        for term in ['不是任意 client', '不是 `WFInt`', '不是 `GOOD_OS`',
                     'TaskSim', '显式', 'CGpending', 'K1–K4 未闭合', 'uCOS3 未开始', '未提交／推送']:
            self.assertIn(term, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- current-ready-resume-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
        review = read('adversarial-review.json')
        for key in ['full_continuation_prefix_to_return', 'WFInt', 'GOOD_OS', 'uCOS3_started']:
            self.assertFalse(review[key], key)
        for p, h in review['source_sha256'].items():
            self.assertEqual(sha(R / p), h)
