"""固定有限 client 的接口与声明边界；数学检查由实际 Coq/coqchk 完成。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage254-nonterminal-saved-contract'
PROD = 'certiucos/v293/proofs/V293ClientSkipTaskSim.v'
PROBE = 'audit/probes/V293ClientSkipTaskSimProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class ClientSkipTaskSimTests(unittest.TestCase):
    def test_protocol_and_fixed_original_inputs(self):
        self.assertEqual(sha(D / 'protocol.json'), (D / 'protocol.sha256').read_text().strip())
        for p, h in read('baseline.json')['files'].items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md', '_CoqProject']:
                self.assertEqual(sha(R / p), h, p)
        before, after = (R / '_CoqProject').read_bytes().split((PROD + '\n').encode(), 1)
        self.assertEqual(hashlib.sha256(before).hexdigest(), read('baseline.json')['files']['_CoqProject'])
        self.assertNotIn((PROD + '\n').encode(), after)
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h, p)

    def test_original_seven_obligations_and_no_saved_hypothesis(self):
        src = (R / PROD).read_text()
        self.assertNotIn('CertiOS.audit.', src)
        sim = theorem(src, 'V293_skip_client_TaskSim')
        self.assertEqual(sim.count('\n - '), 7)
        for term in ['cofix CIH', 'apply task_sim', 'V293_skip_client_match_low',
                     'V293_skip_client_no_low_event', 'V293_skip_client_match_abort',
                     'InitTaskSt li t', 'exact Init', 'exact Local']:
            self.assertIn(term, sim)
        for name in ['V293_skip_client_match_low', 'V293_skip_client_match_high',
                     'V293_skip_client_match_abort']:
            self.assertIn(name + ' :', src)
        saved = theorem(src, 'V293_skip_client_saved')
        self.assertIn('LINV li t init_lg', saved)
        self.assertIn('eapply crt_init', saved)
        resume = theorem(src, 'V293_current_skip_resume')
        statement = resume.split('Proof.', 1)[0]
        self.assertEqual(statement.count('TaskSim'), 1)
        self.assertNotIn('Saved', statement)
        self.assertIn('(true,nil,nil)', statement)
        self.assertIn('apply V293_skip_client_saved', resume)
        self.assertTrue(read('adversarial-review.json')['saved_assumption_removed_for_selected_client'])

    def test_actual_copy_switch_init_local_sim_and_separate_controls(self):
        src = (R / PROBE).read_text()
        actual = theorem(src, 'CSactual_resume')
        for term in ['GHactual_copy_obstruction', 'V293_ready_storage_switch_step',
                     'V293_current_skip_resume', '(forall R,~CGstate OwnershipWaiting Mc',
                     'CGpending', 'OldPrivateM', 'PrivateTarget',
                     'LINV V293_shared_li OwnershipReady init_lg', 'InitTaskSt', 'CurLINV',
                     'TaskSim', 'INV GHinv', 'RDYINV GHinv OwnershipReady']:
            self.assertIn(term, actual)
        self.assertIn('~IsEnd V293_skip_client_code', theorem(src, 'CSnonterminal_progress'))
        self.assertIn('si=nil /\\ cs=nil', theorem(src, 'CSinit_requires_clear_stacks'))
        self.assertIn('(true,cons 0%nat nil,nil)', theorem(src, 'CSinterrupted_target_not_initial'))
        self.assertIn('(true,nil,cons false nil)', theorem(src, 'CScritical_target_not_initial'))
        review = read('adversarial-review.json')
        self.assertTrue(review['typed_probe_frame_is_old_current'])
        self.assertTrue(review['typed_probe_target_private_LINV_proved'])
        self.assertFalse(review['arbitrary_interrupted_target'])

    def test_actual_compiles_and_recursive_trust(self):
        roots = []
        for key, p in [('production', PROD), ('probe', PROBE)]:
            src = (R / p).read_text()
            self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
            c = read(read('stable-compiles.json')[key] + '.json')
            self.assertEqual(c['exit'], 0)
            self.assertEqual(c['initial_source_sha256'], c['source_sha256'])
            self.assertEqual(c['source_sha256'], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        self.assertEqual(len(roots), 18)
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], 18)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})

    def test_chinese_claim_boundaries_and_preserved_tails(self):
        doc = (R / 'audit/STAGE254_NONTERMINAL_SAVED_CONTRACT.md').read_text()
        for term in ['不是任意 client', '不是 `WFInt`', '不是 `GOOD_OS`',
                     'CGpending', 'K1–K4 未闭合', 'uCOS3 未开始', '未提交／推送', '七项义务']:
            self.assertIn(term, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- nonterminal-saved-contract-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
        review = read('adversarial-review.json')
        for key in ['arbitrary_clients', 'arbitrary_suspended_TaskSim_contract_proved',
                    'full_continuation_prefix_to_return', 'global_ProgSim', 'WFInt', 'GOOD_OS', 'uCOS3_started']:
            self.assertFalse(review[key], key)
        for p, h in review['source_sha256'].items():
            self.assertEqual(sha(R / p), h)
