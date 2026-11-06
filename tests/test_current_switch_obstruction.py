"""切换关联障碍的结构回归；语义结论以 Coq 检查为准。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage247-current-switch-obstruction'
P = 'audit/probes/V293CurrentSwitchObstruction.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class CurrentSwitchObstructionTests(unittest.TestCase):
    def test_prospective_protocol_and_fixed_sources(self):
        self.assertEqual(sha(D / 'protocol.json'), (D / 'protocol.sha256').read_text().strip())
        base = read('baseline.json')['files']
        for p in ['framework/logic/inferules.v', '_CoqProject',
                  'audit/probes/V293ReadyStorageInvariantProbe.v',
                  'audit/probes/V293InterruptBuilderCurrentCounterexample.v',
                  'certiucos/v293/proofs/V293ReadyStorageInvariant.v']:
            self.assertEqual(sha(R / p), base[p])
        src = read('source-check.json')
        self.assertEqual(src, read('source-recheck.json'))
        self.assertTrue(src['passed'])
        self.assertEqual(src['previous_manifest_sha256'],
                         'c9972820a598acf15de2f3d9229d9c31822122b85c431b25f544453009fa4fa7')
        self.assertEqual(len(src['functions']), 4)
        for p, h in src['files'].items():
            self.assertEqual(sha(R / p), h)

    def test_nonempty_typed_fragment_and_observable_store(self):
        src = (R / P).read_text()
        body = src.split('Theorem CSswitch_witness :', 1)[1].split('Qed.', 1)[0]
        for token in ['PPnonempty false nil', 'sat_split', 'JM&JO',
                      'join_get_get_l', 'load_mem_mono', 'V293_ready_current_write',
                      'V293_ready_storage_store_frame', 'V293_load_block_frame',
                      'NCcurrent_relation(CSstate M O)',
                      '~NCcurrent_relation(CSstate Mf',
                      'get Mf(b,off)=get M(b,off)']:
            self.assertIn(token, body)
        statement = body.split('Proof.', 1)[0]
        self.assertEqual(statement.count('load Tint8'), 2)
        self.assertEqual(statement.count('store(Tptr'), 1)
        self.assertNotIn('store Tint8', body)

    def test_arbitrary_candidate_closure_with_two_hypotheses(self):
        src = (R / P).read_text()
        theorem = src.split('Theorem CSexact_strengthening_not_GoodI :', 1)[1].split('Qed.', 1)[0]
        for token in ['forall Inv0 li,', 'SWINVt PPinv OwnershipWaiting',
                      'forall t st,st|=SWINVt Inv0 t ->NCcurrent_relation st',
                      '~GoodI Inv0 V293_scheduler li', '[_[_[Switch _]]]',
                      'destruct(Switch', 'Includes _ H Before',
                      'Coherent OwnershipReady', 'apply Dead;exists']:
            self.assertIn(token, theorem)
        a = read('ablation.json')
        self.assertEqual(len(a['candidate_hypotheses']), 2)
        self.assertTrue(a['original_GoodI'] and a['exact_strengthening_ruled_out'])
        self.assertFalse(a['all_possible_invariants_ruled_out'] or a['boot_reachability'] or a['claims_kernel_bug'])
        self.assertEqual(a['proof_source_sha256'], sha(R / P))

    def test_positive_control_import_ablation_and_independent_check(self):
        src = (R / P).read_text()
        self.assertIn('Theorem CSwithout_strengthening_good : GoodI PPinv V293_scheduler V293_shared_li.', src)
        self.assertIn('Proof. exact PPgood. Qed.', src)
        self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
        stable = read('stable-compiles.json')
        row = read(stable['probe'] + '.json')
        self.assertEqual(row['exit'], 0)
        self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
        self.assertEqual(row['source_sha256'], sha(R / P))
        old = (D / 'probe10.v.snapshot.txt').read_text()
        self.assertEqual(old.split('Definition CSstate', 1)[1], src.split('Definition CSstate', 1)[1])
        self.assertEqual(read('probe11.json')['exit'], 1)
        self.assertEqual(len(stable['import_ablation']['removed']), 1)
        roots = ['V293CurrentSwitchObstruction.' + n
                 for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], 6)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})

    def test_chinese_claim_boundaries_and_review(self):
        review = read('adversarial-review.json')
        self.assertTrue(review['claims_bounded'])
        self.assertEqual(review['source_sha256'][P], sha(R / P))
        doc = (R / 'audit/STAGE247_CURRENT_SWITCH_OBSTRUCTION.md').read_text()
        for text in ['不是所有可能 Inv 不存在', '不是初始化可达', '不是 `WFInt`',
                     '不是 `GOOD_OS`', 'uCOS3 未开始', '旧423失败、1错误',
                     'PPactual_switch', '第三子句', '两个假设']:
            self.assertIn(text, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- current-switch-obstruction-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
