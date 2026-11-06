"""入口关联反例的结构回归；语义有效性由 Coq 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage246-builder-current-counterexample'
P = 'audit/probes/V293InterruptBuilderCurrentCounterexample.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class BuilderCurrentTests(unittest.TestCase):
    def test_prospective_protocol_and_original_sources(self):
        self.assertEqual(sha(D / 'protocol.json'), (D / 'protocol.sha256').read_text().strip())
        base = read('baseline.json')['files']
        for p in ['framework/logic/inferules.v', 'framework/logic/assertion.v',
                  'certiucos/v293/proofs/V293ReadyStorageInvariant.v',
                  'certiucos/v293/proofs/V293InterruptCommonDispatch.v', '_CoqProject']:
            self.assertEqual(sha(R / p), base[p])
        src = read('source-check.json')
        self.assertTrue(src['passed'])
        self.assertEqual(src['previous_manifest_sha256'],
                         '3d3da86d41da60fa6daba447fe3ad5fadc0f38bf54665bf2bd1d0d1e18bf6cb5')
        for p, h in src['files'].items():
            self.assertEqual(sha(R / p), h)
        self.assertEqual(len(src['functions']), 4)

    def test_typed_single_byte_and_same_builder(self):
        src = (R / P).read_text()
        body = src.split('Theorem NCtyped_single_byte :', 1)[1].split('Qed.', 1)[0]
        for token in ['join M Mf(JBmemory', 'join O Of(RIabstract OwnershipWaiting)',
                      'join M4 Mf F4', 'CCstate M O|=BCpre', 'CCstate M4 O|=BCpre',
                      'get M4 a=get M a', 'get F4 a=get(JBmemory',
                      'BEchanged_same_state', 'join_store_join']:
            self.assertIn(token, body)
        self.assertEqual(body.split('Proof.', 1)[0].count('store Tint8'), 2)
        self.assertIn('M4=V293_put_byte M(94%positive,0%Z)4', src)

    def test_positive_negative_and_actual_projection_rejection(self):
        src = (R / P).read_text()
        relation = src.split('Definition NCcurrent_relation', 1)[1].split('Lemma NCabstract', 1)[0]
        for token in ['get(getabst st)curtid', 'get(getabst st)abstcblsid',
                      'load Tint8(getmem st)', 'V293_current_task tasks t n']:
            self.assertIn(token, relation)
        reject = src.split('Theorem NCbuilder_not_current_relation :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('BuildintPre 0 BCintspec', reject)
        self.assertIn('~(forall st,st|=BCpre ->NCcurrent_relation st)', reject)
        factor = src.split('Theorem NCrelation_single_factor :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('NCcurrent_relation(CCstate M O) /\\~NCcurrent_relation(CCstate M4 O)', factor)
        a = read('byte-ablation.json')
        self.assertFalse(a['two_C_executions'] or a['boot_reachability'] or a['claims_kernel_bug'])
        self.assertEqual(a['proof_source_sha256'], sha(R / P))

    def test_independent_check_and_no_new_logical_shortcut(self):
        src = (R / P).read_text()
        self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
        label = read('stable-compiles.json')['probe']
        row = read(label + '.json')
        self.assertEqual(row['exit'], 0)
        self.assertEqual(row['source_sha256'], sha(R / P))
        self.assertEqual(row['initial_source_sha256'], sha(D / (label + '.v.snapshot.txt')))
        roots = ['V293InterruptBuilderCurrentCounterexample.' + n
                 for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        t = read('trust.json')
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 12)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in t['commands']))
        self.assertTrue(set(t['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})

    def test_review_and_chinese_claim_boundaries(self):
        review = read('adversarial-review.json')
        self.assertTrue(review['claims_bounded'])
        self.assertEqual(review['source_sha256'][P], sha(R / P))
        doc = (R / 'audit/STAGE246_BUILDER_CURRENT_COUNTEREXAMPLE.md').read_text()
        for text in ['不是两次完整 C 执行', '不是初始化可达', '不是 `WFInt`',
                     '不是 `GOOD_OS`', 'uCOS3 未开始', '旧423失败、1错误', 'GoodI']:
            self.assertIn(text, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- builder-current-counterexample-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
