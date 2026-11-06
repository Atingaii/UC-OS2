"""结构回归只固定公开边界；数学正确性由真实 Coq 编译与 coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage252-switch-semantic-bridge'
PROD = 'certiucos/v293/proofs/V293SwitchProgSim.v'
PROBE = 'audit/probes/V293SwitchProgSimProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class SwitchProgSimTests(unittest.TestCase):
    def test_protocol_and_unchanged_old_inputs(self):
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

    def test_exhaustive_primitive_and_explicit_simulation_obligations(self):
        src = (R / PROD).read_text()
        self.assertNotIn('CertiOS.audit.', src)
        self.assertNotIn('SWINVt', src)
        for n in ['V293_switch_progress', 'V293_switch_all_successors',
                  'V293_switch_no_output', 'V293_switch_no_abort']:
            self.assertIn(n + ' :', src)
        all_steps = theorem(src, 'V293_switch_all_successors')
        self.assertIn("T'=Tf /\\ cst'=cst /\\ S'=Sf /\\ t'=next", all_steps)
        self.assertIn('inversion H;subst', all_steps)
        main = theorem(src, 'V293_switch_progsim')
        for term in ['hpstepstar ph Th cst O Thf cst Of ->',
                     'ProgSim P Tf Sf ph Thf Of cst next ->',
                     'simulation.prog_sim', 'V293_switch_all_successors',
                     'V293_switch_no_output', 'V293_switch_no_abort']:
            self.assertIn(term, main)
        self.assertNotIn('cofix', main)

    def test_nonempty_same_heap_and_independent_high_post_controls(self):
        src = (R / PROBE).read_text()
        actual = theorem(src, 'SPactual_copy_simulation')
        for term in ['GHactual_copy_obstruction', 'V293_ready_storage_switch_step',
                     'JHswitch_result Mc Mf', '(forall R,~CGstate OwnershipWaiting Mc',
                     'SPschedule', 'SPbridge', 'CGpending', 'SPS Mc enabled ci']:
            self.assertIn(term, actual)
        self.assertIn('hswi_step', theorem(src, 'SPschedule'))
        self.assertIn('RIhighest', theorem(src, 'SPschedule'))
        self.assertIn('SPterminal', theorem(src, 'SPpost'))
        self.assertIn('SPpost', theorem(src, 'SPbridge'))
        self.assertIn('~ProgSim', theorem(src, 'SPzero_high_match_rejected'))
        for key in ['arbitrary_clients', 'same_continuation_prefix_to_switch',
                    'Exit_Sched_environment_migrated', 'WFInt', 'GOOD_OS', 'uCOS3_started']:
            self.assertFalse(read('adversarial-review.json')[key], key)

    def test_all_roots_real_compilation_and_recursive_trust(self):
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
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})

    def test_chinese_bounded_claims_and_preserved_document_tails(self):
        doc = (R / 'audit/STAGE252_SWITCH_SEMANTIC_BRIDGE.md').read_text()
        for term in ['不是任意 client', '不是 `WFInt`', '不是 `GOOD_OS`',
                     'CGpending', 'FCpending', 'K1–K4 未闭合', 'uCOS3 未开始', '未提交／推送']:
            self.assertIn(term, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- switch-semantic-bridge-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
        for p, h in read('adversarial-review.json')['source_sha256'].items():
            self.assertEqual(sha(R / p), h)
