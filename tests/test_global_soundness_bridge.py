"""全局soundness的原契约、递归信任边界与单因素对照；不替代具体内核实例。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage343-global-soundness-bridge'
PS = ['certiucos/v293/proofs/V293InitializationPartition.v',
      'certiucos/v293/proofs/V293TraceRefinement.v',
      'certiucos/v293/proofs/V293GlobalSoundness.v']
Q = 'audit/probes/V293GlobalSoundnessProbe.v'
ALLOWED = {'Classical_Prop.classic',
           'FunctionalExtensionality.functional_extensionality_dep'}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class GlobalSoundnessBridgeTests(unittest.TestCase):
    def test_prospective_protocol_and_frozen_gate(self):
        for n in ['protocol', 'regression-plan', 'ablation-plan', 'trace-ablation-plan']:
            self.assertEqual((D / (n + '.sha256')).read_text().split(),
                             [sha(D / (n + '.json')), n + '.json'])
        self.assertTrue(read('protocol.json')['prospective'])
        self.assertEqual(set(read('protocol.json')['allowed']), ALLOWED)
        self.assertFalse(read('regression-plan.json')['gate_waived'])
        diagnostic = read('diagnostic-trust-comparison.json')
        self.assertEqual(diagnostic['before_eqdep_occurrences'], 4)
        self.assertEqual(diagnostic['after_eqdep_occurrences'], 0)
        self.assertFalse(diagnostic['gate_waived'])

    def test_exact_original_contracts_checked_by_kernel(self):
        q = (R / Q).read_text()
        pairs = read('contract-pairs.json') + read('trace-contract-pairs.json')
        self.assertEqual(len(pairs), 9)
        self.assertEqual(q.count('let T := type of '), 9)
        self.assertEqual(q.count('in exact T).'), 9)
        for old, new in pairs:
            self.assertIn('type of ' + old + ' in exact T', q)
            self.assertIn('exact ' + new + '.', q)
        g = (R / PS[2]).read_text().split("Theorem V293_verified_os':", 1)[1]
        for name in ['WFAPI pa apispec', 'WFInt ip intspec', 'WFIFun pi',
                     'side_condition I li', 'GOOD_OS osc A init.']:
            self.assertIn(name, g)
        self.assertIn('GOOD_OS osc A init.', g.split('Theorem V293_Soundness:', 1)[1])

    def test_all_roots_including_primes_and_recursive_check(self):
        roots = [Path(p).stem + '.' + n for p in PS + [Q] for n in
                 re.findall(r"^(?:Lemma|Theorem|Corollary) ([\w']+)\s*:", (R / p).read_text(), re.M)]
        t = read('trust.json')
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 18)
        self.assertEqual(len(roots), 18)
        self.assertIn("V293GlobalSoundness.V293_verified_os'", roots)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in t['commands']))
        self.assertEqual(set(t['allowed']), ALLOWED)
        byroot = read('assumptions-by-root.json')
        self.assertEqual(set(byroot), set(roots))
        self.assertTrue(all(set(v) <= ALLOWED for v in byroot.values()))
        for label, p in zip(['partition', 'trace', 'global', 'probe'], PS + [Q]):
            for i in [1, 2]:
                row = read(f'stable-{label}-{i}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / p))
                self.assertEqual(row['source_sha256'], sha(R / p))
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')

    def test_four_single_dependency_swap_controls_rejected_late(self):
        a = read('ablation.json')
        self.assertEqual({x['label'] for x in a['controls']}, {'init', 'api', 'isr', 'trace'})
        self.assertTrue(a['all_single_swap_controls_rejected'])
        self.assertFalse(a['early_rejection'])
        src = (R / PS[2]).read_text()
        for c in a['controls']:
            pattern = r'((?:eapply |apply |lets Hx: ))' + re.escape(c['swapped_from']) + r"(?![\w'])"
            expected, count = re.subn(pattern, lambda m: m.group(1) + c['swapped_to'], src)
            self.assertEqual(count, c['replacements'])
            saved = D / ('control-' + c['label'] + '.v.snapshot.txt')
            self.assertEqual(saved.read_text(), expected + '\nPrint Assumptions V293_Soundness.\n')
            self.assertEqual(read('control-' + c['label'] + '.json')['exit'], 0)
            self.assertIn('Eqdep.Eq_rect_eq.eq_rect_eq', (D / ('control-' + c['label'] + '.log')).read_text())
            self.assertTrue(c['original_contracts_unchanged'] and c['rejected_by_unchanged_trust_gate'])

    def test_ordinary_induction_and_original_dependency_provenance(self):
        init = (R / PS[0]).read_text()
        trace = (R / PS[1]).read_text()
        self.assertIn('induction H2; intros.', init)
        self.assertNotIn('inductions H2', init)
        self.assertIn('revert lp lt cs os t Heqlw.', trace)
        self.assertIn('induction HLe;', trace)
        self.assertNotIn('inductions HLe', trace)
        for p, h in read('global-provenance.json').items():
            self.assertEqual(sha(R / p), h)
        tr = read('trace-provenance.json')
        self.assertEqual(sha(R / tr['original']), tr['original_sha256'])
        for p in PS:
            self.assertNotIn('Require Import CertiOS.audit.', (R / p).read_text())

    def test_frozen_old_inputs_and_append_only_registration(self):
        self.assertEqual([p for p, h in read('baseline.json').items()
                          if not (R / p).is_file() or sha(R / p) != h], [])
        prev = json.loads((R / 'audit/logs/stage342-soundness-assumption-isolation/checkpoint-evidence-manifest.json').read_text())
        self.assertEqual([p for p, row in prev.items()
                          if p not in {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject'}
                          and sha(R / p) != row['sha256']], [])
        prefix = (D / '_CoqProject.baseline').read_bytes() + ''.join(p + '\n' for p in PS).encode()
        self.assertTrue((R / '_CoqProject').read_bytes().startswith(prefix))
        for p in PS:
            self.assertEqual((R / '_CoqProject').read_text().splitlines().count(p), 1)
        for n in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / n).read_bytes().endswith((D / (n + '.baseline')).read_bytes()))

    def test_conditional_global_bridge_not_concrete_kernel_credit(self):
        e = json.loads((R / 'audit/global-soundness-bridge-evidence-stage343.json').read_text())
        self.assertTrue(e['conditional_global_soundness_accepted'])
        self.assertFalse(e['full_target_linked'])
        self.assertFalse(e['concrete_initialization_supplied'])
        self.assertFalse(e['concrete_WFInt_supplied'])
        self.assertEqual(e['source_identity_sha256'], '74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da')
        self.assertEqual(e['coverage_registration_status'], 'NOT_REGISTERED_IN_LEGACY_AGGREGATE')
        for p, h in e['inputs'].items():
            self.assertEqual(sha(R / p), h)
        doc = (R / 'audit/STAGE343_GLOBAL_SOUNDNESS_BRIDGE.md').read_text()
        for x in ['不是具体内核GOOD_OS', '不是OSInit执行证明', 'WFInt', 'ADR0005',
                  '两个CPU hook', 'K1–K4', 'uCOS3', '总目标保持active', '447']:
            self.assertIn(x, doc)

    def test_adversarial_review_build_and_cache_preservation(self):
        self.assertTrue(read('adversarial-review.json')['completed'])
        self.assertEqual(read('build.json')['exit'], 0)
        self.assertEqual(read('project-audit.json')['exit'], 0)
        restored = read('cache-restoration.json')
        original = read('cache-backups.json')
        self.assertEqual(set(restored['after']), set(original))
        for p, row in original.items():
            self.assertEqual(restored['after'][p], row['sha256'])
