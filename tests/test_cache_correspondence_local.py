"""Structural regressions for the local two-memory cache correspondence gate."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('cache_correspondence_local', ROOT / 'scripts/check-v293-cache-correspondence.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


class CacheCorrespondenceTests(unittest.TestCase):
    def setUp(self):
        self.comparison = (ROOT / CHECK.COMPARISON).read_text()
        self.boundary = (ROOT / CHECK.BOUNDARY).read_text()
        self.probe = (ROOT / CHECK.PROBE).read_text()

    def test_only_one_address_ignored_not_whole_block(self):
        relation = self.comparison.split('Definition V293_same_except_cache', 1)[1].split('Lemma ', 1)[0]
        self.assertIn('a <> (cache, 0%Z)', relation)
        self.assertIn('get source a = get normalized a', relation)
        self.assertIn('load Tint8 source (cache, 0%Z)', relation)

    def test_synchronized_effect_explicit_not_bare_switch(self):
        theorem = self.comparison.split('Theorem V293_cache_synchronized_store_refinement', 1)[1].split('Qed.', 1)[0]
        self.assertIn('store (Tptr tp) normalized', theorem)
        self.assertIn('store (Tptr tp) source', theorem)
        self.assertIn('store Tint8 source_pointer', theorem)
        self.assertIn('V293_cache_related_storebytes', theorem)
        self.assertIn('get source (cache, 0%Z) = Some (true, old)', theorem)
        self.assertNotIn('Axiom', theorem)

    def test_cross_memory_retains_coherence_real_load_and_no_alias(self):
        theorem = self.comparison.split('Theorem V293_OSSched_cross_memory_comparison', 1)[1].split('Qed.', 1)[0]
        for needle in ['V293_current_task tasks tid nc', 'bh <> bcache',
                       'evalval (evar cached) (ge, le, source)', 'load (Tptr tq) normalized',
                       'V293_OSSched_comparison_decision', 'V293_cache_related_load']:
            self.assertIn(needle, theorem)

    def test_fixture_instantiates_general_correspondence(self):
        theorem = self.boundary.split('Theorem V293_cache_observation_refinement', 1)[1]
        self.assertIn('eapply (V293_OSSched_cross_memory_comparison', theorem)
        self.assertIn('V293_current_tasks V293_current_next 12 V293_current_next', theorem)
        self.assertIn('V293_cache_observation_stores', theorem)

    def test_six_literal_roots_not_candidate_relation_alias(self):
        self.assertEqual(self.probe.count('Print Assumptions checked_'), 6)
        self.assertNotIn('V293_cache_correspondence ', self.probe)
        self.assertNotIn('V293_same_except_cache ', self.probe)
        self.assertIn('eunop oppsite (ebinop oeq (ecast (evar high)', self.probe)
        self.assertIn('Some (Vint32 Int.one)', self.probe)
        self.assertNotIn('type of', self.probe)

    def test_four_single_header_controls_retain_all_proofs(self):
        cases = CHECK.mutations(self.comparison, self.boundary)
        self.assertEqual(len(cases), 4)
        for name, (path, changed, declaration) in cases.items():
            with self.subTest(name=name):
                source = (ROOT / path).read_text()
                start = source.index(declaration)
                end = source.index('Proof.', start)
                self.assertEqual(changed[:start], source[:start])
                self.assertEqual(changed[changed.index('Proof.', start):], source[end:])
                self.assertNotEqual(changed[start:changed.index('Proof.', start)], source[start:end])

    def test_assumption_count_and_unknown_axiom_rejected(self):
        output = 'Axioms:\nClassical_Prop.classic : forall P : Prop, P \\/ ~ P\n' * 6
        self.assertEqual(CHECK.checked_assumptions(output), ['Classical_Prop.classic'])
        for altered in [output.rsplit('Axioms:', 1)[0], output + 'Unapproved.trust : False\n']:
            with self.assertRaises(ValueError):
                CHECK.checked_assumptions(altered)

    def test_negative_rejection_is_file_and_declaration_specific(self):
        _, candidate, declaration = CHECK.mutations(self.comparison, self.boundary)['current-coherence-omitted-only']
        path = Path('/tmp/cache-correspondence-designated.v')
        line = candidate[:candidate.index('Proof.', candidate.index(declaration))].count('\n') + 2
        output = f'File "{path}", line {line}, characters 0-1:\nError: type mismatch\n'
        self.assertFalse(CHECK.CHECK.check_rejection(1, output, candidate, declaration, path)['downstream_credit'])
        for code, altered in [(0, output), (1, output.replace(str(line), '1')),
                              (1, output.replace(str(path), '/tmp/wrong.v'))]:
            with self.assertRaises(ValueError):
                CHECK.CHECK.check_rejection(code, altered, candidate, declaration, path)


if __name__ == '__main__':
    unittest.main()
