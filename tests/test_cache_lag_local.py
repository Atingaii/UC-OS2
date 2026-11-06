"""Structural controls supplement, never replace, actual Coq execution."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('cache_lag_local', ROOT / 'scripts/check-v293-cache-lag.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


class CacheLagTests(unittest.TestCase):
    def setUp(self):
        self.connect = (ROOT / CHECK.CONNECT).read_text()
        self.boundary = (ROOT / CHECK.BOUNDARY).read_text()
        self.probe = (ROOT / CHECK.PROBE).read_text()

    def test_vacated_branch_has_same_ready_relation_not_coherence(self):
        head, proof = self.connect.split('Theorem V293_ready_OSSched_vacated_cache :', 1)[1].split('Proof.', 1)
        self.assertIn('nth nc entries Vnull = Vnull ->', head)
        self.assertNotIn('V293_current_task', head)
        self.assertIn('V293_OSSched_change high current counter (sprim (switch target))', head)
        for name in ['V293_vacated_cache_selection', 'V293_retained_OSSched_storage_prefix_returned',
                     'V293_ready_conditional_change', 'V293_ready_priority_guarded_skip']:
            self.assertIn(name, proof)

    def test_rekey_is_only_explicit_list_effect(self):
        theorem = self.connect.split('Theorem V293_rekey_vacates_cache :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('cached < length entries -> cached <> new ->', theorem)
        self.assertIn('update_nth_val new (update_nth_val cached entries Vnull) (Vptr next)', theorem)
        self.assertNotIn('cstepstar', theorem)

    def test_counter_execution_uses_real_store_and_uint32_add(self):
        theorem = self.boundary.split('Lemma V293_assign_counter_execution :', 1)[1].split('Qed.', 1)[0]
        for needle in ['store Tint32 M', 'Int.add c Int.one', 'sassignend_step', 'evalval_imply_estepstar']:
            self.assertIn(needle, theorem)
        self.assertNotIn('max_unsigned', theorem)  # no no-wrap precondition

    def test_same_pointer_fixture_keeps_counter_and_stops_before_call(self):
        theorem = self.boundary.split('Theorem V293_cache_lag_same_pointer_execution :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('Some (Vint32 Int.one)', theorem)
        self.assertIn('Some (Vint32 Int.zero)', theorem)
        self.assertIn('(curs (scall boundary nil), (kenil, ks))', theorem)
        self.assertIn('V293_OSSched_changed_execution', theorem)
        control = self.boundary.split('Theorem V293_cache_lag_pointer_rewrite_execution :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('(curs (sskip None), (kenil, ks))', control)
        self.assertIn('Int.repr 17', control)
        self.assertNotIn('V293_cache_lag_incremented', control)

    def test_eight_independent_literal_probe_roots(self):
        self.assertEqual(self.probe.count('Print Assumptions checked_'), 8)
        for forbidden in ['type of', 'V293_OSSched_change ', 'V293_OSSched_guards ', 'V293_OSSched_increment ']:
            self.assertNotIn(forbidden, self.probe)
        self.assertIn('eunop oppsite (ebinop oeq (ecast (evar high)', self.probe)
        self.assertIn('sassign (evar counter) (ebinop oplus (evar counter)', self.probe)
        self.assertIn('nth nc entries Vnull = Vnull ->', self.probe)

    def test_four_single_headers_preserve_entire_proof_suffix(self):
        cases = CHECK.mutations(self.connect, self.boundary)
        self.assertEqual(len(cases), 4)
        for label, (path, candidate, declaration) in cases.items():
            with self.subTest(label=label):
                original = (ROOT / path).read_text()
                start = original.index(declaration)
                end = original.index('Proof.', start)
                self.assertEqual(candidate[:start], original[:start])
                self.assertEqual(candidate[candidate.index('Proof.', start):], original[end:])
                self.assertNotEqual(candidate[start:candidate.index('Proof.', start)], original[start:end])

    def test_root_count_and_unknown_assumption_fail_closed(self):
        output = 'Axioms:\nClassical_Prop.classic : forall P : Prop, P \\/ ~ P\n' * 8
        self.assertEqual(CHECK.checked_assumptions(output), ['Classical_Prop.classic'])
        for altered in [output.rsplit('Axioms:', 1)[0], output + 'Unapproved.trust : False\n']:
            with self.assertRaises(ValueError):
                CHECK.checked_assumptions(altered)

    def test_negative_rejection_is_at_designated_file_and_declaration(self):
        _, candidate, declaration = CHECK.mutations(self.connect, self.boundary)['vacated-slot-omitted-only']
        path = Path('/tmp/cache-lag-designated.v')
        line = candidate[:candidate.index('Proof.', candidate.index(declaration))].count('\n') + 2
        output = f'File "{path}", line {line}, characters 0-1:\nError: type mismatch\n'
        self.assertFalse(CHECK.CHECK.check_rejection(1, output, candidate, declaration, path)['downstream_credit'])
        for code, altered in [(0, output), (1, output.replace(str(line), '1')),
                              (1, output.replace(str(path), '/tmp/wrong.v'))]:
            with self.assertRaises(ValueError):
                CHECK.CHECK.check_rejection(code, altered, candidate, declaration, path)


if __name__ == '__main__':
    unittest.main()
