"""The boundary gate must not infer port or full-function correctness."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('switch_priority_local', ROOT / 'scripts/check-v293-switch-priority.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


class SwitchPriorityLocalTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / CHECK.SOURCE).read_text()

    def test_all_controls_modify_only_one_designated_header(self):
        for name, (changed, declaration) in CHECK.mutations(self.source).items():
            with self.subTest(name=name):
                start = self.source.index(declaration)
                end = self.source.index('Proof.', start)
                self.assertEqual(self.source[:start], changed[:start])
                self.assertEqual(self.source[end:], changed[changed.index('Proof.', start):])

    def test_pointer_control_retains_byte_and_task_postconditions(self):
        changed, _ = CHECK.mutations(self.source)['pointer_store_omitted_only']
        self.assertEqual(changed.replace('    Some V293_priority_boundary_memory /\\',
                                       '    Some V293_priority_boundary_pointer_memory /\\'), self.source)

    def test_byte_control_retains_actual_pointer_store(self):
        changed, _ = CHECK.mutations(self.source)['preserved_byte_wrong_only']
        self.assertEqual(changed.replace('= Some (V293_byteval 12) /\\', '= Some (V293_byteval 4) /\\'), self.source)

    def test_sync_control_retains_successful_store_equation(self):
        changed, decl = CHECK.mutations(self.source)['explicit_sync_omitted_only']
        start = changed.index(decl)
        header = changed[start:changed.index('Proof.', start)]
        self.assertIn('Some V293_priority_boundary_synchronized_memory /\\', header)
        self.assertIn('(V293_priority_boundary_task V293_priority_boundary_pointer_memory)', header)

    def test_assumptions_require_all_five_actual_prints(self):
        output = 'Axioms:\nClassical_Prop.classic : forall P : Prop, P \\/ ~ P\n' * 5
        self.assertEqual(CHECK.checked_assumptions(output), ['Classical_Prop.classic'])
        with self.assertRaises(ValueError):
            CHECK.checked_assumptions(output.rsplit('Axioms:', 1)[0])
        with self.assertRaises(ValueError):
            CHECK.checked_assumptions(output + 'Unapproved.trust : False\n')

    def test_rejection_must_reach_designated_declaration(self):
        candidate, decl = CHECK.mutations(self.source)['explicit_sync_omitted_only']
        path = Path('/tmp/switch-priority-designated.v')
        line = candidate[:candidate.index('Proof.', candidate.index(decl))].count('\n') + 2
        output = f'File "{path}", line {line}, characters 0-1:\nError: type mismatch\n'
        result = CHECK.CHECK.check_rejection(1, output, candidate, decl, path)
        self.assertFalse(result['downstream_credit'])
        for code, altered in [(0, output), (1, output.replace(str(line), '1')), (1, output.replace(str(path), '/tmp/wrong.v'))]:
            with self.assertRaises(ValueError):
                CHECK.CHECK.check_rejection(code, altered, candidate, decl, path)

    def test_probe_is_literal_and_keeps_acceptance_premise(self):
        probe = (ROOT / CHECK.PROBE).read_text()
        self.assertEqual(probe.count('Print Assumptions checked_'), CHECK.ROOT_COUNT)
        self.assertIn('SWINVt I V293_idle_tid ->', probe)
        self.assertIn('~ GoodI I V293_scheduler li :=', probe)
        self.assertNotIn('type of', probe)


# Deliverable-only mutation definitions; no dependency on ignored run logs.
def ready_cache_mutations(source):
    def header(declaration, old, new):
        start = source.index(declaration)
        end = source.index('Proof.', start)
        return (source[:start] + CHECK.CHECK.replace_once(source[start:end], old, new) + source[end:], declaration)
    entry = 'Theorem V293_ready_boundary_entry :'
    switch = 'Theorem V293_ready_boundary_pointer_only :'
    return {
        'entry-cache-wrong-only': header(entry, '= Some (V293_byteval 4) /\\', '= Some (V293_byteval 12) /\\'),
        'switch-target-unchanged-only': header(switch,
            '(6%positive, 0%Z) (Vptr V293_current_next)', '(6%positive, 0%Z) (Vptr V293_idle_tid)'),
        'post-cache-wrong-only': header(switch, '= Some (V293_byteval 4) /\\', '= Some (V293_byteval 12) /\\'),
        'post-coherence-wrong-only': header(switch,
            '~ V293_current_priority_coherent 12%positive', 'V293_current_priority_coherent 12%positive'),
    }


class ReadyCacheCounterexampleTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / CHECK.SOURCE).read_text()
        self.probe = (ROOT / 'audit/probes/V293ReadyCacheCounterexampleProbe.v').read_text()

    def test_actual_ready_entry_and_post_not_hypothetical_acceptance(self):
        for declaration in ['Theorem V293_ready_boundary_entry :', 'Theorem V293_ready_boundary_pointer_only :']:
            start = self.source.index(declaration)
            header = self.source[start:self.source.index('Proof.', start)]
            self.assertNotIn('->', header)
            self.assertIn('SWINVt V293_ready_boundary_inv', header)
        self.assertIn('eapply V293_ready_store;', self.source)
        self.assertIn('eapply store_exist_join\';', self.source)
        self.assertIn('V293_conditional_fixture_physical', self.source)

    def test_live_highest_target_and_real_byte_read_are_retained(self):
        start = self.source.index('Theorem V293_ready_boundary_pointer_only :')
        header = self.source[start:self.source.index('Proof.', start)]
        for fact in ['store (Tptr Tvoid)', 'load Tint8 M\'', 'V293_highest_ready V293_current_tasks',
                     'indom V293_current_tasks V293_idle_tid', '~ V293_current_priority_coherent']:
            self.assertIn(fact, header)
        self.assertIn('eapply load_local;', self.source)
        self.assertIn('eapply mapstoval_load;', self.source)

    def test_probe_restates_invariant_and_relation_with_three_roots(self):
        self.assertEqual(self.probe.count('Print Assumptions checked_'), 3)
        self.assertIn('V293_ready_inv 1%positive', self.probe)
        self.assertIn('load Tint8 (get_mem (get_smem o))', self.probe)
        for alias in ['V293_ready_boundary_inv', 'V293_ready_boundary_task', 'V293_ready_boundary_abs',
                      'V293_current_priority_coherent']:
            self.assertNotIn(alias, self.probe)
        self.assertNotIn('type of', self.probe)

    def test_new_controls_only_modify_one_header_keep_every_proof(self):
        for name, (changed, declaration) in ready_cache_mutations(self.source).items():
            with self.subTest(name=name):
                start = self.source.index(declaration)
                end = self.source.index('Proof.', start)
                self.assertEqual(self.source[:start], changed[:start])
                self.assertEqual(self.source[end:], changed[changed.index('Proof.', start):])
                self.assertNotEqual(self.source[start:end], changed[start:changed.index('Proof.', start)])


if __name__ == '__main__':
    unittest.main()
