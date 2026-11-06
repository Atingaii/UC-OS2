"""Contract tests for the local connected-segment check, not full kernel credit."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('storage_connect_local', ROOT / 'scripts/check-v293-storage-connect.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


class StorageConnectLocalTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / CHECK.SOURCE).read_text()
        self.probe = (ROOT / CHECK.PROBE).read_text()

    def test_increment_control_changes_only_designated_program(self):
        changed, declaration = CHECK.mutations(self.source)['increment_omitted_only']
        start = self.source.index(declaration)
        end = self.source.index('Proof.', start)
        self.assertEqual(changed[:start], self.source[:start])
        self.assertEqual(changed[changed.index('Proof.', start):], self.source[end:])
        self.assertIn('(V293_storage_connected_tail next (Int.add c Int.one))', changed[start:end])
        self.assertEqual(changed.replace('(sskip None)', '(V293_OSSched_increment counter)'), self.source)

    def test_physical_control_retains_same_state_metadata_and_invariant(self):
        changed, declaration = CHECK.mutations(self.source)['physical_projection_forgotten_only']
        self.assertEqual(declaration, 'Lemma V293_storage_connected_prefix_open :')
        body = changed.split('assert (HO :', 1)[1].split('clear H.', 1)[0]
        self.assertIn('SWINV (V293_storage_inv cells target tp)', body)
        self.assertIn('CurTid tid ** V293_shared_fields tid tasks events now', body)
        self.assertIn('GV target @ (Tptr tp) |-> (Vptr next)', body)
        self.assertNotIn('V293_prefix_physical', body)
        self.assertIn('//'+chr(92)*2, body)
        self.assertEqual(changed.split('Proof.', 1)[0], self.source.split('Proof.', 1)[0])

    def test_return_control_changes_only_reassembly_step(self):
        changed, declaration = CHECK.mutations(self.source)['arrays_not_returned_only']
        self.assertEqual(declaration, 'Lemma V293_storage_connected_return :')
        self.assertEqual(changed.replace('[intros st H; exact H | intros st H; exact H]. }',
            '[intros st H; exact H | apply V293_prefix_physical_return; assumption]. }', 1), self.source)
        self.assertEqual(set(CHECK.mutations(self.source)), {
            'increment_omitted_only', 'physical_projection_forgotten_only', 'arrays_not_returned_only',
            'exact_priority_forgotten_only', 'conditional_increment_omitted_only',
            'conditional_exactness_forgotten_only', 'equal_sched_not_consumed_only',
            'outer_guard_omitted_only', 'inner_guard_omitted_only', 'guard_exactness_forgotten_only',
            'ready_increment_omitted_only', 'ready_switch_omitted_only', 'ready_relation_erased_on_return_only',
            'ready_conditional_increment_omitted_only', 'ready_conditional_switch_omitted_only',
            'ready_conditional_current_byte_forgotten_only', 'ready_conditional_current_task_omitted_only'})

    def test_exactness_control_changes_only_closed_observation(self):
        changed, declaration = CHECK.mutations(self.source)['exact_priority_forgotten_only']
        self.assertEqual(declaration, 'Theorem V293_storage_priority_comparison :')
        self.assertEqual(changed.replace('lo hi entries extra (V293_storage extra) tid',
            'lo hi entries extra V293_priority_kept tid'), self.source)
        self.assertEqual(changed.split('Definition V293_priority_closed :=')[0],
                         self.source.split('Definition V293_priority_closed :=')[0])
        self.assertIn('PV (bcur, Int.zero) @ Tint8 |-> (V293_byteval nc)', self.probe)
        self.assertIn('eunop oppsite (ebinop oeq (ecast (evar high) Tint32)', self.probe)
        self.assertIn('Print Assumptions checked_priority_comparison.', self.probe)

    def test_priority_witness_control_changes_only_encoded_value(self):
        source = (ROOT / CHECK.WITNESS).read_text()
        changed, declaration = CHECK.witness_mutation(source)
        self.assertEqual(declaration, 'Theorem V293_storage_priority_entry_witness :')
        self.assertEqual(changed.replace('(encode_val Tint8 (V293_byteval 0))',
            '(encode_val Tint8 (V293_byteval (V293_current_mode_priority different)))', 1), source)
        self.assertIn('V293_current_task (V293_current_mode_tasks different)', changed)
        self.assertIn('s |= V293_priority_entry', changed)
        self.assertIn('V293_priority_fixture_memory (different : bool)', changed)

    def test_conditional_increment_control_preserves_condition_and_switch(self):
        changed, declaration = CHECK.mutations(self.source)['conditional_increment_omitted_only']
        self.assertEqual(declaration, 'Theorem V293_conditional_change :')
        self.assertEqual(changed.replace(
            '(sifthen (V293_OSSched_different high current) (sseq (sskip None) (sprim (switch target))))',
            '(V293_OSSched_change high current counter (sprim (switch target)))'), self.source)

    def test_conditional_exactness_control_changes_only_closed_observation(self):
        changed, declaration = CHECK.mutations(self.source)['conditional_exactness_forgotten_only']
        self.assertEqual(declaration, 'Theorem V293_conditional_comparison :')
        self.assertEqual(changed.replace('lo hi entries extra (V293_storage extra) tid',
            'lo hi entries extra V293_conditional_kept tid', 1), self.source)
        self.assertIn('((bcounter, 0%Z), Tint32) :: ((bcur, 0%Z), Tint8) :: rest.', self.probe)

    def test_conditional_comparison_precedes_the_exact_snapshot_forget_consumer(self):
        # Otherwise the exactness control dies in an unrelated consumer before
        # reaching the designated physical-comparison obligation.
        self.assertLess(self.source.index('Theorem V293_conditional_comparison :'),
                        self.source.index('Lemma V293_conditional_forget :'))

    def test_equal_control_removes_only_abstract_schedule(self):
        changed, declaration = CHECK.mutations(self.source)['equal_sched_not_consumed_only']
        self.assertEqual(declaration, 'Lemma V293_self_schedule_consume :')
        start = self.source.index(declaration)
        end = self.source.index('Qed.', start)
        self.assertEqual(changed[:start], self.source[:start])
        self.assertEqual(changed[changed.index('Qed.', start):], self.source[end:])
        self.assertEqual(changed[start:changed.index('Qed.', start)].count("apply absinfer_eq'."), 1)

    def test_combined_witness_control_changes_only_physical_current(self):
        source = (ROOT / CHECK.WITNESS).read_text()
        changed, declaration = CHECK.conditional_witness_mutation(source)
        self.assertEqual(declaration, 'Theorem V293_storage_conditional_entry_witness :')
        start = source.index('Definition V293_conditional_priority_memory')
        end = source.index(declaration, start)
        self.assertEqual(changed[:start], source[:start])
        self.assertEqual(changed[changed.index(declaration, start):], source[end:])
        self.assertEqual(changed[start:changed.index(declaration, start)].replace(
            '(encode_val Tint8 (V293_byteval 0))',
            '(encode_val Tint8 (V293_byteval (V293_current_mode_priority different)))'), source[start:end])
        self.assertIn('V293_conditional_counter_memory c', changed)
        self.assertIn('Print Assumptions checked_conditional.', self.probe)
        self.assertIn('checked_conditional_entry_witness', self.probe)

    def test_literal_program_and_non_frozen_resumed_interface(self):
        self.assertIn('(sseq (sseq (scall sched_id nil) (sassign (evar target) (earrayelem (evar table) (evar high))))', self.probe)
        self.assertIn('(sseq (sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))', self.probe)
        self.assertIn('(sprim (switch target))))', self.probe)
        resumed = self.probe.split('Let resumed :=', 1)[1].split('Let snapshot', 1)[0]
        self.assertIn('<||aop||> ** SWINVt (V293_storage_inv cells target tp) tid', resumed)
        self.assertNotIn('next', resumed)
        self.assertNotIn('Int.add', resumed)
        for alias in ['V293_prefix_cells', 'V293_storage_connected_tail', 'V293_storage_connected_resumed',
                      'V293_storage_prefix_entry', 'V293_storage_prefix_closed']:
            self.assertNotIn(alias, self.probe)
        self.assertEqual(self.probe.count('Print Assumptions '), CHECK.ROOT_COUNT)

    def test_counter_storage_and_bindings_are_not_duplicated_ownership(self):
        self.assertIn('Let extra := ((bcounter, 0%Z), Tint32) :: rest.', self.probe)
        locals_ = self.probe.split('Let locals :=', 1)[1].split('Let payload', 1)[0]
        self.assertIn('V293_counter_bindings counter bcounter', locals_)
        self.assertNotIn('PV', locals_)
        self.assertNotIn('V293_storage ', locals_)
        self.assertNotIn('checked_array', locals_)

    def test_constructed_witness_has_real_arbitrary_uint32_and_two_modes(self):
        witness = (ROOT / CHECK.WITNESS).read_text()
        self.assertIn('forall different c events now aop,', witness)
        self.assertIn('encode_val Tint32 (Vint32 c)', witness)
        self.assertIn('merge (V293_storage_prefix_memory different) (V293_connect_counter_memory c)', witness)
        self.assertIn('[((12%positive, 0%Z), Tint32)]', witness)
        self.assertIn('V293_counter_bindings 108%Z 12%positive ** Aemp', witness)
        self.assertIn('exists s.', witness)
        self.assertNotIn('False ->', witness)

    def test_actual_assumption_output_requires_all_roots_and_allowlist(self):
        valid = ('Axioms:\nClassical_Prop.classic : forall P : Prop, P \\/ ~ P\n'
                 'FunctionalExtensionality.functional_extensionality_dep\n  : forall A : Type, A = A\n')
        self.assertEqual(len(CHECK.checked_assumptions(valid * CHECK.ROOT_COUNT)), 2)
        for changed in [valid * (CHECK.ROOT_COUNT - 1), valid * CHECK.ROOT_COUNT + 'Bad.evil : False\n']:
            with self.assertRaises(ValueError):
                CHECK.checked_assumptions(changed)

    def test_rejection_must_be_inside_exact_designated_proof_and_file(self):
        changed, declaration = CHECK.mutations(self.source)['increment_omitted_only']
        line = changed[:changed.index(declaration)].count('\n') + 1
        path = Path('/tmp/connect-test/V293OSSchedStorageConnect.v')
        message = f'File "{path}", line {line}, characters 0-1:\nError: mismatch\n'
        result = CHECK.check_rejection(1, message, changed, declaration, path)
        self.assertFalse(result['downstream_credit'])
        for code, output in [(0, message), (124, message), (1, message.replace(f'line {line}', 'line 1')),
                             (1, message.replace(str(path), '/tmp/Unrelated.v'))]:
            with self.assertRaises(ValueError):
                CHECK.check_rejection(code, output, changed, declaration, path)


    def test_old_witness_normalizes_scalar_before_large_memory_conversion(self):
        source = (ROOT / CHECK.WITNESS).read_text()
        witness = source.split('Theorem V293_storage_conditional_entry_witness :', 1)[1]
        witness = witness.split('Theorem V293_storage_guarded_entry_witness :', 1)[0]
        self.assertLess(witness.index('assert (Epriority :'),
                        witness.index('rewrite Epriority. apply V293_conditional_fixture_physical'))
        self.assertIn('unfold M, Mb. rewrite Epriority.', witness)

    def test_guard_program_controls_only_remove_one_guard_in_header(self):
        declaration = 'Theorem V293_OSSched_storage_guarded :'
        start = self.source.index(declaration)
        end = self.source.index('Proof.', start)
        for label, expression in [('outer_guard_omitted_only', 'lock'),
                                  ('inner_guard_omitted_only', 'interrupt')]:
            changed, actual = CHECK.mutations(self.source)[label]
            self.assertEqual(actual, declaration)
            self.assertEqual(changed[:start], self.source[:start])
            self.assertEqual(changed[changed.index('Proof.', start):], self.source[end:])
            self.assertEqual(changed.replace(f'(sifthen (V293_OSSched_zero {expression})',
                '(V293_OSSched_guards interrupt lock', 1), self.source)

    def test_guard_exactness_control_keeps_shared_layout_and_environment(self):
        changed, declaration = CHECK.mutations(self.source)['guard_exactness_forgotten_only']
        start = self.source.index('Definition V293_storage_guarded_entry')
        end = self.source.index('Definition V293_storage_guarded_resumed', start)
        self.assertEqual(declaration, 'Theorem V293_OSSched_storage_guarded :')
        self.assertEqual(changed[:start], self.source[:start])
        self.assertEqual(changed[changed.index('Definition V293_storage_guarded_resumed', start):],
                         self.source[end:])
        fragment = changed[start:changed.index('Definition V293_storage_guarded_resumed', start)]
        self.assertIn('entries guardrest tid tasks events now aop', fragment)
        self.assertIn('stack critical guardbindings old hv.', fragment)
        self.assertNotIn('V293_guard_cell', fragment)

    def test_guard_memory_controls_mutate_only_one_encoded_byte(self):
        source = (ROOT / CHECK.WITNESS).read_text()
        for guard, value in [('interrupt', 'ni'), ('lock', 'nl')]:
            self.assertIn(f'Definition V293_guarded_{guard}_memory ({value} : nat) :=', source)
            changed, declaration = CHECK.guarded_witness_mutation(source, guard)
            start = source.index(f'Definition V293_guarded_{guard}_memory')
            end = source.index('.', start) + 1
            self.assertEqual(declaration, 'Theorem V293_storage_guarded_entry_witness :')
            self.assertEqual(changed[:start], source[:start])
            self.assertEqual(changed[changed.index('.', start) + 1:], source[end:])
            self.assertEqual(changed[start:changed.index('.', start) + 1].replace(
                '(encode_val Tint8 (V293_byteval 0))',
                f'(encode_val Tint8 (V293_byteval {value}))'), source[start:end])

    def test_guard_probe_uses_literal_two_ifs_and_shared_not_private_bytes(self):
        guard = self.probe.split('Section FixedGuards.', 1)[1].split('End FixedGuards.', 1)[0]
        bindings = guard.split('Let gb :=', 1)[1].split('Let grest :=', 1)[0]
        self.assertNotIn('Amapsto', bindings)
        self.assertNotIn('PV', bindings)
        self.assertIn('((bi, 0%Z), Tint8) :: ((bl, 0%Z), Tint8) :: rest.', guard)
        self.assertIn('Amapsto (bi, 0%Z) Tint8 false (V293_byteval ni)', guard)
        self.assertIn('Amapsto (bl, 0%Z) Tint8 false (V293_byteval nl)', guard)
        for name in ['interrupt', 'lock']:
            self.assertIn(f'(sifthen (ebinop oeq (ecast (evar {name}) Tint32)', guard)
        resumed = guard.split('Let gresumed :=', 1)[1].split('Definition checked_guarded :', 1)[0]
        self.assertIn('SWINVt (V293_storage_inv gcells target tp) tid', resumed)
        for frozen in ['V293_byteval ni', 'V293_byteval nl', 'PV', 'V293_guard_cell']:
            self.assertNotIn(frozen, resumed)
        self.assertIn('then gresumed else checked_guarded_entry old hv', guard)
        self.assertNotIn('V293_storage_guarded_entry ', self.probe)
        self.assertIn('Print Assumptions checked_guarded_entry_witness.', self.probe)

    def test_guard_witness_constructs_one_memory_with_both_arbitrary_guard_bytes(self):
        source = (ROOT / CHECK.WITNESS).read_text()
        witness = source.split('Theorem V293_storage_guarded_entry_witness :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('forall different c ni nl events now aop,', witness)
        self.assertIn('ni < 256 -> nl < 256 ->', witness)
        self.assertIn('set (M := merge M0 Mg).', witness)
        self.assertIn('set (Mg := merge (V293_guarded_interrupt_memory ni)', witness)
        self.assertIn('(V293_guarded_lock_memory nl)', witness)
        self.assertEqual(witness.count('exists s.'), 1)
        self.assertIn('V293_conditional_fixture_physical', witness)


    def test_ready_program_controls_are_single_factor_at_actual_composition(self):
        decl = 'Theorem V293_ready_OSSched_prefix_increment_switch :'
        start = self.source.index(decl)
        end = self.source.index('Proof.', start)
        for label, original in [('ready_increment_omitted_only', '(V293_OSSched_increment counter)'),
                                ('ready_switch_omitted_only', '(sprim (switch target))')]:
            changed, actual = CHECK.mutations(self.source)[label]
            self.assertEqual(actual, decl)
            self.assertEqual(changed[:start], self.source[:start])
            self.assertEqual(changed[changed.index('Proof.', start):], self.source[end:])
            self.assertEqual(changed.replace('(sskip None)', original), self.source)
            self.assertIn('(V293_OSSched_unlocked_prefix sched_id table high target)', changed[start:end])
            self.assertIn('readyI r ri', changed[start:end])

    def test_ready_return_control_changes_only_relational_closure(self):
        changed, actual = CHECK.mutations(self.source)['ready_relation_erased_on_return_only']
        decl = 'Lemma V293_ready_connected_return :'
        self.assertEqual(actual, decl)
        start = self.source.index(decl)
        end = self.source.index('Qed.', start)
        self.assertEqual(changed[:start], self.source[:start])
        self.assertEqual(changed[changed.index('Qed.', start):], self.source[end:])
        self.assertEqual(changed.replace('apply V293_retained_prefix_return_snapshot; eassumption',
            'apply V293_ready_prefix_return; eassumption'), self.source)
        self.assertIn('SWINVt readyI tid', changed[start:end])
        self.assertIn('V293_bitmap_tasks lo hi tasks', changed[start:end])

    def test_generic_counter_control_targets_execution_not_compatibility_wrapper(self):
        changed, decl = CHECK.mutations(self.source)['increment_omitted_only']
        self.assertEqual(decl, 'Lemma V293_storage_connected_increment_under :')
        under = self.source.split(decl, 1)[1].split('Qed.', 1)[0]
        self.assertIn('(RI : Inv)', under)
        self.assertIn('apply V293_OSSched_counter_increment.', under)

    def test_ready_probe_fixes_same_invariant_literal_execution_and_nonfrozen_resume(self):
        ready = self.probe.split('Let readyI :=', 1)[1].split('End FixedConnect.', 1)[0]
        self.assertIn('V293_ready_inv bt bg br bh bp tp extra target.', ready)
        self.assertIn('forall Spec (RI : Inv)', ready)
        self.assertIn('(GV target @ (Tptr tp) |-> old)', ready)
        self.assertIn('SWINV readyI', ready)
        self.assertIn('(sseq (scall sched_id nil)', ready)
        self.assertIn('(sassign (evar target) (earrayelem (evar table) (evar high)))', ready)
        self.assertIn('(sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))', ready)
        self.assertIn('(sprim (switch target))', ready)
        self.assertNotIn('V293_ready_connected_entry ', ready)
        self.assertNotIn('V293_OSSched_unlocked_prefix ', ready)
        self.assertNotIn('V293_OSSched_increment ', ready)
        resumed = ready.split('Let ready_resumed :=', 1)[1].split('Definition checked_increment_under', 1)[0]
        self.assertIn('SWINVt readyI tid', resumed)
        for frozen in ['lo', 'hi', 'tasks', 'entries', 'next', ' c', 'PV']:
            self.assertNotRegex(resumed, r'\b' + frozen.strip() + r'\b')
        for root in ['checked_increment_under', 'checked_ready_connect_return', 'checked_ready_connect_switch',
                     'checked_ready_connect', 'checked_ready_connect_entry_witness']:
            self.assertIn(f'Print Assumptions {root}.', self.probe)
            self.assertLess(self.probe.index('End FixedConnect.'),
                            self.probe.index(f'Print Assumptions {root}.'))
        self.assertEqual(self.probe.count('Print Assumptions '), CHECK.ROOT_COUNT)

    def test_ready_witness_reuses_one_physical_state_and_exact_counter_observation(self):
        source = (ROOT / CHECK.WITNESS).read_text()
        # The public theorem drops only the empty-local-environment fact.
        # The single physical construction lives in the stronger helper.
        wrapper = source.split('Theorem V293_ready_connected_entry_witness :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('forall different c events now aop,', wrapper)
        self.assertIn('destruct (V293_ready_connected_entry_witness_empty_locals different c events now aop)', wrapper)
        self.assertEqual(wrapper.count('exists s.'), 1)
        self.assertIn('as (s & Hb & Ht & Hcur & Hptr & Hle & Hs)', wrapper)
        self.assertIn('exact Hs.', wrapper)
        witness = source.split('Lemma V293_ready_connected_entry_witness_empty_locals :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('forall different c events now aop,', witness)
        self.assertIn('destruct (V293_storage_connected_entry_witness_empty_locals different c events now aop)', witness)
        self.assertEqual(witness.count('exists s.'), 1)
        self.assertIn('getlenv s = emp', witness)
        self.assertIn('exact Hle', witness)
        self.assertIn('exact Hcounter', witness)
        self.assertIn('apply V293_ready_switch_close', witness)
        for declaration in [wrapper, witness]:
            self.assertIn('V293_bitmap_tasks 0 16 (V293_current_mode_tasks different)', declaration)
            self.assertIn('V293_priority_table (V293_current_mode_entries different)', declaration)
            self.assertIn('(PV (12%positive, Int.zero) @ Tint32 |-> (Vint32 c))', declaration)
            self.assertNotIn('False ->', declaration)
        physical = source.split('Lemma V293_storage_connected_entry_witness_empty_locals :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('getlenv s = emp', physical)
        self.assertIn('set (s := ((V293_connect_fixture_ge, emp, M,', physical)
        self.assertEqual(physical.count('exists s.'), 1)
        self.assertIn('V293_encoded_memory_mapsto', physical)

    def test_pointer_probe_has_literal_branches_same_state_and_no_shadow_frame(self):
        probe = (ROOT / 'audit/probes/V293ReadyPointerConditionalProbe.v').read_text()
        self.assertEqual(probe.count('Print Assumptions '), 5)
        for root in ['checked_pointer_tail', 'checked_pointer_change', 'checked_pointer_conditional',
                     'checked_pointer_entry_witness', 'checked_no_shadow_frame']:
            self.assertIn(f'Print Assumptions {root}.', probe)
        branch = probe.split('Definition checked_pointer_conditional :', 1)[1].split('End FixedConnect.', 1)[0]
        self.assertIn('(px ==> A_notin_lenv OSTCBCur ** Atrue)', branch)
        self.assertIn('(eunop oppsite (ebinop oeq (evar target) (evar OSTCBCur)))', branch)
        self.assertIn('(sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))', branch)
        self.assertIn('(sprim (switch target))', branch)
        self.assertNotIn('V293_OSSched_unlocked_prefix', branch)
        self.assertNotIn('V293_OSSched_pointer_different', branch)
        fixture = probe.split('Theorem checked_pointer_entry_witness :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('forall different c events now aop,', fixture)
        self.assertIn('V293_ready_connected_entry_witness_empty_locals different c events now aop', fixture)
        self.assertEqual(fixture.count('exists s.'), 1)
        self.assertIn('(A_notin_lenv OSTCBCur)', fixture)
        self.assertIn('exact Hcounter', fixture)

    def test_ready_conditional_program_controls_change_one_branch_statement_only(self):
        decl = 'Theorem V293_ready_conditional_change :'
        start = self.source.index(decl)
        end = self.source.index('Proof.', start)
        cases = [
            ('ready_conditional_increment_omitted_only', '(sseq (sskip None) (sprim (switch target)))'),
            ('ready_conditional_switch_omitted_only', '(sseq (V293_OSSched_increment counter) (sskip None))')]
        for label, then_program in cases:
            changed, actual = CHECK.mutations(self.source)[label]
            self.assertEqual(actual, decl)
            self.assertEqual(changed[:start], self.source[:start])
            self.assertEqual(changed[changed.index('Proof.', start):], self.source[end:])
            self.assertEqual(changed.replace(
                '(sifthen (V293_OSSched_different high current) ' + then_program + ')',
                '(V293_OSSched_change high current counter (sprim (switch target)))'), self.source)
            self.assertIn('readyI r ri', changed[start:changed.index('Proof.', start)])

    def test_ready_conditional_exact_byte_control_keeps_every_other_resource(self):
        changed, decl = CHECK.mutations(self.source)['ready_conditional_current_byte_forgotten_only']
        self.assertEqual(decl, 'Theorem V293_ready_conditional_comparison :')
        start = self.source.index('Definition V293_ready_conditional_open :=')
        end = self.source.index('Let tail next c :=', start)
        self.assertEqual(changed[:start], self.source[:start])
        self.assertEqual(changed[changed.index('Let tail next c :=', start):], self.source[end:])
        self.assertEqual(changed.replace('lo hi entries (V293_storage extra) tid',
                                        'lo hi entries kept tid', 1), self.source)

    def test_ready_conditional_current_relation_control_changes_explicit_premise_only(self):
        changed, decl = CHECK.mutations(self.source)['ready_conditional_current_task_omitted_only']
        self.assertEqual(decl, 'Theorem V293_ready_conditional_equal_finish :')
        start = self.source.index(decl)
        end = self.source.index('Proof.', start)
        self.assertEqual(changed[:start], self.source[:start])
        self.assertEqual(changed[changed.index('Proof.', start):], self.source[end:])
        self.assertEqual(changed.replace('True -> GoodFrm px ->',
                                        'V293_current_task tasks tid nc -> GoodFrm px ->'), self.source)

    def test_ready_conditional_probe_is_literal_same_inv_and_unfrozen(self):
        part = self.probe.split('Section FixedReadyConditional.', 1)[1].split('End FixedReadyConditional.', 1)[0]
        self.assertIn('V293_ready_inv bt bg br bh bp tp extra target.', part)
        self.assertIn('SWINV readyI', part)
        self.assertIn('(GV target @ (Tptr tp) |-> old)', part)
        self.assertIn('PV (bcur, Int.zero) @ Tint8 |-> (V293_byteval nc)', part)
        self.assertIn('V293_current_task tasks tid nc ->', part)
        self.assertIn('(sseq (scall sched_id nil)', part)
        self.assertIn('(sifthen (eunop oppsite (ebinop oeq', part)
        self.assertIn('(sassign (evar counter) (ebinop oplus (evar counter) (econst32 Int.one)))', part)
        self.assertIn('(sprim (switch target))', part)
        resumed = part.split('Let cresumed :=', 1)[1].split('Definition checked_ready_conditional_comparison', 1)[0]
        self.assertIn('SWINVt readyI tid', resumed)
        for frozen in ['lo', 'hi', 'tasks', 'entries', 'nc', 'next', ' c', 'PV']:
            self.assertNotRegex(resumed, r'\b' + frozen.strip() + r'\b')
        for alias in ['V293_ready_conditional_entry ', 'V293_ready_conditional_open ',
                      'V293_ready_conditional_resumed ', 'V293_OSSched_change ',
                      'V293_OSSched_unlocked_prefix ', 'V293_OSSched_different ']:
            self.assertNotIn(alias, part)
        for root in ['comparison', 'equal_finish', '', 'entry_witness']:
            root = 'checked_ready_conditional' + ('_' + root if root else '')
            self.assertLess(self.probe.index('End FixedReadyConditional.'),
                            self.probe.index(f'Print Assumptions {root}.'))

    def test_ready_conditional_witness_reuses_exact_same_state_not_separate_models(self):
        source = (ROOT / CHECK.WITNESS).read_text()
        witness = source.split('Theorem V293_ready_conditional_entry_witness :', 1)[1].split('Qed.', 1)[0]
        self.assertEqual(witness.count('exists s.'), 1)
        self.assertIn('destruct (V293_storage_conditional_entry_witness different c events now aop)', witness)
        self.assertIn('exact Hcounter', witness)
        self.assertIn('V293_conditional_kept 12%positive 13%positive (V293_current_mode_priority different)', witness)
        self.assertIn('V293_current_task (V293_current_mode_tasks different)', witness)
        self.assertNotIn('False ->', witness)

    def test_self_schedule_execution_has_one_shared_mechanism_and_physical_task_table(self):
        self.assertEqual(self.source.count("eapply (absinfer_sched'"), 1)
        self.assertEqual(self.source.count('eapply V293_self_schedule_consume;'), 2)
        generic = self.source.split('Lemma V293_self_schedule_consume :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('Hfields s Hs', generic)
        self.assertIn('V293_highest_ready tasks tid', generic)
        self.assertIn('Print Assumptions checked_self_schedule_consume.', self.probe)
        self.assertIn('Print Assumptions checked_ready_self_finish.', self.probe)

    def test_pointer_critical_probe_has_literal_enabled_roundtrip_without_stale_values(self):
        probe = (ROOT / 'audit/probes/V293ReadyPointerCriticalProbe.v').read_text()
        root = probe.split('Definition checked_critical_roundtrip :', 1)[1].split('End FreshCritical.', 1)[0]
        pre = root.split('InfRules ', 1)[1].split('(sseq (sprim encrit)', 1)[0]
        for stale in ['tasks', 'entries', 'checked_snapshot', 'lo', 'hi', 'next']:
            self.assertNotRegex(pre, r'\b' + stale + r'\b')
        self.assertIn('<||sched;;aop||>', pre)
        self.assertIn('true, nil, critical', pre)
        self.assertEqual(root.count('(sprim encrit)'), 1)
        self.assertEqual(root.count('(sprim excrit)'), 1)
        self.assertIn('<||aop||> ** OS[', root)
        self.assertIn('(sassign (evar counter) (ebinop oplus', root)
        self.assertIn('(sprim (switch target))', root)
        for alias in ['V293_ready_roundtrip_pre ', 'V293_ready_roundtrip_post ',
                      'V293_ready_prefix_open ', 'V293_OSSched_unlocked_prefix ',
                      'V293_OSSched_pointer_different ', 'V293_OSSched_increment ']:
            self.assertNotIn(alias, probe)
        self.assertEqual(probe.count('Print Assumptions '), 4)

    def test_deleted_current_switch_is_nonreturning_before_postcondition_weakening(self):
        dead = self.source.split('Lemma V293_ready_connected_switch_dead :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('~ indom tasks tid ->', dead)
        self.assertIn('(sprim (switch target)) Afalse tid.', dead)
        self.assertIn('eapply switchdead_rule', dead)
        self.assertIn('unfold SWPRE_DEAD', dead)
        self.assertIn('V293_storage_connected_switch_highest', dead)
        total = self.source.split('Lemma V293_ready_connected_switch_total :', 1)[1].split('Qed.', 1)[0]
        self.assertNotIn('indom tasks tid ->', total.split('Proof.', 1)[0])
        self.assertIn('classic (indom tasks tid)', total)
        self.assertIn('conseq_rule with (q := Afalse)', total)
        self.assertIn('apply V293_ready_connected_switch_dead', total)

    def test_fresh_pointer_body_binds_shared_observations_inside_proof(self):
        fresh = self.source.split('Theorem V293_ready_OSSched_pointer_fresh :', 1)[1].split('Qed.', 1)[0]
        header, proof = fresh.split('Proof.', 1)
        for stale in ['indom', 'tasks', 'events', 'entries', 'lo', 'hi', 'old', 'hv']:
            self.assertNotRegex(header, r'\b' + stale + r'\b')
        self.assertIn('EX tasks : TcbMod.map', proof)
        self.assertIn('V293_shared_current_agree', proof)
        self.assertIn('V293_ready_switch_close', proof)
        self.assertIn('V293_ready_OSSched_pointer_conditional_total', proof)


    def test_fresh_guard_bytes_come_from_same_ready_storage_not_private_frame(self):
        part = self.source.split('Section ReadyPointerGuards.', 1)[1].split('End ReadyPointerGuards.', 1)[0]
        self.assertIn('((bi, 0%Z), Tint8) :: ((bl, 0%Z), Tint8) :: rest', part)
        frame = part.split('Let guardbindings px :=', 1)[1].split('Let body sched_id :=', 1)[0]
        for forbidden in ['Amapsto', 'V293_guard_cell', 'V293_byteval', ' ni', ' nl']:
            self.assertNotIn(forbidden, frame)
        observation = part.split('Lemma V293_ready_guard_observe :', 1)[1].split('Qed.', 1)[0]
        for required in ['V293_storage_cell (bi, 0%Z) Tint8', 'V293_storage_cell (bl, 0%Z) Tint8',
                         'V293_typed_byte_value', 'separate_rw2ro']:
            self.assertIn(required, observation)
        self.assertNotIn('evalval', observation.split('Proof.', 1)[0])

    def test_disabled_guard_keeps_pending_schedule_and_same_ready_invariant(self):
        continuation = self.source.split('Definition V293_ready_guard_continuation', 1)[1].split('Lemma ', 1)[0]
        self.assertIn('then aop else (sched;;aop)', continuation)
        skip = self.source.split('Lemma V293_ready_guard_skip_close :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('tid (sched;;aop) stack critical px', skip)
        self.assertIn('V293_ready_switch_close', skip)
        self.assertNotIn('absinfer', skip)
        observed = self.source.split('Theorem V293_ready_OSSched_pointer_guards_observed :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('V293_OSSched_guards_rule', observed)
        self.assertIn('V293_ready_guard_skip_close', observed)
        self.assertIn('V293_ready_OSSched_pointer_fresh', observed)

    def test_guard_probe_checks_literal_two_guard_critical_ast_and_pending_post(self):
        probe = (ROOT / 'audit/probes/V293ReadyPointerGuardsProbe.v').read_text()
        root = probe.split('Definition checked_guarded_critical :', 1)[1].split('End FreshGuards.', 1)[0]
        pre = root.split('InfRules ', 1)[1].split('(sseq (sprim encrit)', 1)[0]
        for stale in ['ni', 'nl', 'tasks', 'entries', 'checked_snapshot', 'lo', 'hi', 'next']:
            self.assertNotRegex(pre, r'\b' + stale + r'\b')
        for name in ['interrupt', 'lock']:
            self.assertIn('(sifthen (ebinop oeq (ecast (evar ' + name + ') Tint32)', root)
        self.assertIn('then aop else (sched;;aop)', root)
        self.assertEqual(root.count('(sprim encrit)'), 1)
        self.assertEqual(root.count('(sprim excrit)'), 1)
        self.assertIn('(sprim (switch target))', root)
        self.assertEqual(probe.count('Print Assumptions '), 4)
        for alias in ['V293_ready_guard_open ', 'V293_ready_guard_observed ', 'V293_ready_guard_resumed ',
                      'V293_ready_guard_continuation ', 'V293_OSSched_guards ', 'V293_OSSched_zero ',
                      'V293_ready_roundtrip_pre ', 'V293_ready_roundtrip_post ']:
            self.assertNotIn(alias, probe)

    def test_fresh_guard_post_does_not_freeze_guard_memory_after_switch(self):
        fresh = self.source.split('Theorem V293_ready_OSSched_pointer_guards_fresh :', 1)[1].split('Qed.', 1)[0]
        pre = fresh.split('InfRules ', 1)[1].split('(V293_OSSched_guards ', 1)[0]
        for stale in ['ni', 'nl', 'tasks', 'entries', 'indom']:
            self.assertNotRegex(pre, r'\b' + stale + r'\b')
        post = fresh.split('(V293_OSSched_guards ', 1)[1].split('Proof.', 1)[0]
        self.assertIn('EX ni : nat, EX nl : nat', post)
        self.assertNotIn('V293_guard_cell', post)
        self.assertNotIn('Amapsto', post)


class ReadyGuardEntryTests(unittest.TestCase):
    def setUp(self):
        self.witness = (ROOT / CHECK.WITNESS).read_text().split(
            'Theorem V293_ready_guard_entry_witness :', 1)[1]
        self.probe = (ROOT / 'audit/probes/V293ReadyGuardEntryProbe.v').read_text()

    def test_entry_constructs_one_state_with_guards_counter_and_accurate_cache(self):
        header, body = self.witness.split('Proof.', 1)
        self.assertEqual(header.count('exists s,'), 1)
        self.assertIn('getlenv s = emp', header)
        self.assertIn('ni < 256 -> nl < 256', header)
        self.assertIn('OSTCBCur) ni nl)', header)
        self.assertIn('(V293_byteval (V293_current_mode_priority different))', header)
        self.assertIn('(Vint32 c)', header)
        self.assertIn('events now ** Atrue', header)
        self.assertIn('V293_guarded_interrupt_memory ni', body)
        self.assertIn('V293_guarded_lock_memory nl', body)
        self.assertIn('V293_conditional_fixture_physical', body)

    def test_private_frame_has_no_shared_bytes(self):
        private = self.probe.split('Definition checked_entry_private :=', 1)[1].split('Definition checked_entry_open', 1)[0]
        self.assertIn('A_notin_lenv OSTCBCur', private)
        self.assertIn('Agvarenv 108%Z Tint8', private)
        for ownership in ['Amapsto', 'PV ', 'V293_guard_cell', 'V293_storage_cell']:
            self.assertNotIn(ownership, private)

    def test_probe_spells_full_entry_and_reads_literal_guards_on_same_state(self):
        for alias in ['V293_ready_guard_observed ', 'V293_ready_guard_open ', 'V293_ready_snapshot ',
                      'V293_retained_prefix_entry_heap ', 'V293_OSSched_zero ']:
            self.assertNotIn(alias, self.probe)
        reads = self.probe.split('Theorem checked_guard_entry_reads :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(reads.count('exists s,'), 1)
        self.assertEqual(reads.count('load Tint8 (getmem s)'), 3)
        self.assertEqual(reads.count('load Tint32 (getmem s)'), 1)
        self.assertEqual(reads.count('evalval (ebinop oeq'), 2)
        self.assertEqual(reads.count('evaltype (ebinop oeq'), 2)
        self.assertIn('checked_array true 1%positive', self.probe)
        self.assertEqual(self.probe.count('Print Assumptions '), 3)

    def test_controls_change_only_one_new_header_observation(self):
        # A clean checkout excludes audit/logs: inspect only delivery source.
        header, proof = self.witness.split('Proof.', 1)
        cases = [
            ('OSTCBCur) ni nl)', 'OSTCBCur) 0 nl)'),
            ('OSTCBCur) ni nl)', 'OSTCBCur) ni 0)'),
            ('(V293_byteval (V293_current_mode_priority different))', '(V293_byteval 0)'),
            ('(Vint32 c)', '(Vint32 (Int.add c Int.one))'),
        ]
        for old, new in cases:
            with self.subTest(observation=old, replacement=new):
                self.assertEqual(header.count(old), 1)
                changed = header.replace(old, new, 1) + 'Proof.' + proof
                self.assertEqual(changed.split('Proof.', 1)[1], proof)
                self.assertEqual(changed.replace(new, old, 1), self.witness)



class ReadyPriorityGuardsTests(unittest.TestCase):
    def setUp(self):
        source = (ROOT / CHECK.SOURCE).read_text()
        self.section = source.split('Section ReadyPriorityGuards.', 1)[1]
        self.probe = (ROOT / 'audit/probes/V293ReadyPriorityGuardsProbe.v').read_text()

    def test_priority_program_and_explicit_accuracy_frontier(self):
        header = self.section.split('Theorem V293_ready_OSSched_priority_guarded :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('V293_current_task tasks tid nc ->', header)
        self.assertIn('V293_OSSched_guards interrupt lock', header)
        self.assertIn('V293_OSSched_change high current counter (sprim (switch target))', header)
        self.assertNotIn('pointer_different', self.section)
        self.assertNotIn('sprim encrit', header)
        self.assertNotIn('sprim excrit', header)

    def test_disabled_closure_retains_pending_schedule_and_same_ready_relation(self):
        skip = self.section.split('Lemma V293_ready_priority_guarded_skip :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('V293_ready_priority_guarded_resumed (sched;;aop)', skip)
        self.assertNotIn('absinfer', skip)
        self.assertIn('then aop else (sched;;aop)', self.section)
        self.assertIn('Let I := V293_ready_inv', self.section)
        self.assertIn('V293_ready_conditional_resumed', self.section)

    def test_independent_literal_interface_not_candidate_precondition_alias(self):
        for alias in ['V293_ready_priority_guarded_entry', 'V293_ready_priority_guarded_resumed',
                      'V293_ready_conditional_entry', 'V293_ready_conditional_resumed']:
            self.assertNotIn(alias, self.probe)
        self.assertIn('SWINV readyI', self.probe)
        self.assertIn('SWINVt readyI tid', self.probe)
        self.assertIn('(ebinop oeq (ecast (evar high) Tint32) (ecast (evar current) Tint32))', self.probe)
        self.assertIn('Amapsto (bi, 0%Z) Tint8 false (V293_byteval ni)', self.probe)
        self.assertIn('Amapsto (bl, 0%Z) Tint8 false (V293_byteval nl)', self.probe)
        self.assertEqual(self.probe.count('Print Assumptions '), 2)

    def test_four_controls_change_only_one_new_header_factor(self):
        prefix, theorem = self.section.split('Theorem V293_ready_OSSched_priority_guarded :', 1)
        header, proof = theorem.split('Proof.', 1)
        cases = [
            ('(V293_OSSched_guards interrupt lock', '(sifthen (V293_OSSched_zero lock)'),
            ('(V293_OSSched_guards interrupt lock', '(sifthen (V293_OSSched_zero interrupt)'),
            ('then aop else (sched;;aop)', 'then aop else aop'),
            ('V293_current_task tasks tid nc ->', 'True ->'),
        ]
        for old, new in cases:
            with self.subTest(factor=new):
                self.assertEqual(header.count(old), 1)
                changed = header.replace(old, new, 1) + 'Proof.' + proof
                self.assertEqual(changed.split('Proof.', 1)[1], proof)
                self.assertEqual(changed.replace(new, old, 1), theorem)
        self.assertNotIn('audit/logs', prefix + header + proof)

if __name__ == '__main__':
    unittest.main()
