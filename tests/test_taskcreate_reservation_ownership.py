"""预留半权限的结构回归；语义结论由独立 Coq 证据承担。"""
from pathlib import Path
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskCreateReservationOwnership.v'
PROBE = 'audit/probes/V293TaskCreateReservationOwnershipProbe.v'
D = ROOT / 'audit/logs/stage112-reservation-ownership'


class TaskCreateReservationOwnershipTests(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / SOURCE).read_text()
        self.probe = (ROOT / PROBE).read_text()

    def statement(self, name):
        return self.text.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]

    def test_no_holes_new_axioms_or_audit_dependency(self):
        for text in [self.text, self.probe]:
            self.assertNotRegex(text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.', self.text)
        self.assertNotIn('CertiOS.audit.probes.', self.probe)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

    def test_permission_is_value_determined_not_existential(self):
        permission = self.text.split('Definition V293_reservation_permission ')[1].split('Definition ')[0]
        pool = self.text.split('Definition V293_reservation_pool ')[1].split('Definition ')[0]
        self.assertIn('negb(beq_tid t reserved)', permission)
        self.assertIn('EX v:val', pool)
        self.assertIn('V293_reservation_permission reserved v', pool)
        self.assertNotIn('EX permission', pool)

    def test_precision_and_physical_compatibility_are_proved(self):
        for name in ['V293_reservation_pool_precise', 'V293_reservation_pool_good',
                     'V293_reservation_pool_isr', 'V293_reservation_compatible_values']:
            self.assertRegex(self.text, r'Lemma ' + name + r' :')
        self.assertIn('load_mem_mono', self.text)
        self.assertIn('V293_reservation_bytes_exact', self.text)
        self.assertIn('Theorem ROArbitraryPermissionNotPrecise : ~precise ROBadPool.', self.probe)

    def test_publish_reacquire_and_uniqueness_need_pool(self):
        acquire = self.statement('V293_reservation_reacquire')
        self.assertIn('V293_reservation_owner a reserved ** V293_reservation_pool a reserved', acquire)
        self.assertIn('true(Vptr reserved)', acquire)
        unique = self.statement('V293_reservation_single_owner')
        self.assertIn('V293_reservation_pool a reserved', unique)
        self.assertIn('Afalse', unique)
        self.assertIn('Theorem V293_reservation_publish :', self.text)

    def test_actual_reservation_and_excrit_publish_owner(self):
        public = self.statement('V293_OSTaskCreateExt_owned_reservation')
        self.assertIn('V293_task_prio_reserved_expr 97%Z', public)
        self.assertIn('(sprim excrit)', public)
        self.assertIn('V293_create_owned_share table(br,Int.zero)p', public)
        self.assertIn('apply V293_create_prefix_reserve_hoare', self.text)

    def test_actual_rollback_consumes_owner(self):
        public = self.statement('V293_OSTaskCreateExt_owned_rollback')
        self.assertEqual(public.count('V293_create_owned_share'), 1)
        self.assertIn('(V293_create_enabled_failure_state table p F aop ir si ci)tid.', public)
        self.assertIn('V293_TaskCreateExt_rollback 92%Z 101%Z', public)
        self.assertIn('apply V293_create_failure_store_hoare', self.text)

    def test_hook_preserves_owner_in_caller_frame(self):
        public = self.statement('V293_OSTaskCreateExt_owned_stack_fragment')
        self.assertIn('V293_TaskCreateExt_stack_call 108%Z hook', public)
        self.assertIn('V293_create_enabled_external Rafter aop ir si ci', public)
        self.assertIn('V293_create_owned_share table(br,Int.zero)p', public)
        self.assertIn('V293_OSTaskCreateExt_stack_resource_call_hoare', self.text)

    def test_actual_tcb_call_and_complete_suffix_no_execution_oracle(self):
        public = self.statement('V293_OSTaskCreateExt_owned_empty_call_suffix')
        self.assertEqual(public.count('InfRules '), 1)
        self.assertNotRegex(public, r'\b(?:evaladdr|evalval|load|loststep|sfexec|WFIFun)\b')
        self.assertIn('V293_TaskCreateExt_TCB_call 209%Z f 101%Z 108%Z 205%Z 206%Z 207%Z 208%Z 204%Z', public)
        self.assertIn('V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z running sched', public)

    def test_one_literal_invariant_checks_reservation_caller_and_full_callee(self):
        self.assertEqual(len(re.findall(r'^Definition \w+ : Inv :=', self.probe, re.M)), 1)
        self.assertEqual(self.probe.count('InfRules(ROSpec cs)sd V293_witness_li ROInv'), 3)
        for name in ['ROSharedLiteral', 'ROSameInvariantFreeReservedOther', 'ROOwnedWholeLiteral',
                     'ROBuilders', 'ROCalleeCheckedSameSpec', 'ROCallerCheckedSameSpec',
                     'ROReservationCheckedSameSpec']:
            self.assertRegex(self.probe, r'(?:Lemma|Theorem) ' + name + r' :')
        self.assertIn('V293_OS_TCBInit_empty_enabled_contract', self.probe)

    def test_owner_ablation_is_single_factor_and_has_counterexample(self):
        plan = json.loads((D / 'controls-plan02.json').read_text())
        controls = json.loads((D / 'controls.json').read_text())
        self.assertTrue(controls['passed'])
        self.assertTrue(all(row['common_input_checked'] for row in controls['accepted_rows']))
        present = (D / 'OwnerPresent02.v.snapshot.txt').read_text()
        removed = (D / 'OwnerRemoved02.v.snapshot.txt').read_text()
        self.assertEqual(present.replace('Definition Action : mem := ROOwner.',
                                         'Definition Action : mem := (emp:mem).'), removed)
        self.assertIn('physical permission compatibility only', plan['scope'])
        self.assertIn('Theorem ROOwnerRemovedAdmitsWrong :', self.probe)


if __name__ == '__main__':
    unittest.main()
