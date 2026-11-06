"""任务创建 NULL 分支纵向连接的结构回归；语义由 Coq 证据承担。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskCreateOwnedEmpty.v'
PROBE = 'audit/probes/V293TaskCreateOwnedEmptyProbe.v'
D = ROOT / 'audit/logs/stage113-taskcreate-owned-null-branch'


class TaskCreateOwnedEmptyTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / SOURCE).read_text()
        self.probe = (ROOT / PROBE).read_text()

    def test_no_holes_new_axioms_or_audit_dependency(self):
        for text in [self.source, self.probe]:
            self.assertNotRegex(text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.', self.source)
        self.assertNotIn('CertiOS.audit.', self.probe)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

    def test_public_interface_is_not_a_continuation_or_execution_oracle(self):
        public = self.source.split('Theorem V293_OSTaskCreateExt_owned_empty_critical_tail :')[1].split('Proof.')[0]
        self.assertEqual(public.count('InfRules '), 1)
        self.assertNotRegex(public, r'\b(?:evalval|evaladdr|load|loststep|sfexec|WFIFun)\b')
        self.assertIn('V293_create_slot_state bp bc table bn br p 0 None', public)
        self.assertIn('V293_create_enabled_failure_return', public)
        self.assertIn('Spec hook=Some', public)
        self.assertIn('Spec f=Some', public)

    def test_actual_ast_and_dead_occupied_tail_are_retained(self):
        tail = self.source.split('Definition V293_create_owned_empty_tail ')[1].split('Lemma ')[0]
        for token in ['V293_TaskCreateExt_irq_error', 'V293_TaskCreateExt_occupied',
                      'V293_task_prio_reserved_expr 97%Z', 'sprim excrit',
                      'V293_TaskCreateExt_calls', 'V293_TaskCreateExt_suffix']:
            self.assertIn(token, tail)
        identity = self.source.split('Lemma V293_create_owned_empty_tail_source :')[1].split('Qed.')[0]
        self.assertIn('V293_CreateExt_body 92%Z 99%Z 97%Z', identity)
        self.assertIn('Proof. reflexivity.', identity)
        self.assertIn('apply V293_create_reject_if_true', self.source)
        self.assertIn('apply pfalse_rule', self.source)

    def test_seam_uses_owned_locals_once_and_no_head_bytes(self):
        seam = self.source.split('Lemma V293_create_owned_empty_seam :')[1].split('Proof.')[0]
        self.assertIn('V293_create_owned_empty_aux', seam)
        self.assertIn('V293_create_owned_empty_kept', seam)
        self.assertIn('V293_create_tcb_arguments', seam)
        self.assertNotIn('Amapsto(bf', seam)
        self.assertIn('apply V293_create_raw_local', self.source)
        self.assertIn('apply V293_OSTaskCreateExt_owned_empty_call_suffix', self.source)

    def test_literal_entry_has_physical_slot_counter_and_all_twelve_locals(self):
        self.assertIn('Theorem OEEntryLiteral : OEState OELE OEEntryMemory(true::nil) |= OEEntry nil.', self.probe)
        self.assertIn('Definition OEEntryMemory :=', self.probe)
        self.assertIn('Definition OEEntrySlot :=', self.probe)
        self.assertIn('Definition OEEntryNest :=', self.probe)
        self.assertIn('Definition OEEntryHead :=', self.probe)
        for name in ['101', '109', '108', '205', '206', '207', '208', '204', '209', '201', '202', '203']:
            self.assertRegex(self.probe, r'(?:Alvarenv|LV) ' + name + r'%Z')

    def test_single_literal_inv_and_finite_spec_check_full_callee_and_connected_tail(self):
        self.assertEqual(len(re.findall(r'^Definition \w+ : Inv :=', self.probe, re.M)), 1)
        self.assertEqual(self.probe.count('InfRules(OESpec cs)sd V293_witness_li OEInv'), 2)
        for name in ['OEBuilders', 'OECalleeCheckedSameSpec', 'OEConnectedTailCheckedSameSpec']:
            self.assertRegex(self.probe, r'(?:Lemma|Theorem) ' + name + r' :')
        self.assertIn('Z.eq_dec f 500%Z', self.probe)
        self.assertIn('Z.eq_dec f 600%Z', self.probe)
        self.assertIn('V293_OS_TCBInit_empty_enabled_contract', self.probe)

    def test_store_removal_is_one_factor_and_common_input_checked(self):
        controls = json.loads((D / 'controls.json').read_text())
        self.assertTrue(controls['passed'])
        self.assertEqual([r['exit'] for r in controls['rows']], [0, 1])
        self.assertTrue(all(r['common_input_checked'] for r in controls['rows']))
        for row in controls['rows']:
            p = D / (row['label'] + '.v.snapshot.txt')
            self.assertEqual(hashlib.sha256(p.read_bytes()).hexdigest(), row['source_sha256'])
        present = (D / 'StorePresent02.v.snapshot.txt').read_text()
        removed = (D / 'StoreRemoved02.v.snapshot.txt').read_text()
        self.assertEqual(present.replace('Definition Action : option mem := store(Tptr V293_tcb_type)Input(403%positive,44%Z)Vnull.',
                                         'Definition Action : option mem := Some Input.'), removed)
        self.assertIn('OERollbackStoreRemovedKeepsReserved', self.probe)

    def test_control_scope_does_not_claim_mutated_whole_api(self):
        controls = json.loads((D / 'controls.json').read_text())
        self.assertIn('not whole mutated API', controls['scope'])
        for label in ['StorePresent', 'StoreRemoved']:
            row = json.loads((D / (label + '.json')).read_text())
            self.assertEqual(row['exit'], 1)
            self.assertFalse(row['common_input_checked'])
