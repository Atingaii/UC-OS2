"""预留权限接真实优先级写入；结构回归不替代 Coq 语义检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TCBOwnedPriority.v'
PROBE = 'audit/probes/V293TCBOwnedPriorityProbe.v'
D = ROOT / 'audit/logs/stage118-tcb-owned-priority'


class TCBOwnedPriorityTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / SOURCE).read_text()
        self.probe = (ROOT / PROBE).read_text()

    def section(self, name):
        return self.source.split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_no_holes_or_production_audit_dependency(self):
        for text in [self.source, self.probe]:
            self.assertNotRegex(text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.', self.source)
        self.assertEqual(self.probe.count('Require Import CertiOS.audit.'), 1)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

    def test_enabled_entry_owns_half_not_full_slot(self):
        enter = self.section('V293_tcb_priority_enter')
        pre = enter.split('InfRules ', 1)[1].split('(sprim encrit)', 1)[0]
        self.assertIn('V293_create_owned_share', pre)
        self.assertNotIn('Amapsto', pre)
        self.assertIn('apply V293_reservation_reacquire', enter)
        self.assertIn('apply encrit1_rule', enter)

    def test_physical_store_and_actual_loads(self):
        store = self.section('V293_tcb_priority_store')
        self.assertIn('p<13', store)
        self.assertIn('(sassign(earrayelem(evar 92%Z)(evar 101%Z))(evar 108%Z))', store)
        self.assertIn('V293_raw_assign_hoare', store)
        self.assertIn('V293_tcb_init_read H 1%nat PriorityRead', store)
        self.assertIn('V293_tcb_init_read H 2%nat PointerRead', store)
        self.assertIn('V293_rekey_array_address', store)
        self.assertNotIn('Rvl', store.split('Proof.')[0])

    def test_same_pool_return_and_explicit_freshness(self):
        exit_proof = self.section('V293_tcb_priority_exit')
        self.assertIn('pointer<>reserved', exit_proof)
        self.assertIn('apply V293_reservation_pool_pointer', exit_proof)
        self.assertIn('exact Close', exit_proof)
        self.assertIn('apply excrit1_rule', exit_proof)
        post = exit_proof.split('(sprim excrit)', 1)[1].split('Proof.')[0]
        self.assertNotIn('V293_create_owned_share', post)
        self.assertNotIn('Amapsto', post)

    def test_original_right_associated_bracket(self):
        whole = self.section('V293_OS_TCBInit_owned_priority_then')
        statement = whole.split('Proof.')[0]
        self.assertEqual(statement.count('InfRules '), 2)
        self.assertIn('(sseq(sprim encrit)(sseq(sassign', statement)
        self.assertIn('(sseq(sprim excrit)tail)))', statement)
        self.assertEqual(whole.count('eapply seq_rule'), 3)

    def test_typed_hook_real_call_and_argument(self):
        call = self.section('V293_tcb_priority_first_hook')
        self.assertEqual(call.split('Proof.')[0].count('InfRules '), 1)
        self.assertIn('eapply call_rule', call)
        self.assertIn('apply V293_tcb_priority_argument', call)
        self.assertIn('V293_tcb_enabled_hook_fpre', call)
        self.assertIn('V293_tcb_priority_resources table bprio bp', call)
        self.assertIn('V293_tcb_init_read H1 1%nat Load', self.source)
        self.assertNotIn('hoare_skip', call)

    def test_suffix_remaining_premise_starts_at_second_hook(self):
        suffix = self.section('V293_OS_TCBInit_owned_suffix_after_first_hook')
        statement = suffix.split('Proof.')[0]
        self.assertEqual(statement.count('InfRules '), 2)
        self.assertIn('(sseq(scall hc[evar 108%Z])(V293_TCB_publish', statement)
        self.assertIn('(V293_TCBInit_success_suffix hi hc)', statement)
        self.assertIn('(b,off)<>reserved', statement)
        self.assertNotIn('(scall hi', statement)
        self.assertIn('apply V293_tcb_priority_first_hook', suffix)
        self.assertIn('apply V293_OS_TCBInit_owned_priority_then', suffix)

    def test_literal_input_same_inv_and_store_omission(self):
        self.assertNotRegex(self.probe, r'Definition \w+ : Inv :=')
        for name in ['OPWholeLiteral', 'OPActualArgument', 'OPBracketChecked',
                     'OPSameInvariantBeforeAfter', 'OPActualReservedRead',
                     'OPWrittenSlotRead', 'OPOmittedSlotRead', 'OPOmittedSlotDiffers']:
            self.assertRegex(self.probe, r'Theorem ' + name + r' :')
        self.assertIn('V293_witness_li ROInv', self.probe)
        self.assertIn('apply ROOwnedBorrowEquivalence', self.probe)
        self.assertIn('if write then store', self.probe)
        self.assertIn('else Some OPWhole', self.probe)
        controls = json.loads((D / 'controls.json').read_text())
        self.assertTrue(controls['passed'])
        self.assertEqual([r['exit'] for r in controls['rows']], [0, 1])
        self.assertTrue(all(r['common_input_checked'] for r in controls['rows']))

    def test_stable_compiles_and_prospective_protocol(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('proof', SOURCE), ('probe', PROBE)]:
            label = stable[kind]
            row = json.loads((D / (label + '.json')).read_text())
            content = (ROOT / path).read_bytes()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(hashlib.sha256(content).hexdigest(), row['source_sha256'])
            self.assertEqual(content, (D / (label + '.v.snapshot.txt')).read_bytes())
        self.assertLessEqual((D / 'protocol.json').stat().st_mtime_ns,
                             (D / 'proof01.v.snapshot.txt').stat().st_mtime_ns)
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertIn('C/AST/config/framework/old frozen evidence/gates94/1/1/1/1/0', protocol['unchanged'])
        self.assertIn('fresh node distinct from reserved is explicit premise, not yet production allocator invariant', protocol['limitations'])


if __name__ == '__main__':
    unittest.main()
