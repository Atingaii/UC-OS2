"""发布所有权接口的结构回归；语义证据来自 Coq 编译与 coqchk。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TCBPublicationPool.v'
PROBE = 'audit/probes/V293TCBPublicationPoolProbe.v'
D = ROOT / 'audit/logs/stage121-tcb-publication-pool'


class TCBPublicationPoolTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / SOURCE).read_text()
        self.probe = (ROOT / PROBE).read_text()

    def section(self, name):
        return self.source.split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_no_holes_or_audit_import(self):
        for content in [self.source, self.probe]:
            self.assertNotRegex(content, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.', self.source)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

    def test_actual_body_not_a_hoare_continuation_premise(self):
        body = self.section('V293_OS_TCBInit_publish_pool_body')
        signature = body.split('Proof.')[0]
        self.assertEqual(signature.count('InfRules '), 1)
        self.assertIn('(V293_TCB_publish_body ptcb head group rows counter)', signature)
        for token in ['V293_tcb_publication_prepare', 'V293_tcb_publication_finish',
                      'V293_OS_TCBInit_publish_body_hoare']:
            self.assertIn(token, body)
        self.assertNotIn('encrit2_rule', self.source)
        self.assertNotIn('excrit2_rule', self.source)

    def test_full_storage_layout_and_typed_preserved_tail(self):
        self.assertIn('Lemma V293_tcb_active_payload_layout :', self.source)
        layout = self.section('V293_tcb_active_payload_layout')
        self.assertIn('Permutation', layout)
        self.assertIn('V293_tcb_free_payload_cells b base', layout)
        self.assertIn('(base+24)%Z', layout)
        chain = self.source.split('Fixpoint V293_tcb_active_chain', 1)[1].split('Definition V293_tcb_publication_pool', 1)[0]
        for text in ['O=>[|head=Vnull|]', 'V293_tcb_active_payload',
                     'rule_type_val_match(Tcom_ptr 410%Z)next=true',
                     'V293_tcb_active_chain k head next', '(Int.unsigned off+55<=Int.max_unsigned)%Z']:
            self.assertIn(text, chain)
        tail = self.source.split('Definition V293_tcb_publication_old_tail', 1)[1].split('Definition V293_tcb_publication_frame', 1)[0]
        self.assertIn('[|rule_type_val_match(Tcom_ptr 410%Z)next=true|]', tail)

    def test_both_rows_counter_and_counted_chain_preserved(self):
        pool = self.source.split('Definition V293_tcb_publication_pool', 1)[1].split('Definition V293_tcb_publication_new', 1)[0]
        self.assertIn('(br,Z.of_nat y)', pool)
        self.assertIn('(br,Z.of_nat(1-y))', pool)
        self.assertIn('V293_byteval n', pool)
        self.assertIn('V293_tcb_active_chain n Vnull head', pool)
        signature = self.section('V293_OS_TCBInit_publish_pool_body').split('Proof.')[0]
        for text in ['y<2 -> x<8', '(if present then S k else O)<255',
                     '(S(if present then S k else O))(Nat.setbit g y)(Nat.setbit row x)other R']:
            self.assertIn(text, signature)

    def test_real_initialized_node_supplies_same_bytes(self):
        body = self.section('V293_tcb_publication_initialized_view')
        self.assertIn('V293_tcb_allocated_initialized b off next p top bottom identity size ext options ==>', body)
        self.assertIn('EX prev:val,V293_tcb_publication_new', body)
        self.assertNotIn('InfRules ', body)
        self.assertNotIn('reserved', body)

    def test_literal_null_two_node_and_both_selected_rows(self):
        for text in ['Theorem PPLiteralInput : forall (present upper:bool) cs,',
                     'Theorem PPBodyChecked :', 'PPNodeRows 511%positive Vnull PPTail',
                     'PPNodeRows 512%positive PPOld Vnull', 'if upper then 1 else 0',
                     'apply PPLiteralRaw', 'V293_OS_TCBInit_publish_pool_body']:
            self.assertIn(text, self.probe)
        self.assertNotRegex(self.probe, r'Definition \w+ : Inv :=')

    def test_backlink_control_checks_real_store_and_full_pre_first(self):
        controls = json.loads((D / 'controls.json').read_text())
        self.assertTrue(controls['passed'])
        self.assertEqual([r['exit'] for r in controls['rows']], [0, 1])
        normal = (D / 'Normal.v.snapshot.txt').read_text()
        omitted = (D / 'Omitted.v.snapshot.txt').read_text()
        self.assertEqual(normal.replace('perform_write : bool := true', 'perform_write : bool := false'), omitted)
        for row in controls['rows']:
            self.assertTrue(row['common_input_checked'])
        for name in ['PPBackStoreChecked', 'PPFinalChainBacklink', 'PPOmittedBreaksFinalChain']:
            self.assertRegex(self.probe, r'(?:Theorem|Lemma) ' + name + r' :')
        log = (D / 'Omitted.log').read_text()
        self.assertLess(log.index('COMMON_INPUT_CHECKED'), log.index('Error:'))

    def test_stable_compile_and_prospective_protocol(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('proof', SOURCE), ('probe', PROBE)]:
            label = stable[kind]
            row = json.loads((D / (label + '.json')).read_text())
            data = (ROOT / path).read_bytes()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(hashlib.sha256(data).hexdigest(), row['source_sha256'])
            self.assertEqual(data, (D / (label + '.v.snapshot.txt')).read_bytes())
        self.assertLessEqual((D / 'protocol.json').stat().st_mtime_ns,
                             (D / 'proof01.v.snapshot.txt').stat().st_mtime_ns)

    def test_unchanged_gates_and_explicit_global_limits(self):
        rows = json.loads((ROOT / 'audit/coverage.json').read_text())['rows']
        self.assertEqual([sum(bool(row[k]) for row in rows) for k in
                          ['located', 'modeled', 'specified', 'local_hoare', 'component_linked', 'full_target_linked']],
                         [94, 1, 1, 1, 1, 0])
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertIn('physical chain ownership alone is not production task-map/ready relation', protocol['limitations'])
        self.assertNotIn('GOOD_OS', self.section('V293_OS_TCBInit_publish_pool_body').split('Proof.')[0])


if __name__ == '__main__':
    unittest.main()
