"""真实取出的 TCB 接原字段初始化：结构门，不替代 Coq 语义核验。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TCBAllocatedFields.v'
PROBE = 'audit/probes/V293TCBAllocatedFieldsProbe.v'
D = ROOT / 'audit/logs/stage116-tcb-allocated-fields'


class TCBAllocatedFieldsTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / SOURCE).read_text()
        self.probe = (ROOT / PROBE).read_text()

    def test_no_holes_and_audit_dependency_is_probe_only(self):
        for text in [self.source, self.probe]:
            self.assertNotRegex(text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.', self.source)
        self.assertEqual(self.probe.count('Require Import CertiOS.audit.'), 1)
        self.assertIn('Require Import CertiOS.audit.probes.V293TCBFreePoolProbe.', self.probe)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

    def test_old_values_are_derived_from_owned_payload(self):
        statement = self.source.split('Lemma V293_tcb_allocated_payload_open :')[1].split('Proof.')[0]
        self.assertIn('V293_tcb_free_payload b base ==>', statement)
        self.assertIn('EX old:Z->val', statement)
        self.assertNotIn('forall old', statement)
        body = self.source.split('Lemma V293_tcb_allocated_payload_open :')[1].split('Qed.')[0]
        self.assertIn('destruct H as (v0&v1&v2', body)
        offsets = re.findall(r'^ \| (\d+)%Z=>v\d+', body, re.M)
        self.assertEqual(len(offsets), 18)
        self.assertEqual(len(set(offsets)), 18)

    def test_unwritten_bytes_and_next_are_framed_without_shared_head(self):
        spares = self.source.split('Definition V293_tcb_allocated_spares ')[1].split('Lemma ')[0]
        self.assertEqual(re.findall(r'base\+(\d+)', spares), ['24', '40', '42', '43'])
        remainder = self.source.split('Definition V293_tcb_allocated_remainder ')[1].split('Definition ')[0]
        self.assertIn('V293_tcb_allocated_spares', remainder)
        self.assertIn('Int.unsigned off+20', remainder)
        frame = self.source.split('Definition V293_tcb_allocated_field_frame ')[1].split('Lemma ')[0]
        self.assertIn('V293_tcb_allocated_remainder b off next ** R', frame)
        self.assertNotIn('Amapsto(bf,', frame)
        self.assertNotIn('V293_tcb_free_pool', frame)

    def test_closed_pop_exit_and_all_original_fields(self):
        public = self.source.split('Lemma V293_tcb_free_pop_fields :')[1].split('Proof.')[0]
        self.assertEqual(public.count('InfRules '), 1)
        self.assertNotRegex(public, r'\b(?:evalval|evaladdr|load|loststep|sfexec|WFIFun)\b')
        self.assertNotIn('success_suffix', public)
        self.assertIn('(sseq(V293_TCBInit_pop 91%Z 108%Z)(sseq(sprim excrit)', public)
        self.assertIn('V293_TCBInit_fields 108%Z 101%Z', public)
        self.assertIn('V293_tcb_allocated_initialized b off next', public)
        self.assertIn('EX next:val', public)

    def test_whole_body_premise_starts_after_fields_not_before(self):
        public = self.source.split('Theorem V293_OS_TCBInit_free_body_after_fields :')[1].split('Proof.')[0]
        self.assertEqual(public.count('InfRules '), 2)
        self.assertIn('V293_tcb_allocated_initialized b off next', public)
        self.assertIn('V293_TCBInit_success_suffix hi hc', public)
        self.assertIn('V293_TCBInit_function_body hi hc', public)
        self.assertNotIn('V293_TCBInit_fields ', public)
        self.assertIn('r(Some(Vint32(Int.repr 66)))', public)
        self.assertIn('apply V293_OS_TCBInit_free_body_with_success', self.source)

    def test_same_frozen_inv_and_literal_inputs(self):
        self.assertNotRegex(self.probe, r'Definition \w+ : Inv :=')
        for name in ['AFActualPopInput', 'AFPopFieldsChecked', 'AFPrivateFieldsSpatial', 'AFWholeEnabledLiteral']:
            self.assertRegex(self.probe, r'Theorem ' + name + r' :')
        self.assertIn('V293_witness_li FPInv', self.probe)
        self.assertIn('apply V293_tcb_free_pop_fields', self.probe)
        self.assertIn('apply FPBorrowEquivalence', self.probe)
        self.assertIn('apply FPWholeEnabledLiteral', self.probe)

    def test_enabled_caller_has_no_shared_bytes(self):
        self.assertIn('Lemma AFCallerNoShared :', self.probe)
        self.assertIn('b=401%positive \/ b=501%positive \/ b=502%positive', self.probe)
        self.assertIn('rewrite FPCallerNoShared by exact B.', self.probe)
        self.assertIn('Theorem AFPrivateNoSharedHead :', self.probe)

    def test_priority_store_has_positive_semantic_omission_counterexample(self):
        for name in ['AFActualPriorityRead', 'AFInputPriorityRead', 'AFWrittenPriorityRead', 'AFOmittedPriorityDiffers']:
            self.assertRegex(self.probe, r'(?:Lemma|Theorem) ' + name + r' :')
        self.assertIn('store Tint8 AFFieldsInput(501%positive,50%Z)(V293_byteval 5)', self.probe)
        self.assertIn('rewrite AFActualPriorityRead. discriminate.', self.probe)

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
        self.assertIn('not Hook/publication/return0', protocol['limitations'])


if __name__ == '__main__':
    unittest.main()
