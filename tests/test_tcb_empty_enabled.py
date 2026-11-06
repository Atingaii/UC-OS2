"""开启中断空池接口的结构回归；不替代 Coq，也不授予整核信用。"""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TCBEmptyEnabled.v'


class TCBEmptyEnabledTests(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / SOURCE).read_text()
        self.public = self.text.split('Theorem V293_OS_TCBInit_empty_enabled_contract :')[1].split('Proof.')[0]

    def test_enabled_caller_does_not_own_shared_head(self):
        resources = self.text.split('Definition V293_tcb_enabled_resources ')[1].split('Definition ')[0]
        external = self.text.split('Definition V293_tcb_enabled_external ')[1].split('Lemma ')[0]
        self.assertNotIn('Amapsto(bf,', resources)
        self.assertNotIn('Amapsto', external)
        self.assertIn('OS[isr,true,is,cs]', external)
        pool = self.text.split('Definition V293_tcb_empty_pool ')[1].split('Definition ')[0]
        self.assertIn('(Tptr V293_tcb_type)false Vnull ** K', pool)

    def test_actual_borrow_close_restore_same_interrupt_state(self):
        for name in ['apply encrit1_rule', 'apply excrit1_rule', 'true::ci',
                     'V293_tcb_enabled_enter', 'V293_tcb_enabled_exit']:
            self.assertIn(name, self.text)
        self.assertEqual(self.public.count('V293_tcb_empty_pool bf K'), 2)
        self.assertIn('Aisr isr ** invlth_isr I 0(gettopis is)', self.public)
        external = self.text.split('Definition V293_tcb_enabled_external ')[1].split('Lemma ')[0]
        self.assertNotIn(' K', external)

    def test_full_original_body_actual_null_load_guard_return(self):
        body = self.text.split('Theorem V293_OS_TCBInit_empty_enabled_body :')[1].split('Print Assumptions')[0]
        for name in ['V293_TCBInit_function_body hi hc', 'V293_tcb_enabled_cpu',
                     'V293_tcb_empty_pointer_hoare', 'V293_tcb_empty_guard_eval',
                     'V293_tcb_enabled_exit', 'apply rete_rule', 'Int.repr 66']:
            self.assertIn(name, body)
        original = (ROOT / 'certiucos/v293/code/V293OSTCBInitFunction.v').read_text()
        self.assertIn('V293_TCBInit_prefix', original)
        self.assertIn('V293_TCBInit_success_suffix', original)

    def test_real_builders_and_exact_domain(self):
        for name in ['BuildPreI', 'BuildRetI', 'P f=Some(V293_TCBInit_function hi hc)']:
            self.assertIn(name, self.public)
        for name in ['dl_vl_match', 'V293_tcb_internal_buildp', 'V293_tcb_empty_internal_bindings',
                     'V293_tcb_internal_post_cells', 'V293_tcb_internal_domain']:
            self.assertIn(name, self.text)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

    def test_no_execution_oracle_holes_or_audit_imports(self):
        self.assertNotRegex(self.text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.', self.text)
        self.assertEqual(self.public.count('InfRules '), 1)
        self.assertNotRegex(self.public, r'\b(?:evalval|evaladdr|load|loststep|sfexec|WFIFun)\b')

    def test_independent_literal_partition_and_same_invariant(self):
        probe = (ROOT / 'audit/probes/V293TCBEmptyEnabledProbe.v').read_text()
        self.assertNotIn('CertiOS.audit.probes.', probe)
        self.assertEqual(len(re.findall(r'^Definition \w+ : Inv :=', probe, re.M)), 1)
        for name in ['ENLiteralBuilderEntry', 'ENBuilders', 'ENSharedLiteral', 'ENCallerHasNoHead',
                     'ENWholePartition', 'ENWholeSpatial', 'ENBorrowEquivalence', 'ENContractChecked']:
            self.assertIsNotNone(re.search(rf'^(?:Lemma|Theorem) {name} :', probe, re.M))
        self.assertIn('InfRules(fun _=>None)sd V293_witness_li ENInv', probe)
        self.assertIn('forall vl l permission m1 m2', probe)


if __name__ == '__main__':
    unittest.main()
