"""Source-structure regressions; machine proof evidence is recorded separately."""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
PROOF = ROOT / 'certiucos/v293/proofs/V293TCBEmptyHoare.v'
PROBE = ROOT / 'audit/probes/V293TCBEmptyHoareProbe.v'

class TCBEmptyHoareTests(unittest.TestCase):
    def test_no_new_assumptions(self):
        for path in [PROOF, PROBE]:
            self.assertIsNone(re.search(r'\b(Axiom|Parameter|Conjecture|Admitted|admit)\b', path.read_text()))

    def test_real_complete_body_used_by_both_interfaces(self):
        text = PROOF.read_text()
        for name in ['V293_OS_TCBInit_empty_body_hoare', 'V293_OS_TCBInit_empty_body_semantics']:
            tail = text[text.index('Theorem ' + name):]
            statement = tail[:tail.index('Proof.')]
            self.assertIn('(V293_TCBInit_function_body hi hc) Afalse tid', statement)
            self.assertIn('GoodFrm R -> (R ==> CurLINV li tid)', statement)
        self.assertIn('apply RuleSound', text)

    def test_failure_body_is_not_a_hook_contract(self):
        text = PROOF.read_text()
        self.assertIn('apply encrit2_rule', text)
        self.assertIn('apply excrit2_rule', text)
        self.assertIn('eapply ift_rule', text)
        self.assertIn('apply pfalse_rule', text)
        self.assertNotIn('V293_records_hook_return', text)
        self.assertNotIn('call_rule', text)

    def test_readonly_head_disabled_entry_and_return_66(self):
        text = PROOF.read_text()
        self.assertIn('(Tptr V293_tcb_type) false Vnull', text)
        self.assertIn('OS[isr,false,is,cs]', text)
        self.assertIn('result=Some(Vint32(Int.repr 66))', text)

    def test_nonvacuity_and_distinct_controls_retained(self):
        text = PROBE.read_text()
        for name in ['EmptyLiteralEntry', 'EmptyBodyNoHook', 'EmptyPostRejectZero', 'EmptyGuardNotTrue']:
            self.assertIn('Theorem ' + name, text)
        self.assertIn('Definition EmptyNoHookSpec : funspec := fun _=>None', text)
        self.assertIn('Definition EmptySentinel', text)
        self.assertNotRegex(text, r'Require Import CertiOS\.audit\.probes\.')

    def test_exactly_once_in_active_build(self):
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(str(PROOF.relative_to(ROOT))), 1)

if __name__ == '__main__':
    unittest.main()
