"""接口结构回归；不代替 Coq 的资源、语义和内核检查。"""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskCreateDynamicReject.v'


class TaskCreateDynamicRejectTests(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / SOURCE).read_text()
        self.public = self.text.split('Theorem V293_OSTaskCreateExt_dynamic_rejection_contract :')[1].split('Proof.')[0]

    def test_no_entry_class_nesting_or_slot(self):
        binders = self.public.split('p<13 ->')[0]
        self.assertNotRegex(binders, r'\b(?:k|n|slot)\b')
        self.assertIn('V293_create_reject_pool table bn p K', self.public)
        pool = self.text.split('Definition V293_create_reject_pool ')[1].split('Definition ')[0]
        self.assertIn('EX n:nat, EX slot:addrval', pool)

    def test_open_exists_only_after_acquire(self):
        body = self.text.split('Theorem V293_OSTaskCreateExt_dynamic_rejection_body :')[1]
        self.assertLess(body.index('eapply V293_create_dynamic_enter'), body.index('intro n.'))
        self.assertLess(body.index('intro n.'), body.index('destruct n as [ | n]'))
        self.assertIn('apply encrit1_rule', self.text)
        self.assertIn('eapply V293_create_enabled_exit', self.text)

    def test_standard_builders_original_body_and_domain(self):
        for term in ['BuildPreI P creator vl lg', 'BuildRetI P creator vl lg',
                     'V293_CreateExt_function 92%Z 99%Z 97%Z 98%Z',
                     'V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z']:
            self.assertIn(term, self.public)
        self.assertIn('V293_create_internal_buildp', self.text)
        self.assertIn('V293_create_internal_domain', self.text)

    def test_no_oracle_or_holes(self):
        self.assertEqual(self.public.count('InfRules '), 1)
        self.assertNotRegex(self.public, r'\b(?:evalval|evaladdr|load|loststep|sfexec|WFIFun)\b')
        self.assertNotRegex(self.text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.probes.', self.text)

    def test_both_branches_close_same_pool_and_owned_guards(self):
        for term in ['V293_create_dynamic_isr_close', 'V293_create_dynamic_occupied_close',
                     'V293_create_rejection_nesting', 'V293_create_rejection_slot',
                     'Some(Vint32(Int.repr 60))', 'Some(Vint32(Int.repr 40))']:
            self.assertIn(term, self.text)

    def test_registered_once_and_one_probe_invariant(self):
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)
        probe = (ROOT / 'audit/probes/V293TaskCreateDynamicRejectProbe.v').read_text()
        self.assertIn('Definition DRInv : Inv', probe)
        self.assertIn('forall n,n<256 -> RIState(DRExtra n) |= invlth_isr DRInv', probe)
        self.assertIn('DRTypedNestingGuard', probe)


if __name__ == '__main__':
    unittest.main()
