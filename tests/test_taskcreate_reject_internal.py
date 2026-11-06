"""三类拒绝分支的结构回归；实际证明由 Coq/coqchk 检查。"""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskCreateRejectInternal.v'


class TaskCreateRejectInternalTests(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / SOURCE).read_text()
        self.public = self.text.split('Theorem V293_OSTaskCreateExt_rejection_internal_contract :')[1].split('Proof.')[0]

    def test_three_original_codes(self):
        for term in ['V293_create_bad_priority=>42%Z', 'V293_create_from_isr=>60%Z',
                     'V293_create_occupied_priority=>40%Z']:
            self.assertIn(term, self.text)

    def test_real_builders_original_body_and_all_cells(self):
        for term in ['BuildPreI P creator vl lg', 'BuildRetI P creator vl lg',
                     'V293_CreateExt_function 92%Z 99%Z 97%Z 98%Z',
                     'V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z',
                     'V293_create_internal_unpack', 'V293_create_internal_buildp',
                     'V293_create_internal_post_cells', 'V293_create_internal_pre_to_post']:
            self.assertIn(term, self.text)

    def test_guards_from_owned_bytes_and_critical_restore(self):
        for name in ['priority', 'nesting', 'slot', 'cpu', 'enter', 'exit', 'ret']:
            self.assertIn('Lemma V293_create_rejection_' + name + ' :', self.text)
        self.assertIn('(false::cs)', self.text)
        self.assertIn('V293_OSTaskCreateExt_rejection_body_hoare', self.text)

    def test_public_no_hook_or_execution_oracle(self):
        self.assertEqual(self.public.count('InfRules '), 1)
        self.assertNotIn('Spec ', self.public.split('InfRules ')[0].split(' ->', 1)[-1])
        for term in ['Spec f=', 'Spec hook=', 'evalval', 'evaladdr', 'sfexec', 'WFIFun', 'V293_tcb_success_pre_owned']:
            self.assertNotIn(term, self.public)

    def test_minimal_branch_resources_and_no_local_fun_assertions(self):
        extra = self.text.split('Definition V293_create_rejection_extra_cells ')[1].split('Definition ')[0]
        self.assertIn('V293_create_bad_priority=>[]', extra)
        self.assertIn('Vptr slot', extra)
        for name in ['fpre', 'fpost']:
            part = self.text.split('Definition V293_create_reject_' + name + ' ')[1].split('Lemma ')[0]
            for bad in ['Alvarenv', 'LV ', 'A_notin_lenv', 'A_dom_lenv']:
                self.assertNotIn(bad, part)
        self.assertIn('V293_create_internal_domain', self.text)

    def test_no_holes_probe_imports_or_duplicate_project(self):
        self.assertNotRegex(self.text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.probes.', self.text)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)


if __name__ == '__main__':
    unittest.main()
