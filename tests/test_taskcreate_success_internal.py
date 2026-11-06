"""成功侧真实函数构造器的结构回归；不替代 Coq 内核检查。"""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskCreateSuccessInternal.v'


class TaskCreateSuccessInternalTests(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / SOURCE).read_text()
        self.public = self.text.split('Theorem V293_OSTaskCreateExt_success_internal_contract :')[1].split('Proof.')[0]

    def test_real_builders_original_body_and_vertical_reuse(self):
        for term in ['BuildPreI P creator vl lg', 'BuildRetI P creator vl lg',
                     'V293_CreateExt_function 92%Z 99%Z 97%Z 98%Z',
                     'V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z',
                     'V293_OSTaskCreateExt_success_body_hoare',
                     'V293_create_internal_unpack', 'V293_create_internal_buildp',
                     'V293_create_internal_post_cells', 'V293_create_internal_pre_to_post']:
            self.assertIn(term, self.text)

    def test_exact_null_entry_and_reserved_snapshot(self):
        self.assertIn('V293_tcb_success_pre_owned table Vnull', self.public)
        self.assertIn('V293_tcb_success_pre_owned table(Vptr(breserved,Int.zero))', self.public)
        self.assertIn('V293_create_success_entry', self.text)
        self.assertIn('V293_create_success_body_frame cells', self.text)

    def test_return_retains_whole_callee_and_all_cells(self):
        post = self.text.split('Definition V293_create_success_fpost ')[1].split('Lemma ')[0]
        self.assertIn('getasrt(fq arguments(Some(Vint32 Int.zero))[logic_val head]tid)', post)
        self.assertIn('V293_create_success_saved bnest breserved brun', post)
        self.assertIn('V293_create_success_kept_return', self.text)
        self.assertIn('LV 109%Z @ Tint32 |->Vint32 Int.zero', self.text)
        self.assertIn('V293_create_success_exit', self.text)

    def test_no_shadow_from_exact_domain_and_no_local_fun_assertions(self):
        self.assertIn('eq_dom_env le(getlenvdom V293_create_internal_declarations)', self.text)
        self.assertIn('(91<=x<=99)%Z -> get le x=None', self.text)
        for name in ['fpre', 'fpost']:
            part = self.text.split('Definition V293_create_success_' + name + ' ')[1].split('Lemma ')[0]
            for bad in ['Alvarenv', 'LV ', 'A_notin_lenv', 'A_dom_lenv']:
                self.assertNotIn(bad, part)
        self.assertIn('V293_create_internal_domain', self.text)

    def test_full_snapshot_no_execution_or_hoare_oracle(self):
        self.assertEqual(self.public.count('InfRules '), 1)
        self.assertEqual(self.public.count('Spec hook=Some('), 1)
        self.assertEqual(self.public.count('Spec f=Some('), 1)
        for branch in ['empty', 'success']:
            for part in ['fpre', 'fpost']:
                self.assertIn(f'V293_tcb_{branch}_{part}', self.public)
        self.assertNotRegex(self.public, r'\b(?:evalval|evaladdr|load|sfexec|WFIFun)\b')

    def test_no_holes_or_probe_dependencies_and_project_once(self):
        self.assertNotRegex(self.text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.probes.', self.text)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)


if __name__ == '__main__':
    unittest.main()
