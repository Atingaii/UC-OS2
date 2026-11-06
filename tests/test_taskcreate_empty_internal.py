"""真实 TaskCreateExt 标准构造器接口；结构回归不替代 Coq 语义检查。"""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskCreateEmptyInternal.v'


class TaskCreateEmptyInternalTests(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / SOURCE).read_text()
        self.public = self.text.split('Theorem V293_OSTaskCreateExt_empty_internal_contract :')[1]

    def test_real_builders_and_original_full_body(self):
        for term in ['BuildPreI P creator vl lg', 'BuildRetI P creator vl lg',
                     'V293_CreateExt_function 92%Z 99%Z 97%Z',
                     '(V293_CreateExt_body 92%Z 99%Z 97%Z running sched hook f)',
                     'V293_OSTaskCreateExt_empty_body_hoare']:
            self.assertIn(term, self.text)

    def test_all_twelve_cells_preserved_in_actual_order(self):
        post = self.text.split('Definition V293_create_internal_post_cells :=')[1].split('Lemma ')[0]
        order = ['204', '208', '207', '205', '206', '101', '203', '202', '201']
        indices = [post.index('LV ' + x + '%Z') for x in order]
        self.assertEqual(indices, sorted(indices))
        locals_ = self.text.split('Definition V293_create_internal_locals :=')[1].split('Definition ')[0]
        self.assertLess(locals_.index('108%Z'), locals_.index('209%Z'))
        self.assertLess(locals_.index('209%Z'), locals_.index('109%Z'))
        for term in ['V293_create_internal_buildp', 'V293_create_internal_buildq',
                     'V293_create_internal_pre_to_post', 'V293_create_internal_exit']:
            self.assertIn(term, self.text)

    def test_external_specs_do_not_expose_local_bindings(self):
        external = self.text.split('Definition V293_create_internal_external ')[1].split('Lemma ')[0]
        for bad in ['Alvarenv', 'A_notin_lenv', 'LV ', 'A_dom_lenv']:
            self.assertNotIn(bad, external)
        for name in ['fpre', 'fpost']:
            part = self.text.split('Definition V293_create_empty_' + name + ' ')[1].split('\nLemma ')[0]
            self.assertNotIn('Alvarenv', part)
            self.assertNotIn('A_notin_lenv', part)

    def test_no_shadow_derived_from_exact_domain(self):
        self.assertIn('eq_dom_env le(getlenvdom V293_create_internal_declarations)', self.text)
        self.assertIn('V293_create_internal_no_shadow _ 92%Z Domain', self.text)
        self.assertIn('V293_create_internal_no_shadow _ 99%Z Domain', self.text)
        self.assertIn('V293_create_internal_no_shadow _ 97%Z Domain', self.text)
        self.assertIn('V293_create_internal_domain', self.public)

    def test_public_is_bounded_not_an_execution_oracle(self):
        part = self.public.split('Proof.')[0]
        self.assertEqual(part.count('InfRules '), 1)
        self.assertEqual(part.count('Spec hook=Some('), 1)
        self.assertEqual(part.count('Spec f=Some('), 1)
        self.assertIn('GoodFrm Rbefore -> GoodFrm R -> p<13 ->', part)
        for branch in ['empty', 'success']:
            for section in ['fpre', 'fpost']:
                self.assertIn(f'V293_tcb_{branch}_{section}', part)
        self.assertNotRegex(part, r'\b(?:evalval|evaladdr|load|sfexec|WFIFun)\b')

    def test_no_holes_probe_dependency_or_duplicate_project_entry(self):
        self.assertNotRegex(self.text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.probes.', self.text)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)


if __name__ == '__main__':
    unittest.main()
