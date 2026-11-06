"""标准函数构造器连接的结构回归；Coq 探针另检验可满足性和接口类型。"""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
PROOF = ROOT / 'certiucos/v293/proofs/V293TCBEmptyInternal.v'


class TCBEmptyInternalTests(unittest.TestCase):
    def setUp(self):
        self.text = PROOF.read_text()

    def test_standard_builders(self):
        statement = self.text.split('Theorem V293_OS_TCBInit_empty_internal_contract :')[1].split('Proof.')[0]
        self.assertIn('Some pre=BuildPreI P f vl lg', statement)
        self.assertIn('Some post=BuildRetI P f vl lg', statement)
        self.assertEqual(statement.count('InfRules '), 1)
        self.assertNotRegex(statement, r'\b(?:evalval|V293_local_steps|WFIFun)\b')

    def test_all_parameters_and_locals_returned(self):
        post = self.text.split('Definition V293_tcb_internal_post_cells :=')[1].split('Lemma ')[0]
        for ident in range(101, 108):
            self.assertEqual(post.count(f'LV {ident}%Z'), 1)
        self.assertIn('V293_tcb_internal_locals', post)
        locals_ = self.text.split('Definition V293_tcb_internal_locals :=')[1].split('Definition ')[0]
        self.assertIn('EX pc : val, LV 108%Z', locals_)
        self.assertIn('EX cpu : val, LV 109%Z', locals_)

    def test_no_shadow_derived_from_exact_declarations(self):
        lemma = self.text.split('Lemma V293_tcb_internal_no_shadow :')[1].split('Qed.')[0]
        self.assertIn('eq_dom_env le (getlenvdom V293_tcb_internal_declarations)', lemma)
        self.assertIn('get le 91%Z=None', lemma)
        self.assertIn('proj2(Domain 91%Z tp)', lemma)

    def test_external_specs_have_no_locals(self):
        resource = self.text.split('Definition V293_tcb_empty_external ')[1].split('Lemma ')[0]
        self.assertNotRegex(resource, r'\b(?:Alvarenv|LV|A_notin_lenv|A_dom_lenv)\b')
        self.assertIn('false Vnull', resource)
        self.assertIn('GoodFunAsrt R', self.text)

    def test_empty_path_needs_no_hook_lookup(self):
        statement = self.text.split('Theorem V293_OS_TCBInit_empty_internal_contract :')[1].split('Proof.')[0]
        self.assertNotIn('Spec hi=', statement)
        self.assertNotIn('Spec hc=', statement)
        self.assertIn('apply V293_OS_TCBInit_empty_body_hoare', self.text)

    def test_no_proof_holes_or_old_probe_dependency(self):
        self.assertNotRegex(self.text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort)\b')
        self.assertNotIn('CertiOS.audit.probes.', self.text)
        project = (ROOT / '_CoqProject').read_text().splitlines()
        self.assertEqual(project.count(str(PROOF.relative_to(ROOT))), 1)


if __name__ == '__main__':
    unittest.main()
