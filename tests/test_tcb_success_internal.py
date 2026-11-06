"""成功路径标准构造器接口的结构回归；不替代 Coq 内核检查。"""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
PROOF = ROOT / 'certiucos/v293/proofs/V293TCBSuccessInternal.v'


class TCBSuccessInternalTests(unittest.TestCase):
    def setUp(self):
        self.text = PROOF.read_text()

    def test_real_builders_and_no_body_oracle(self):
        statement = self.text.split('Theorem V293_OS_TCBInit_success_internal_contract :')[1].split('Proof.')[0]
        self.assertIn('Some pre=BuildPreI P f vl lg', statement)
        self.assertIn('Some post=BuildRetI P f vl lg', statement)
        self.assertEqual(statement.count('InfRules '), 1)
        self.assertNotRegex(statement, r'\b(?:evalval|evaladdr|sfexec|V293_stmt_exec|WFIFun)\b')

    def test_external_resource_has_no_caller_locals(self):
        for start, end in [('Definition V293_tcb_success_global_bindings', 'Lemma '),
                           ('Definition V293_tcb_success_external', 'Lemma ')]:
            part = self.text.split(start)[1].split(end)[0]
            self.assertNotRegex(part, r'\b(?:Alvarenv|LV|A_notin_lenv|A_dom_lenv)\b')
        self.assertIn('GoodFunAsrt R', self.text)

    def test_nine_local_bindings_and_both_pack_directions(self):
        part = self.text.split('Definition V293_tcb_success_local_bindings')[1].split('Definition ')[0]
        for ident in range(101, 110):
            self.assertEqual(part.count(f'Alvarenv {ident}%Z'), 1)
        for lemma in ['internal_unpack', 'internal_pack', 'internal_prepack']:
            self.assertIn(f'Lemma V293_tcb_success_{lemma} :', self.text)
        self.assertIn('V293_tcb_internal_post_cells **', self.text)

    def test_domain_derived_no_shadow_and_caller_frame(self):
        part = self.text.split('Lemma V293_tcb_internal_no_shadow_globals :')[1].split('Qed.')[0]
        self.assertIn('eq_dom_env le (getlenvdom V293_tcb_internal_declarations)', part)
        self.assertIn('get le x=None', part)
        self.assertIn('frame_rule_all', self.text)
        self.assertIn('GoodI I sd li', self.text)

    def test_two_real_hook_spec_obligations_remain(self):
        statement = self.text.split('Theorem V293_OS_TCBInit_success_internal_contract :')[1].split('Proof.')[0]
        self.assertEqual(statement.count('Spec hi=Some('), 1)
        self.assertEqual(statement.count('Spec hc=Some('), 1)
        self.assertIn('eapply V293_OS_TCBInit_hook_calls_body_hoare', self.text)

    def test_no_holes_no_probe_import_and_active_source(self):
        self.assertNotRegex(self.text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort)\b')
        self.assertNotIn('CertiOS.audit.probes.', self.text)
        project = (ROOT / '_CoqProject').read_text().splitlines()
        self.assertEqual(project.count(str(PROOF.relative_to(ROOT))), 1)


if __name__ == '__main__':
    unittest.main()
