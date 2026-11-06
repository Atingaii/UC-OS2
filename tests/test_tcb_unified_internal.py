"""统一函数契约的结构回归；不替代 Coq 或整核覆盖验收。"""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TCBUnifiedInternal.v'


class TCBUnifiedInternalTests(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / SOURCE).read_text()

    def test_public_contract_has_real_builders_and_no_branch_oracle(self):
        statement = self.text.split('Theorem V293_OS_TCBInit_internal_contract :')[1].split('Proof.')[0]
        self.assertIn('Some pre=BuildPreI P f vl lg', statement)
        self.assertIn('Some post=BuildRetI P f vl lg', statement)
        self.assertEqual(statement.count('InfRules '), 1)
        self.assertNotRegex(statement, r'\b(?:evalval|evaladdr|sfexec|V293_stmt_exec|WFIFun|bool)\b')

    def test_union_is_pointwise_and_preserves_good_fun_assertions(self):
        for name in ['fpre', 'fpost']:
            part = self.text.split(f'Definition V293_tcb_union_{name}')[1].split('\n\n')[0]
            self.assertIn('Adisj (getasrt(left', part)
            self.assertIn('(getasrt(right', part)
            self.assertIn('(conj (getprop(left', part)
            self.assertIn('(getprop(right', part)

    def test_both_proved_branch_contracts_are_used(self):
        body = self.text.split('Theorem V293_OS_TCBInit_internal_contract :')[1].split('Proof.')[1]
        self.assertIn('V293_OS_TCBInit_empty_internal_contract', body)
        self.assertIn('V293_OS_TCBInit_success_internal_contract', body)
        self.assertIn('apply disj_rule.', self.text)

    def test_builder_return_resources_and_domain_not_dropped(self):
        part = self.text.split('Lemma V293_tcb_union_builder_rule :')[1].split('Qed.')[0]
        self.assertIn('buildp(revlcons d1 d2)vl', part)
        self.assertIn('buildq(revlcons d1 d2)', part)
        self.assertIn('Some(fun result=>returned **', part)
        self.assertIn('A_dom_lenv(getlenvdom(revlcons d1 d2))', part)
        self.assertIn('V293_tcb_union_resources_left', part)
        self.assertIn('V293_tcb_union_resources_right', part)

    def test_cpu_port_and_global_obligations_are_not_removed(self):
        statement = self.text.split('Theorem V293_OS_TCBInit_internal_contract :')[1].split('Proof.')[0]
        self.assertEqual(statement.count('Spec hi=Some('), 1)
        self.assertEqual(statement.count('Spec hc=Some('), 1)
        self.assertIn('GoodI I sd li', statement)
        self.assertIn('GoodFrm R -> (R ==> CurLINV li tid)', statement)
        self.assertIn('P f=Some(V293_TCBInit_function hi hc)', statement)

    def test_no_holes_no_probe_dependency_and_single_active_entry(self):
        self.assertNotRegex(self.text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort)\b')
        self.assertNotIn('CertiOS.audit.probes.', self.text)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)


if __name__ == '__main__':
    unittest.main()
