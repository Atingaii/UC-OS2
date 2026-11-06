"""入口快照规格的结构回归；语义由 Coq 定理与内核校验保证。"""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TCBSnapshotInternal.v'


class TCBSnapshotInternalTests(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / SOURCE).read_text()

    def test_one_value_snapshot_not_boolean_selector(self):
        part = self.text.split('Definition V293_tcb_snapshot_fpre')[1].split('Lemma V293_tcb_guard_builder_rule')[0]
        self.assertIn('| [item] => match item with', part)
        self.assertIn('logic_val Vnull', part)
        self.assertIn('logic_val (Vptr pointer)', part)
        self.assertIn('(Vptr pointer=allocated)', part)
        self.assertNotIn('bool', part)
        self.assertIn('@mkfunasrt Afalse I', part)

    def test_contract_uses_real_builders_and_both_precise_branches(self):
        part = self.text.split('Theorem V293_OS_TCBInit_snapshot_internal_contract :')[1].split('Qed.')[0]
        self.assertIn('Some pre=BuildPreI P f vl lg', part)
        self.assertIn('Some post=BuildRetI P f vl lg', part)
        statement = part.split('Proof.')[0]
        self.assertEqual(statement.count('InfRules '), 1)
        self.assertNotRegex(statement, r'\b(?:evalval|evaladdr|sfexec|V293_stmt_exec|WFIFun|bool)\b')
        for branch in ['empty', 'success']:
            self.assertIn(f'exact(V293_OS_TCBInit_{branch}_internal_contract', part)

    def test_guard_is_proved_and_return_resources_are_preserved(self):
        part = self.text.split('Lemma V293_tcb_guard_builder_rule')[1].split('Qed.')[0]
        self.assertIn('apply pure_split_rule. intro Saved.', part)
        self.assertIn('buildp(revlcons d1 d2)vl', part)
        self.assertIn('buildq(revlcons d1 d2)', part)
        self.assertIn('A_dom_lenv(getlenvdom(revlcons d1 d2))', part)
        self.assertIn('apply astar_l_apure_intro;[exact H|exact Saved]', part)

    def test_snapshot_is_connected_to_physical_load_and_result(self):
        for root in ['V293_tcb_snapshot_pre_load', 'V293_tcb_empty_pre_head',
                     'V293_tcb_success_pre_head', 'V293_tcb_snapshot_post_code',
                     'V293_tcb_empty_post_code', 'V293_tcb_success_post_code']:
            self.assertIn(f'Lemma {root} :', self.text)
        part = self.text.split('Lemma V293_tcb_snapshot_pre_load')[1].split('Proof.')[0]
        self.assertIn('load(Tptr V293_tcb_type)(getmem s)(bg,0%Z)=Some saved', part)
        self.assertIn('lg=[logic_val saved]', part)

    def test_external_hook_and_global_obligations_remain_explicit(self):
        part = self.text.split('Theorem V293_OS_TCBInit_snapshot_internal_contract :')[1].split('Proof.')[0]
        for text in ['GoodI I sd li', 'GoodFrm R -> (R ==> CurLINV li tid)',
                     '(Hfun:GoodFunAsrt R)', 'Spec hi=Some(', 'Spec hc=Some(']:
            self.assertIn(text, part)

    def test_no_holes_probe_imports_or_duplicate_active_entry(self):
        self.assertNotRegex(self.text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort)\b')
        self.assertNotIn('CertiOS.audit.probes.', self.text)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)


if __name__ == '__main__':
    unittest.main()
