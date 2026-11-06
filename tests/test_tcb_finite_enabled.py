"""有限共享链开启中断发布接口的结构回归；不替代 Coq 语义检查。"""
from pathlib import Path
import hashlib
import json
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TCBFiniteEnabled.v'
PROBE = 'audit/probes/V293TCBFiniteEnabledProbe.v'
D = ROOT / 'audit/logs/stage124-tcb-finite-enabled'


class TCBFiniteEnabledTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / SOURCE).read_text()
        self.probe = (ROOT / PROBE).read_text()

    def section(self, name):
        return self.source.split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_no_holes_or_production_audit_import(self):
        for content in [self.source, self.probe]:
            self.assertNotRegex(content, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.', self.source)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

    def test_shared_keeps_indexed_bytes_and_pure_membership(self):
        shared = self.source.split('Definition V293_tcb_finite_shared', 1)[1].split('Lemma ', 1)[0]
        self.assertIn('V293_tcb_sites_valid(V293_tcb_table_sites tcbtable)', shared)
        self.assertIn('V293_tcb_indexed_pool', shared)
        self.assertNotIn('V293_tcb_publication_shared', shared)
        forget = self.section('V293_tcb_finite_shared_forget')
        self.assertIn('V293_tcb_table_capacity', forget)
        self.assertIn('V293_tcb_indexed_pool_forget', forget)

    def test_enter_borrows_current_indexed_witness(self):
        enter = self.section('V293_tcb_finite_enter')
        self.assertIn('EX present:bool,EX tail:list (block*int32)', enter)
        self.assertIn('V293_tcb_indexed_input', enter)
        self.assertIn('invlth_isr I 0(gettopis si)', enter)
        self.assertIn('apply encrit1_rule', enter)
        self.assertNotIn('finite_shared_forget', enter)

    def test_exit_rebuilds_same_shared_pool_before_return(self):
        leave = self.section('V293_tcb_finite_exit')
        self.assertIn('((bt,Int.repr base)::nodes)', leave)
        self.assertIn('V293_tcb_indexed_output', leave)
        self.assertIn('exists true. exists nodes. exists bt. exists base.', leave)
        self.assertIn('V293_tcb_finite_shared tcbtable bh bg br bn y ** K', leave)
        self.assertIn('apply excrit1_rule', leave)

    def test_enabled_original_suffix_has_one_hoare_conclusion(self):
        whole = self.section('V293_OS_TCBInit_publish_finite_enabled')
        signature = whole.split('Proof.')[0]
        self.assertEqual(signature.count('InfRules '), 1)
        self.assertNotIn('Capacity', signature)
        self.assertNotIn('<255', signature)
        self.assertIn('In(bt,Int.repr base)(V293_tcb_table_sites tcbtable)', signature)
        self.assertIn('(V293_TCB_publish ptcb head group rows counter)', signature)
        for step in ['V293_tcb_finite_enter', 'V293_OS_TCBInit_publish_finite_body',
                     'V293_tcb_finite_exit', 'apply rete_rule']:
            self.assertIn(step, whole)

    def test_full_body_retains_real_production_obligations(self):
        whole = self.section('V293_OS_TCBInit_free_body_finite_published')
        signature = whole.split('Proof.')[0]
        self.assertEqual(signature.count('InfRules '), 1)
        self.assertIn('(V293_TCBInit_function_body hi hc)', signature)
        self.assertNotIn('Capacity', signature)
        for text in ['Spec hi=Some', 'Spec hc=Some', '(b,off)<>reserved',
                     'In(b,off)(V293_tcb_table_sites tcbtable)',
                     'V293_tcb_free_pool bf', 'V293_create_owned_pool table reserved p Kprio',
                     'V293_tcb_finite_shared tcbtable']:
            self.assertIn(text, signature)
        self.assertIn('Member b off next s H', whole)
        self.assertIn('V293_OS_TCBInit_publish_finite_enabled', whole)

    def test_literal_enabled_input_and_whole_suffix_independent(self):
        literal = self.probe.split('Theorem FELiteralInput :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('forall (present upper:bool) cs', literal)
        self.assertIn('PEState(FCInput present(if upper then 1 else 0))true cs', literal)
        self.assertIn('invlth_isr(FEInv(if upper then 1 else 0))0 INUM', literal)
        self.assertIn('FEInputRaw present upper true cs', literal)
        whole = self.probe.split('Theorem FEEnabledSuffixChecked :', 1)[1].split('Qed.', 1)[0]
        signature = whole.split('Proof.')[0]
        self.assertEqual(signature.count('InfRules '), 1)
        self.assertNotIn('Capacity', signature)
        for text in ['apply FCNewMember', 'apply FEBorrowOpen', 'apply FEBorrowClose']:
            self.assertIn(text, whole)
        self.assertIn('exact(FCLiteralRaw present upper cs)', self.probe)
        self.assertIn('exists[(501%positive,Int.repr 112)]', self.probe)

    def test_frozen_compiles_prospective_protocol_and_scope(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('proof', SOURCE), ('probe', PROBE)]:
            label = stable[kind]
            record = json.loads((D / (label + '.json')).read_text())
            data = (ROOT / path).read_bytes()
            self.assertEqual(record['exit'], 0)
            self.assertEqual(record['initial_source_sha256'], record['source_sha256'])
            self.assertEqual(hashlib.sha256(data).hexdigest(), record['source_sha256'])
            self.assertEqual(data, (D / (label + '.v.snapshot.txt')).read_bytes())
        self.assertLessEqual((D / 'protocol.json').stat().st_mtime_ns,
                             (D / 'proof01.v.snapshot.txt').stat().st_mtime_ns)
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertTrue(any('same invariant' in s for s in [protocol['subject']]))
        doc = (ROOT / 'audit/STAGE124_TCB_FINITE_ENABLED.md').read_text()
        for text in ['不是生产全局Inv', 'token freshness', '255', 'uCOS3', 'GOOD_OS']:
            self.assertIn(text, doc)
        rows = json.loads((ROOT / 'audit/coverage.json').read_text())['rows']
        self.assertEqual([sum(bool(row[k]) for row in rows) for k in
                          ['located', 'modeled', 'specified', 'local_hoare', 'component_linked', 'full_target_linked']],
                         [94, 1, 1, 1, 1, 0])


if __name__ == '__main__':
    unittest.main()
