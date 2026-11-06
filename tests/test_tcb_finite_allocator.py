"""真实空闲链表成员性接口的结构回归；不替代 Coq 语义检查。"""
from pathlib import Path
import hashlib
import json
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TCBFiniteAllocator.v'
PROBE = 'audit/probes/V293TCBFiniteAllocatorProbe.v'
D = ROOT / 'audit/logs/stage125-tcb-finite-allocator'


class TCBFiniteAllocatorTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / SOURCE).read_text()
        self.probe = (ROOT / PROBE).read_text()

    def section(self, name):
        return self.source.split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_no_holes_or_audit_import(self):
        for content in [self.source, self.probe]:
            self.assertNotRegex(content, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.', self.source)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

    def test_refinement_keeps_actual_bytes(self):
        chain = self.source.split('Fixpoint V293_tcb_site_free_chain', 1)[1].split('Definition ', 1)[0]
        for text in ['In(b,offset)sites', 'V293_tcb_free_payload', 'Amapsto(b,(Int.unsigned offset+20)',
                     'V293_tcb_site_free_chain sites n next']:
            self.assertIn(text, chain)
        forget = self.section('V293_tcb_site_free_pool_forget')
        self.assertIn('V293_tcb_free_pool bf', forget)
        self.assertIn('V293_tcb_site_free_forget', forget)
        self.assertIn('apply V293_tcb_site_free_weaken', self.section('V293_tcb_site_free_exit'))

    def test_pop_derives_member_and_returns_same_refined_pool(self):
        whole = self.section('V293_OS_TCBInit_site_free_pop_transfer')
        signature = whole.split('Proof.')[0]
        self.assertEqual(signature.count('InfRules '), 1)
        self.assertIn('In(b,off)(V293_tcb_table_sites tcbtable)', signature)
        self.assertIn('V293_tcb_site_free_pool tcbtable bf ** K', signature)
        self.assertIn('(sseq(V293_TCBInit_pop 91%Z 108%Z)(sprim excrit))', signature)
        self.assertIn('intros[[Bound Member]Typed]', whole)
        self.assertIn('apply V293_tcb_site_free_pop', whole)
        self.assertIn('apply V293_tcb_site_free_exit', whole)

    def test_complete_original_body_without_member_or_hoare_premise(self):
        whole = self.section('V293_OS_TCBInit_site_allocated_finite_published')
        signature = whole.split('Proof.')[0]
        self.assertEqual(signature.count('InfRules '), 1)
        self.assertIn('(V293_TCBInit_function_body hi hc)', signature)
        self.assertNotIn('In(b,off)', signature)
        self.assertNotIn('Capacity', signature)
        for text in ['Spec hi=Some', 'Spec hc=Some', '(b,off)<>reserved',
                     'V293_tcb_site_free_pool tcbtable bf', 'V293_create_owned_pool table reserved p Kprio',
                     'V293_tcb_finite_shared tcbtable']:
            self.assertIn(text, signature)
        self.assertIn('NodeMember NodeBound NextTyped', whole)
        self.assertIn('exact NodeMember', whole)

    def test_literal_same_block_input_not_pure_list(self):
        for text in ['FANodeMemory 501%positive 0 FANext', 'FANodeMemory 501%positive 56 Vnull',
                     'V293_encoded_memory b (base+20)', 'FAPayloadTactic', 'Theorem FAActualPopInput :']:
            self.assertIn(text, self.probe)
        literal = self.probe.split('Theorem FAActualPopInput :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('FPState(merge(FPCaller FAHead(Vint32 Int.zero))FASharedTwo)', literal)
        self.assertIn('apply FATwoRaw', literal)
        self.assertIn('V293_tcb_site_free_critical 501%positive', literal)

    def test_same_invariant_and_whole_pop(self):
        for text in ['FASameInvariantTwoOne', 'FPState FASharedOne ie cs |= invlth_isr FAInv',
                     'FPState FASharedTwo ie cs |= invlth_isr FAInv', 'apply FABorrowEquivalence']:
            self.assertIn(text, self.probe)
        whole = self.probe.split('Theorem FAPopTransferChecked :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(whole.count('InfRules'), 1)
        self.assertIn('(sseq(V293_TCBInit_pop 91%Z 108%Z)(sprim excrit))', whole)

    def test_single_factor_physical_counterexample(self):
        ablation = self.probe.split('Theorem FAWithoutMembershipPhysicalCounterexample :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('FPState FPSharedOne ie cs |= V293_tcb_free_pool', ablation)
        self.assertIn('~(FPState FPSharedOne ie cs |= V293_tcb_site_free_pool 501%positive', ablation)
        self.assertIn('apply FPOnePool', ablation)
        self.assertIn('FAOutsideHeadRead', ablation)
        self.assertNotIn('exists(seq', ablation)

    def test_frozen_compiles_and_honest_scope(self):
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
        doc = (ROOT / 'audit/STAGE125_TCB_FINITE_ALLOCATOR.md').read_text()
        for text in ['不是生产全局Inv', 'token freshness', '初始化', 'uCOS3', 'GOOD_OS', 'WFIFun']:
            self.assertIn(text, doc)
        rows = json.loads((ROOT / 'audit/coverage.json').read_text())['rows']
        self.assertEqual([sum(bool(row[k]) for row in rows) for k in
                          ['located', 'modeled', 'specified', 'local_hoare', 'component_linked', 'full_target_linked']],
                         [94, 1, 1, 1, 1, 0])


if __name__ == '__main__':
    unittest.main()
