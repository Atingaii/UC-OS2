"""有限地址发布链的结构回归；不替代独立 Coq/coqchk 语义检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TCBFiniteSites.v'
PROBE = 'audit/probes/V293TCBFiniteSitesProbe.v'
D = ROOT / 'audit/logs/stage123-tcb-finite-sites'


class TCBFiniteSitesTests(unittest.TestCase):
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

    def test_real_table_stride_and_count(self):
        self.assertIn('56*Z.of_nat i', self.source)
        self.assertIn('(seq 0 13)', self.source)
        self.assertIn('length(V293_tcb_table_sites bt)=13', self.source)

    def test_same_heap_refinement_forgets_to_original_chain(self):
        for name in ['V293_tcb_indexed_forget', 'V293_tcb_indexed_pool_forget',
                     'V293_tcb_finite_pool_forget']:
            self.assertIn('V293_tcb_active_chain' if name.endswith('indexed_forget')
                          else 'V293_tcb_publication_pool', self.section(name))
        self.assertIn('V293_tcb_active_payload b(Int.unsigned off)', self.source)

    def test_capacity_uses_both_cardinality_conditions(self):
        self.assertIn('NoDup nodes /\\ incl nodes sites', self.source)
        self.assertIn('NoDup_incl_length', self.section('V293_tcb_sites_count'))
        self.assertIn('V293_tcb_table_sites_length', self.section('V293_tcb_table_capacity'))
        self.assertIn('V293_tcb_sites_count', self.section('V293_tcb_table_capacity'))

    def test_physical_freshness_uses_actual_write_conflict(self):
        self.assertIn('V293_tcb_pointer_conflict', self.section('V293_tcb_indexed_private_fresh'))
        self.assertIn('V293_tcb_indexed_member_cell', self.section('V293_tcb_indexed_private_fresh'))
        self.assertIn('V293_tcb_indexed_private_fresh', self.section('V293_tcb_indexed_input_fresh'))

    def test_original_body_has_no_hoare_continuation_or_capacity_premise(self):
        body = self.section('V293_OS_TCBInit_publish_finite_body')
        signature = body.split('Proof.')[0]
        self.assertEqual(signature.count('InfRules '), 1)
        self.assertIn('(V293_TCB_publish_body ptcb head group rows counter)', signature)
        self.assertNotIn('<255', signature)
        self.assertNotIn('~In', signature)
        self.assertIn('V293_OS_TCBInit_publish_body_hoare', body)
        self.assertIn('V293_tcb_indexed_finish', body)

    def test_postcondition_preserves_finite_membership(self):
        body = self.section('V293_OS_TCBInit_publish_finite_body')
        self.assertIn('V293_tcb_sites_prepend', body)
        self.assertIn('((bt,Int.repr base)::V293_tcb_old_sites', body)
        self.assertIn('V293_tcb_indexed_output', body)

    def test_literal_input_and_body_are_independently_checked(self):
        for name in ['FCLiteralInput', 'FCBodyChecked']:
            self.assertIn('Theorem ' + name + ' :', self.probe)
        self.assertIn('forall (present upper:bool) cs,', self.probe)
        self.assertIn('FCNodeRows 56 Vnull FCTail ++ FCNodeRows 112 FCOld Vnull', self.probe)
        self.assertIn('V293_OS_TCBInit_publish_finite_body', self.probe)

    def test_pure_ablation_not_claimed_as_physical_execution(self):
        self.assertIn('Theorem FCWithoutInclusionCounterexample :', self.probe)
        self.assertIn('NoDup nodes', self.probe)
        self.assertIn('seq 0 255', self.probe)
        self.assertIn('not a physical heap execution', self.probe)

    def test_stable_compile_identity(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('proof', SOURCE), ('probe', PROBE)]:
            label = stable[kind]
            record = json.loads((D / (label + '.json')).read_text())
            data = (ROOT / path).read_bytes()
            self.assertEqual(record['exit'], 0)
            self.assertEqual(record['initial_source_sha256'], record['source_sha256'])
            self.assertEqual(hashlib.sha256(data).hexdigest(), record['source_sha256'])
            self.assertEqual(data, (D / (label + '.v.snapshot.txt')).read_bytes())

    def test_prospective_protocol(self):
        self.assertLessEqual((D / 'protocol.json').stat().st_mtime_ns,
                             (D / 'proof01.v.snapshot.txt').stat().st_mtime_ns)
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertTrue(any('pure cardinality counterexample' in s for s in protocol['prospective_checks']))

    def test_scope_and_unchanged_gates(self):
        rows = json.loads((ROOT / 'audit/coverage.json').read_text())['rows']
        self.assertEqual([sum(bool(row[k]) for row in rows) for k in
                          ['located', 'modeled', 'specified', 'local_hoare', 'component_linked', 'full_target_linked']],
                         [94, 1, 1, 1, 1, 0])
        doc = (ROOT / 'audit/STAGE123_TCB_FINITE_SITES.md').read_text()
        for text in ['不是生产 Inv', 'Capacity', '255', 'uCOS3', 'GOOD_OS']:
            self.assertIn(text, doc)


if __name__ == '__main__':
    unittest.main()
