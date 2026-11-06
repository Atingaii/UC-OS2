"""开启中断发布的结构回归；语义证据仍须独立 Coq 编译与 coqchk。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TCBEnabledPublication.v'
PROBE = 'audit/probes/V293TCBEnabledPublicationProbe.v'
D = ROOT / 'audit/logs/stage122-tcb-enabled-publication'


class TCBEnabledPublicationTests(unittest.TestCase):
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

    def test_full_body_has_no_hoare_continuation(self):
        body = self.section('V293_OS_TCBInit_free_body_published')
        signature = body.split('Proof.')[0]
        self.assertEqual(signature.count('InfRules '), 1)
        self.assertIn('(V293_TCBInit_function_body hi hc)Afalse tid', signature)
        for token in ['V293_OS_TCBInit_free_body_after_second_hook',
                      'V293_tcb_full_publication_view', 'V293_OS_TCBInit_publish_enabled',
                      'V293_tcb_full_publication_restore']:
            self.assertIn(token, body)

    def test_actual_enabled_critical_suffix_and_return_zero(self):
        body = self.section('V293_OS_TCBInit_publish_enabled')
        self.assertEqual(body.split('Proof.')[0].count('InfRules '), 1)
        for text in ['unfold V293_TCB_publish', 'V293_tcb_publication_enter',
                     'V293_OS_TCBInit_publish_pool_body', 'V293_tcb_publication_exit',
                     'apply rete_rule with(v:=Vint32 Int.zero)']:
            self.assertIn(text, body)
        self.assertIn('apply encrit1_rule', self.source)
        self.assertIn('apply excrit1_rule', self.source)
        self.assertNotIn('encrit2_rule', self.source)
        self.assertNotIn('excrit2_rule', self.source)

    def test_caller_and_return_do_not_own_shared_bytes(self):
        private = self.source.split('Definition V293_tcb_publication_private', 1)[1].split('Lemma V293_tcb_publication_private_good', 1)[0]
        self.assertNotIn('V293_tcb_publication_pool', private)
        self.assertNotIn('V293_tcb_publication_shared', private)
        returned = private.split('Definition V293_tcb_publication_returned', 1)[1]
        self.assertNotIn('V293_tcb_publication_new', returned)
        globals_only = self.source.split('Definition V293_tcb_publication_globals', 1)[1].split('Definition V293_tcb_publication_caller_frame', 1)[0]
        self.assertNotIn('Amapsto', globals_only)

    def test_shared_values_are_latent_and_capacity_is_separate(self):
        shared = self.source.split('Definition V293_tcb_publication_shared', 1)[1].split('Definition V293_tcb_publication_private', 1)[0]
        for text in ['EX present:bool', 'EX k:nat', 'EX bo:block', 'EX g:nat',
                     '(if present then S k else O)<256']:
            self.assertIn(text, shared)
        for theorem in ['V293_OS_TCBInit_publish_enabled', 'V293_OS_TCBInit_free_body_published']:
            signature = self.section(theorem).split('Proof.')[0]
            self.assertIn('(if present then S k else O)<255', signature)
            self.assertIn('V293_tcb_publication_input', signature)
        self.assertIn('Theorem PEEnabledSuffixConditional :', self.probe)
        self.assertIn('Count0/2 is fixed only for this already-disabled suffix', self.probe)

    def test_original_seven_parameters_and_two_locals_are_restored(self):
        for name in ['V293_tcb_full_publication_view', 'V293_tcb_full_publication_restore']:
            body = self.section(name)
            self.assertIn('p top bottom identity size ext options', body)
            self.assertIn('V293_tcb_empty_bindings', body)
            self.assertIn('V293_tcb_allocated_inputs', body)
        self.assertIn('V293_tcb_publication_initialized_view', self.section('V293_tcb_full_publication_view'))
        self.assertNotIn('V293_tcb_allocated_initialized', self.section('V293_tcb_full_publication_restore').split('Proof.')[0])

    def test_real_invariant_precision_and_irq_stability(self):
        for name in ['PEChainPrecise', 'PEPoolPrecise', 'PESharedPrecise',
                     'PESharedGood', 'PESharedISR', 'PEBorrowEquivalence']:
            self.assertRegex(self.probe, r'(?:Lemma|Theorem) ' + name + r' :')
        self.assertIn('Definition PEInv y : Inv :=', self.probe)
        self.assertIn('PESharedPrecise 701%positive', self.probe)
        self.assertIn('PESharedISR 701%positive', self.probe)

    def test_literal_input_and_actual_fragments_are_independent(self):
        for name in ['PELiteralInput', 'PECommonLocalInput', 'PEEnterChecked',
                     'PEExitChecked', 'PEBodyExitReturnChecked']:
            self.assertIn('Theorem ' + name + ' :', self.probe)
        self.assertIn('forall (present upper:bool) cs,', self.probe)
        self.assertIn('PEPre(if upper then 1 else 0)cs ** invlth_isr(PEInv(if upper then 1 else 0))0 INUM', self.probe)
        self.assertIn('apply PPBodyChecked', self.probe)

    def test_ownership_counterproof_and_single_factor_control(self):
        self.assertIn('Theorem PEMissingBorrowImpossible :', self.probe)
        self.assertIn('PESharedHeadLoad', self.probe)
        controls = json.loads((D / 'controls.json').read_text())
        self.assertTrue(controls['passed'])
        self.assertEqual([r['exit'] for r in controls['rows']], [0, 1])
        normal = (D / 'Normal.v.snapshot.txt').read_text()
        self.assertEqual(normal.replace('provide_shared : bool := true', 'provide_shared : bool := false'),
                         (D / 'Omitted.v.snapshot.txt').read_text())
        for row in controls['rows']:
            self.assertTrue(row['common_input_checked'])
        log = (D / 'Omitted.log').read_text()
        self.assertLess(log.index('COMMON_INPUT_CHECKED'), log.index('Error:'))

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

    def test_prospective_protocol_not_rewritten_for_capacity(self):
        self.assertLessEqual((D / 'protocol.json').stat().st_mtime_ns,
                             (D / 'proof01.v.snapshot.txt').stat().st_mtime_ns)
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertIn('capacity/freshness/Hook bodies/production open-close/WFIFun/init remain explicit obligations', protocol['limitations'])

    def test_unchanged_gates_and_scope(self):
        rows = json.loads((ROOT / 'audit/coverage.json').read_text())['rows']
        self.assertEqual([sum(bool(row[k]) for row in rows) for k in
                          ['located', 'modeled', 'specified', 'local_hoare', 'component_linked', 'full_target_linked']],
                         [94, 1, 1, 1, 1, 0])
        doc = (ROOT / 'audit/STAGE122_TCB_ENABLED_PUBLICATION.md').read_text()
        for text in ['不是生产 Inv', 'Capacity', '255', 'uCOS3', 'GOOD_OS']:
            self.assertIn(text, doc)


if __name__ == '__main__':
    unittest.main()
