"""第二Hook纵向组合的结构回归；Coq编译／coqchk才是语义检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TCBSecondHook.v'
PROBE = 'audit/probes/V293TCBSecondHookProbe.v'
D = ROOT / 'audit/logs/stage120-tcb-second-hook'


class TCBSecondHookTests(unittest.TestCase):
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

    def test_actual_second_call_not_opaque_hoare_premise(self):
        body = self.section('V293_tcb_second_hook')
        signature = body.split('Proof.')[0]
        self.assertEqual(signature.count('InfRules '), 1)
        self.assertIn('(scall f[evar 108%Z])', signature)
        self.assertIn('GoodFunAsrt R', signature)
        self.assertNotIn('V293_create_owned_share', signature)
        for token in ['V293_tcb_full_priority_view', 'V293_tcb_full_priority_restore',
                      'V293_tcb_priority_caller_frame_good', 'V293_tcb_priority_first_hook']:
            self.assertIn(token, body)

    def test_original_whole_body_only_publication_continuation(self):
        body = self.section('V293_OS_TCBInit_free_body_after_second_hook')
        signature = body.split('Proof.')[0]
        self.assertEqual(signature.count('InfRules '), 2)
        self.assertIn('(V293_TCBInit_function_body hi hc)', signature)
        self.assertIn('(V293_TCB_publish 108%Z 93%Z 94%Z 95%Z 96%Z)Afalse tid', signature)
        self.assertNotIn('(scall ', signature)
        self.assertIn('apply V293_OS_TCBInit_free_body_after_owned_priority', body)
        self.assertIn('eapply seq_rule', body)
        self.assertIn('apply V293_tcb_second_hook', body)

    def test_first_owner_share_is_not_required_by_second_contract(self):
        signature = self.section('V293_OS_TCBInit_free_body_after_second_hook').split('Proof.')[0]
        first, second = signature.split('Spec hi=Some', 1)[1].split('Spec hc=Some', 1)
        self.assertIn('V293_create_owned_share table reserved p ** R', first)
        second = second.split('(V293_tcb_enabled_state', 1)[0]
        self.assertNotIn('V293_create_owned_share', second)
        self.assertIn('R aop ir si ci tid (proj2 good)', second)
        self.assertIn('GoodFunAsrt(V293_create_owned_share table reserved p ** R)', signature)

    def test_freshness_stays_explicit_and_has_physical_counterexample(self):
        signature = self.section('V293_OS_TCBInit_free_body_after_second_hook').split('Proof.')[0]
        fresh = signature.split('(forall b off next s,', 1)[1].split('(b,off)<>reserved)', 1)[0]
        self.assertIn('s |= V293_tcb_enabled_state', fresh)
        self.assertIn('V293_create_owned_share table reserved p ** R', fresh)
        self.assertIn('Theorem TSAliasFreshnessCounterexample : ~ (forall s,', self.probe)
        self.assertIn('TSAliasPhysical nil', self.probe)
        self.assertIn('Definition TSAlias : addrval := (501%positive,Int.zero)', self.probe)
        self.assertIn('Lemma TSOwnerRead : forall token,', self.probe)
        self.assertIn('mapstoval_load', self.probe)
        self.assertNotRegex(self.probe, r'Definition \w+ : Inv :=')

    def test_single_finite_spec_supports_both_calls_for_all_nodes(self):
        for token in ['Definition TSSpec token cs : funspec', 'f 990%Z', 'f 991%Z',
                      'TSFirstPre token cs,TSFirstPost token cs', 'EHPre cs,EHPost cs',
                      'forall sd r ri token b off next cs', 'Theorem TSFirstCallChecked :',
                      'Theorem TSSecondCallChecked :', 'Theorem TSSecondLiteralInput :',
                      'Theorem TSSecondActualArgument :']:
            self.assertIn(token, self.probe)
        self.assertIn('(TSFull b off next FPR cs)', self.probe)

    def test_second_post_boundary_has_positive_and_three_negative_checks(self):
        for name in ['TSAdmitsExact', 'TSAdmitsNone', 'TSWrongPointerRejected',
                     'TSWrongOwnerRejected', 'TSWrongResultRejected']:
            self.assertRegex(self.probe, r'Theorem ' + name + r' :')
        self.assertIn('vl=[FPHead] /\\ owner=FPTid /\\ result=None', self.probe)
        self.assertIn('TFState TFInput true nil |=', self.probe)

    def test_prospective_single_factor_controls(self):
        controls = json.loads((D / 'controls.json').read_text())
        self.assertTrue(controls['passed'])
        self.assertEqual([r['exit'] for r in controls['rows']], [0, 1])
        normal = (D / 'Normal.v.snapshot.txt').read_text()
        alias = (D / 'Aliased.v.snapshot.txt').read_text()
        self.assertEqual(normal.replace('Token : addrval := (405%positive', 'Token : addrval := (501%positive'), alias)
        for row in controls['rows']:
            self.assertTrue(row['common_input_checked'])
            self.assertLessEqual((D / 'controls-plan.json').stat().st_mtime_ns,
                                 (D / (row['label'] + '.v.snapshot.txt')).stat().st_mtime_ns)
        for token in ['Example CommonInput', 'Example CommonOwnerRead', 'Example ExpectedFreshness']:
            self.assertIn(token, normal)
        log = (D / 'Aliased.log').read_text()
        self.assertLess(log.index('COMMON_INPUT_CHECKED'), log.index('Error:'))

    def test_stable_compiles_protocol_and_unchanged_gates(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('proof', SOURCE), ('probe', PROBE)]:
            label = stable[kind]
            row = json.loads((D / (label + '.json')).read_text())
            content = (ROOT / path).read_bytes()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(hashlib.sha256(content).hexdigest(), row['source_sha256'])
            self.assertEqual(content, (D / (label + '.v.snapshot.txt')).read_bytes())
        self.assertLessEqual((D / 'protocol.json').stat().st_mtime_ns,
                             (D / 'proof01.v.snapshot.txt').stat().st_mtime_ns)
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertIn('production allocator freshness and symbolic-token noncollision remain open; no artificial reserved storage introduced',
                      protocol['limitations'])
        rows = json.loads((ROOT / 'audit/coverage.json').read_text())['rows']
        self.assertEqual([sum(bool(row[k]) for row in rows) for k in
                          ['located', 'modeled', 'specified', 'local_hoare', 'component_linked', 'full_target_linked']],
                         [94, 1, 1, 1, 1, 0])


if __name__ == '__main__':
    unittest.main()
