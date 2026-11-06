"""完整函数体接优先级槽；结构回归不是 Coq 语义验证替代品。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TCBFullPriority.v'
PROBE = 'audit/probes/V293TCBFullPriorityProbe.v'
D = ROOT / 'audit/logs/stage119-tcb-full-priority'


class TCBFullPriorityTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / SOURCE).read_text()
        self.probe = (ROOT / PROBE).read_text()

    def section(self, name):
        return self.source.split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_no_holes_or_audit_import_in_production(self):
        for text in [self.source, self.probe]:
            self.assertNotRegex(text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.', self.source)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

    def test_only_environment_facts_are_duplicated(self):
        for name in ['V293_tcb_fields_priority_copy', 'V293_tcb_fields_priority_drop']:
            statement = self.section(name).split('Proof.')[0]
            self.assertIn('Alvarenv 101%Z Tint8', statement)
            self.assertIn('Alvarenv 108%Z(Tptr V293_tcb_type)', statement)
            self.assertIn('V293_tcb_fields_bindings', statement)
            self.assertNotIn('Amapsto', statement)
        self.assertIn('exists empmem. exists M. exists empabst. exists O.', self.source)
        self.assertIn("apply map_join_emp'' in JM,JO", self.source)

    def test_caller_frame_keeps_other_six_parameters_and_cpu(self):
        frame = self.source.split('Definition V293_tcb_priority_caller_frame', 1)[1].split('Lemma ', 1)[0]
        for name in ['bs', 'bb', 'bi', 'bz', 'be', 'bo']:
            self.assertIn('((' + name + ',0%Z)', frame)
        self.assertIn('Amapsto(bc,0%Z)Tint32 true cpu', frame)
        self.assertIn('V293_tcb_empty_bindings bf bp bc', frame)
        self.assertIn('V293_tcb_fields_bindings', frame)
        self.assertNotIn('Amapsto(bp', frame)
        self.assertNotIn('((bprio', frame)

    def test_bidirectional_full_resource_view(self):
        for name in ['V293_tcb_full_priority_view', 'V293_tcb_full_priority_restore']:
            statement = self.section(name).split('Proof.')[0]
            for token in ['V293_tcb_enabled_state', 'V293_tcb_allocated_inputs',
                          'V293_tcb_priority_state', 'V293_tcb_priority_caller_frame',
                          'V293_tcb_table_binding table ** R', 'pc cpu', 'aop ir si ci']:
                self.assertIn(token, statement)
            self.assertNotIn('InfRules ', statement)

    def test_full_original_body_and_single_second_hook_continuation(self):
        whole = self.section('V293_OS_TCBInit_free_body_after_owned_priority')
        statement = whole.split('Proof.')[0]
        self.assertEqual(statement.count('InfRules '), 2)
        self.assertIn('(V293_TCBInit_function_body hi hc)', statement)
        self.assertIn('(sseq(scall hc[evar 108%Z])(V293_TCB_publish', statement)
        self.assertNotIn('(scall hi', statement)
        self.assertIn('apply V293_OS_TCBInit_free_body_after_fields', whole)
        self.assertIn('apply V293_OS_TCBInit_owned_suffix_after_first_hook', whole)
        self.assertIn('apply V293_tcb_full_priority_view', whole)
        self.assertIn('apply V293_tcb_full_priority_restore', whole)
        self.assertNotIn('frame_rule_all', whole)
        self.assertNotIn('hoare_skip', whole)

    def test_freshness_is_actual_state_premise_not_universal_disequality(self):
        statement = self.section('V293_OS_TCBInit_free_body_after_owned_priority').split('Proof.')[0]
        fresh = statement.split('(forall b off next s,', 1)[1].split('(b,off)<>reserved) ->', 1)[0]
        for token in ['s |= V293_tcb_enabled_state', 'V293_tcb_allocated_initialized',
                      'V293_tcb_allocated_inputs', 'V293_create_owned_share table reserved p ** R']:
            self.assertIn(token, fresh)
        self.assertNotIn('==> [|', fresh)
        self.assertIn('Spec hi=Some', statement)
        self.assertIn('GoodFunAsrt(V293_create_owned_share table reserved p ** R)', statement)
        self.assertNotIn('GoodFunAsrt(V293_tcb_table_binding', statement)

    def test_nonempty_literal_full_and_owned_views(self):
        for name in ['TFLiteralFull', 'TFLiteralPriority', 'TFLiteralRestore',
                     'TFActualArgument', 'TFGlobalAddress', 'TFShadowAddress',
                     'TFShadowDiffers', 'TFOwnedLiteral', 'TFOwnedPriorityLiteral', 'TFOwnedRestore']:
            self.assertRegex(self.probe, r'(?:Lemma|Theorem) ' + name + r' :')
        self.assertIn('Lemma TFActualPriorityRead :', self.probe)
        self.assertIn('V293_rekey_array_address TFGE FPLE TFInput', self.probe)
        self.assertIn('set FPGE 92%Z(403%positive,Tarray', self.probe)
        self.assertIn('merge TFInput TFShareMemory', self.probe)
        self.assertNotRegex(self.probe, r'Definition \w+ : Inv :=')

    def test_single_factor_shadow_controls_are_prospective(self):
        controls = json.loads((D / 'controls.json').read_text())
        self.assertTrue(controls['passed'])
        self.assertEqual([r['exit'] for r in controls['rows']], [0, 1])
        normal = (D / 'Normal.v.snapshot.txt').read_text()
        shadowed = (D / 'Shadowed.v.snapshot.txt').read_text()
        self.assertEqual(normal.replace('Shadow : bool := false', 'Shadow : bool := true'), shadowed)
        for row in controls['rows']:
            self.assertTrue(row['common_input_checked'])
            snapshot = D / (row['label'] + '.v.snapshot.txt')
            self.assertLessEqual((D / 'controls-plan.json').stat().st_mtime_ns, snapshot.stat().st_mtime_ns)
        log = (D / 'Shadowed.log').read_text()
        self.assertLess(log.index('COMMON_INPUT_CHECKED'), log.index('Error:'))

    def test_stable_compiles_preceded_by_protocol(self):
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
        self.assertIn('production allocator freshness still open', protocol['limitations'])
        gates = json.loads((ROOT / 'audit/coverage.json').read_text())['rows']
        self.assertEqual([sum(bool(row[k]) for row in gates) for k in
                          ['located', 'modeled', 'specified', 'local_hoare', 'component_linked', 'full_target_linked']],
                         [94, 1, 1, 1, 1, 0])


if __name__ == '__main__':
    unittest.main()
