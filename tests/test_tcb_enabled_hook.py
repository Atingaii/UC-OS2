"""IE=true 的真实首个 Hook 调用：结构回归，不替代 Coq 语义检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TCBEnabledHook.v'
PROBE = 'audit/probes/V293TCBEnabledHookProbe.v'
D = ROOT / 'audit/logs/stage117-tcb-enabled-hook'


class TCBEnabledHookTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / SOURCE).read_text()
        self.probe = (ROOT / PROBE).read_text()

    def test_no_holes_or_production_audit_dependency(self):
        for text in [self.source, self.probe]:
            self.assertNotRegex(text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.', self.source)
        self.assertEqual(self.probe.count('Require Import CertiOS.audit.'), 2)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

    def test_callee_has_private_node_not_caller_or_shared_head(self):
        resource = self.source.split('Definition V293_tcb_enabled_hook_resource ')[1].split('Definition ')[0]
        self.assertIn('OS[ir,true,si,ci]', resource)
        self.assertIn('V293_tcb_allocated_initialized b off next', resource)
        self.assertNotRegex(resource, r'\b(?:bf|bp|bc|bprio|bindings|V293_tcb_free_pool)\b')
        self.assertIn('GoodFunAsrt R -> GoodFunAsrt', self.source)
        self.assertIn('GoodFrm(V293_tcb_enabled_hook_frame', self.source)

    def test_one_generic_spec_not_one_spec_per_allocated_node(self):
        for name, kind in [('fpre', 'fpre'), ('fpost', 'fpost')]:
            definition = self.source.split('Definition V293_tcb_enabled_hook_' + name + ' ')[1].split('\n\n')[0]
            self.assertIn(': ' + kind + ' :=', definition)
            self.assertIn('[logic_val(Vptr(b,off));logic_val next]', definition)
            self.assertIn('@mkfunasrt Afalse I', definition)
        definition = self.probe.split('Definition EHSpec cs : funspec :=')[1].split('Definition ')[0]
        self.assertIn('990%Z', definition)
        self.assertNotIn(' b ', definition)
        self.assertNotIn(' off ', definition)

    def test_real_call_rule_and_actual_pointer_load(self):
        call = self.source.split('Lemma V293_tcb_enabled_hook_call :')[1].split('Qed.')[0]
        statement = call.split('Proof.')[0]
        self.assertEqual(statement.count('InfRules '), 1)
        self.assertIn('(scall f [evar 108%Z])', statement)
        self.assertIn('eapply call_rule', call)
        self.assertIn('apply V293_tcb_enabled_hook_argument', call)
        self.assertIn('eapply mapstoval_load', self.source)
        self.assertIn('rewrite Env.', self.source)
        self.assertNotIn('hoare_skip', call)

    def test_closed_eighteen_fields_then_original_call(self):
        statement = self.source.split('Lemma V293_tcb_allocated_fields_first_hook :')[1].split('Proof.')[0]
        self.assertEqual(statement.count('InfRules '), 1)
        self.assertIn('V293_tcb_free_node b off next', statement)
        self.assertIn('V293_TCBInit_fields 108%Z 101%Z', statement)
        self.assertIn('(scall f[evar 108%Z])', statement)
        self.assertIn('V293_tcb_allocated_initialized b off next', statement)

    def test_original_body_continuation_starts_after_first_hook(self):
        statement = self.source.split('Theorem V293_OS_TCBInit_free_body_after_first_hook :')[1].split('Proof.')[0]
        self.assertEqual(statement.count('InfRules '), 2)
        self.assertIn('Spec hi=Some', statement)
        self.assertIn('(sseq(sprim encrit)', statement)
        self.assertIn('(sseq(sassign(earrayelem(evar 92%Z)', statement)
        self.assertIn('(sseq(sprim excrit)(sseq(scall hc[evar 108%Z])', statement)
        self.assertIn('V293_TCBInit_function_body hi hc', statement)
        self.assertNotIn('(scall hi', statement)
        self.assertIn('r(Some(Vint32(Int.repr 66)))', statement)

    def test_literal_input_same_inv_and_actual_memory(self):
        self.assertNotRegex(self.probe, r'Definition \w+ : Inv :=')
        for name in ['EHLiteralHookInput', 'EHActualArgument', 'EHSeparatedCallInput',
                     'EHPrivateNoShared', 'EHJoinTail', 'EHLiteralSameInvariantTail']:
            self.assertRegex(self.probe, r'(?:Lemma|Theorem) ' + name + r' :')
        self.assertIn('V293_witness_li FPInv', self.probe)
        self.assertIn('apply FPSameInvariantChangedTail', self.probe)
        self.assertIn('EHInput FPSharedOne', self.probe)

    def test_positive_contract_rejection_theorems(self):
        for name in ['EHAdmitsExact', 'EHAdmitsNone', 'EHWrongPointerRejected',
                     'EHWrongOwnerRejected', 'EHWrongResultRejected', 'EHMalformedLogicRejected']:
            self.assertRegex(self.probe, r'Theorem ' + name + r' :')
        self.assertIn('vl=[FPHead] /\\ owner=FPTid /\\ result=None', self.probe)
        self.assertIn('FPState EHInput true nil |=', self.probe)

    def test_stable_compiles_and_prospective_protocol(self):
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
        self.assertIn('C/AST/config/framework/old frozen evidence/gates94/1/1/1/1/0', protocol['unchanged'])
        self.assertIn('CPU Hook body/WFIFun not supplied', protocol['limitations'])


if __name__ == '__main__':
    unittest.main()
