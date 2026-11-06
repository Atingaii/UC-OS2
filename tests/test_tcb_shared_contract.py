"""标准TCB契约的结构回归；类型、资源与调用语义由Coq独立检查。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage130-tcb-shared-contract'
SOURCE = 'certiucos/v293/proofs/V293TCBSharedContract.v'
PROBE = 'audit/probes/V293TCBSharedContractProbe.v'


class TCBSharedContractTests(unittest.TestCase):
    def setUp(self):
        self.source = (R / SOURCE).read_text()
        self.probe = (R / PROBE).read_text()

    def section(self, name, probe=False):
        return (self.probe if probe else self.source).split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_hole_free_and_registered_once(self):
        for text in [self.source, self.probe]:
            self.assertNotRegex(text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.', self.source)
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

    def test_function_resources_have_no_caller_local_facts(self):
        external = self.source.split('Definition V293_tcb_shared_external', 1)[1].split('Lemma ', 1)[0]
        self.assertNotIn('A_dom_lenv', external)
        self.assertNotIn('A_notin_lenv', external)
        self.assertIn('V293_tcb_success_global_bindings', external)
        self.assertIn('V293_tcb_shared_bindings_open', self.section('V293_tcb_shared_internal_entry'))
        self.assertIn('V293_tcb_success_bindings_from_domain', self.section('V293_tcb_shared_internal_entry'))

    def test_original_body_uses_one_joint_inv_and_explicit_hypotheses(self):
        sig, proof = self.section('V293_OS_TCBInit_shared_internal_resources').split('Proof.', 1)
        for text in ['GoodI(V293_create_joint_inv', 'V293_TCBInit_function_body hi hc',
                     'Spec hi=Some', 'Spec hc=Some', '(b,off)<>reserved', 'V293_tcb_internal_domain']:
            self.assertIn(text, sig)
        self.assertNotIn('==> [|(b,off)<>reserved|]', sig)
        self.assertIn('V293_OS_TCBInit_creator_joint_hook_framed', proof)
        self.assertIn('frame_rule_all', proof)
        self.assertNotIn('V293_OS_TCBInit_success_internal_contract', proof)

    def test_exact_standard_builders_are_connected(self):
        body = self.section('V293_OS_TCBInit_shared_internal_contract')
        for text in ['P f=Some(V293_TCBInit_function hi hc)', 'BuildPreI', 'BuildRetI',
                     'V293_tcb_internal_buildp', 'V293_OS_TCBInit_shared_internal_resources']:
            self.assertIn(text, body)
        for name in ['SCBuilders', 'SCTyped', 'SCWrongTopUntyped', 'SCWrongTopBuilderRejected']:
            self.assertIn('reflexivity', self.section(name, True))

    def test_actual_receiver_call_preserves_arguments(self):
        body = self.section('V293_TaskCreateExt_TCB_shared_call')
        for text in ['V293_TaskCreateExt_TCB_call 209%Z f 101%Z 108%Z 205%Z 206%Z 207%Z 208%Z 204%Z',
                     'calle_rule_lvar', 'V293_create_tcb_arguments_read', 'V293_create_tcb_argument_types',
                     'LV 209%Z @ Tint8 |->result']:
            self.assertIn(text, body)
        self.assertIn('V293_TaskCreateExt_TCB_shared_call', self.section('SCActualReceiverCall', True))

    def test_return_cases_checked_semantically(self):
        for name, wanted in [('SC66Owner', 'SCExternal(SCOwner ** FPR)'),
                             ('SC0ConsumesOwner', 'SCExternal FPR'),
                             ('SCNoneRejected', 'None')]:
            body = self.section(name, True)
            self.assertIn(wanted, body)
            self.assertIn('astar_l_apure_elim', body)
        self.assertIn('V293_tcb_internal_no_shadow_globals', self.section('SCDomainNoShadow', True))
        independent = self.section('SCExternalGood', True)
        self.assertIn('V293_reservation_owner', independent)
        self.assertNotIn('V293_tcb_shared_external_good', independent)

    def test_stable_source_compilations(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('proof', SOURCE), ('probe', PROBE)]:
            label = stable[kind]
            row = json.loads((D / (label + '.json')).read_text())
            data = (R / path).read_bytes()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['source_sha256'], hashlib.sha256(data).hexdigest())
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(data, (D / (label + '.v.snapshot.txt')).read_bytes())

    def test_honest_limits_and_single_factor_protocol(self):
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertIn('all contract hypotheses jointly satisfiable', protocol['not_claimed'])
        doc = (R / 'audit/STAGE130_TCB_SHARED_CONTRACT.md').read_text()
        for text in ['联合可满足', '不是生产全局Inv', '单因素', '不是 Hook 函数体',
                     'token freshness', 'GoodI', 'WFIFun', 'GOOD_OS', 'uCOS3', '423']:
            self.assertIn(text, doc)


if __name__ == '__main__':
    unittest.main()
