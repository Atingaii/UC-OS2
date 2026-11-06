"""结构防回退检查；证明信用来自 Coq 内核而非文本匹配。"""
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
PROOF = ROOT / 'certiucos/v293/proofs/V293TCBLinkedHoare.v'
PROBE = ROOT / 'audit/probes/V293TCBLinkedHoareProbe.v'

class TCBLinkedHoareTests(unittest.TestCase):
    def test_no_axioms_or_probe_dependencies(self):
        for path in [PROOF, PROBE]:
            self.assertNotRegex(path.read_text(), r'\b(Axiom|Parameter|Conjecture|Admitted|admit)\b')
            self.assertNotRegex(path.read_text(), r'Require(?: Import)? CertiOS\.audit\.probes\.')

    def test_actual_full_body_with_only_two_real_hook_obligations(self):
        text = PROOF.read_text()
        statement = text.split('Theorem V293_OS_TCBInit_linked_body_hoare :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(statement.count('InfRules '), 3)
        self.assertEqual(statement.count('(scall hi [evar 108%Z])'), 1)
        self.assertEqual(statement.count('(scall hc [evar 108%Z])'), 1)
        self.assertIn('(V293_TCBInit_function_body hi hc)', statement)
        self.assertNotIn('V293_TCB_publish', statement)
        self.assertNotRegex(statement, r'\b(evalval|evaladdr|sfexec|exec|V293_stmt_exec)\b')

    def test_resource_bridge_is_proved_not_a_premise(self):
        text = PROOF.read_text()
        statement = text.split('Theorem V293_tcb_initialized_publish_view :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(statement.count('==>'), 1)
        self.assertNotIn('InfRules', statement)
        for token in ['V293_link_cells_permutation', 'V293_link_layout', 'V293_link_exchange',
                      'V293_tcb_initialized_publish_view', 'apply V293_OS_TCBInit_publish_hoare']:
            self.assertIn(token, text)
        self.assertIn('apply RuleSound', text)

    def test_preserved_cells_are_spatial_not_erased(self):
        text = PROOF.read_text()
        residual = text.split('Definition V293_link_residual ', 1)[1].split('Definition V293_link_residual_frame', 1)[0]
        for token in ['((table,(4*Z.of_nat p)%Z)', '((bg,0%Z),Tptr V293_tcb_type,next)',
                      '((bt,(base+50)%Z),Tint8,V293_byteval p)', '((bu,0%Z),Tint32,Vint32 Int.zero)']:
            self.assertIn(token, residual)
        self.assertIn('V293_link_residual_frame', text.split('Definition V293_link_return_post', 1)[1])

    def test_independent_literal_joint_entry_post_loads_and_sizes(self):
        text = PROBE.read_text()
        for name in ['LinkRawLiteral', 'LinkInitialEntry', 'LinkFinalEntry', 'LinkPriorityRead',
                     'LinkSlotRead', 'LinkFreeHeadRead', 'LinkNextRead', 'LinkPrevRead', 'LinkHeadRead',
                     'LinkOldBacklinkRead', 'LinkGroupRead', 'LinkRowRead', 'LinkCounterRead',
                     'LinkWrongFreeHead', 'LinkReturnedZero', 'LinkCoreSize']:
            self.assertIn('Theorem ' + name, text)
        self.assertIn('Definition LinkBodyChecked', text)
        self.assertIn('then 100 else 96', text)
        self.assertIn('then 36 else 35', text)
        self.assertIn('128%Z', text)
        self.assertIn('256%Z', text)

    def test_active_build_once(self):
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(str(PROOF.relative_to(ROOT))), 1)

if __name__ == '__main__':
    unittest.main()
