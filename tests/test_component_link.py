"""链接结构和编译身份回归；语义结论依赖独立 Coq 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage146-component-link'
PROOF = 'certiucos/v293/proofs/V293ComponentLink.v'
PROBE = 'audit/probes/V293ComponentLinkProbe.v'


class ComponentLinkTests(unittest.TestCase):
    def setUp(self):
        self.proof = (R / PROOF).read_text()
        self.probe = (R / PROBE).read_text()

    def test_no_new_semantics_or_unchecked_holes(self):
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(PROOF), 1)
        self.assertNotIn('CertiOS.audit.', self.proof)
        for src in (self.proof, self.probe):
            self.assertNotRegex(src, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
            self.assertNotRegex(src, re.compile(r'^Inductive ', re.M))

    def test_actual_merged_api_builder_contracts(self):
        section = self.proof.split('Theorem V293_component_WFAPI :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('V293_OSVersion_api_contract', section)
        self.assertIn('V293_TimeSet_api_contract', section)
        self.assertIn('V293_component_api_unit', section)
        self.assertNotIn('api_rule', section)
        self.assertNotIn('WFAPI', '->'.join(section.split('Proof.', 1)[0].split('->')[:-1]))

    def test_common_environment_is_not_whole_program(self):
        statement = self.proof.split('Theorem V293_components_checked :', 1)[1].split('Proof.', 1)[0]
        for term in ('GoodI', 'WFAPI', 'WFIFun', 'no_fun_same'):
            self.assertIn(term, statement)
            self.assertNotIn(term, '->'.join(statement.split('->')[:-1]))
        self.assertEqual(statement.count('let Spec :='), 1)
        self.assertNotIn('verified_os\'', self.proof)
        self.assertNotIn('InitAsrt', self.proof)

    def test_same_local_invariant_has_satisfying_built_entry(self):
        section = self.probe.split('Theorem checked_linked_internal_entry_nonvacuous :', 1)[1]
        for term in ('LinkSpec 200%Z', 'BuildPreI LinkInternal', 'BuildRetI LinkInternal',
                     's |= pre', 'LinkBodyState', 'V293_sched_return_resource'):
            self.assertIn(term, section)
        self.assertIn('CurLINV LinkLI', self.probe)
        self.assertIn('set V293_witness_ge 1001%Z (80%positive,Tint32)', self.probe)

    def test_collision_control_observes_real_lookup_not_downstream_execution(self):
        section = self.proof.split('Theorem V293_component_collision_shadows_internal :', 1)[1].split('Qed.', 1)[0]
        for term in ('pumerge', 'V293_OSSchedNew_internal_unit version',
                     'P version = Some V293_OSVersion_function', 'P version <> Some'):
            self.assertIn(term, section)
        self.assertNotIn('lpstep', section)
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertIn('实际遮蔽', protocol['checks'][2])

    def test_checked_source_snapshots_and_frozen_implementation(self):
        labels = json.loads((D / 'stable-compiles.json').read_text())
        for kind, name in [('proof', PROOF), ('probe', PROBE)]:
            label = labels[kind]
            row = json.loads((D / (label + '.json')).read_text())
            source = (R / name).read_bytes()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256(source).hexdigest())
            self.assertEqual(source, (D / (label + '.v.snapshot.txt')).read_bytes())
        base = json.loads((D / 'baseline.json').read_text())
        for name, row in base.items():
            if name.endswith('.v') or name.startswith(('csrc/', 'framework/', 'tactics/')):
                self.assertEqual(hashlib.sha256((R / name).read_bytes()).hexdigest(), row['sha256'], name)


if __name__ == '__main__':
    unittest.main()
