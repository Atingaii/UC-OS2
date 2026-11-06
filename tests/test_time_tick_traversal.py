"""Bounded tick iteration evidence, not whole-function coverage credit."""
import hashlib
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage28-time-tick'
GATE = LOG / 'gate01'
CODE = 'certiucos/v293/code/V293OSTimeTick.v'
PROOF = 'certiucos/v293/proofs/V293TimeTickTraversal.v'
PROBE = 'audit/probes/V293TimeTickTraversalProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


class TimeTickTraversalTests(unittest.TestCase):
    def test_actual_inputs_are_still_the_checked_inputs(self):
        result = json.loads((GATE / 'result.json').read_text())
        self.assertTrue(result['passed'])
        for path, digest in result['input_sha256'].items():
            self.assertEqual(sha(ROOT / path), digest, path)

    def test_source_body_identity_and_real_accesses(self):
        report = json.loads((ROOT / 'audit/physical-access-inventory.json').read_text())
        function = next(x for x in report['functions'] if x['name'] == 'OSTimeTick')
        protocol = json.loads((LOG / 'protocol.json').read_text())
        self.assertEqual(function['identity'], protocol['function_identity'])
        self.assertEqual(report['source_identity_sha256'], protocol['source_identity'])
        self.assertEqual(function['identity']['first_line'], 937)
        self.assertEqual(function['identity']['last_line'], 1008)
        self.assertIn('read', function['direct_resources']['os_tcb.OSTCBDly'])
        self.assertEqual(function['direct_resources']['os_tcb.OSTCBNext'], ['read'])

    def test_production_and_fixture_snapshots_are_exact(self):
        for name, path in [('code', CODE), ('production', PROOF), ('fixture', PROBE)]:
            self.assertEqual((GATE / (name + '.v.snapshot.txt')).read_bytes(),
                             (ROOT / path).read_bytes())

    def test_kernel_and_compilation_are_actual_successes(self):
        commands = json.loads((GATE / 'commands.json').read_text())
        self.assertEqual(len(commands), 8)
        self.assertTrue(all(x['passed'] for x in commands))
        kernel = next(x for x in commands if x['name'] == 'kernel')
        self.assertEqual(kernel['exit'], 0)
        self.assertEqual(kernel['command'][-2:], [
            'CertiOS.certiucos.v293.proofs.V293TimeTickTraversal',
            'CertiOS.audit.probes.V293TimeTickTraversalProbe'])
        self.assertTrue((GATE / 'kernel.log').is_file())

    def test_next_to_prev_is_one_factor_with_unchanged_proof(self):
        code = (ROOT / CODE).read_text()
        mutated = (GATE / 'next-to-prev-V293OSTimeTick.v.snapshot.txt').read_text()
        self.assertEqual(mutated, code.replace(
            'sassign (evar ptcb) (V293_tick_field ptcb 7%Z).',
            'sassign (evar ptcb) (V293_tick_field ptcb 8%Z).'))
        self.assertNotEqual(mutated, code)
        self.assertEqual((GATE / 'next-to-prev-V293TimeTickTraversal.v.snapshot.txt').read_bytes(),
                         (ROOT / PROOF).read_bytes())
        self.assertIn('Unable to unify', (GATE / 'next-to-prev-reject.log').read_text())

    def test_wrong_post_keeps_entire_proof_suffix(self):
        original = (ROOT / PROBE).read_text()
        mutant = (GATE / 'wrong-post-pointer-V293TimeTickTraversalProbe.v.snapshot.txt').read_text()
        self.assertEqual(mutant, original.replace(
            'load (Tptr V293_tcb_type) Mf (70%positive,0%Z) = Some (Vptr TickNext)',
            'load (Tptr V293_tcb_type) Mf (70%positive,0%Z) = Some (Vptr (81%positive,Int.repr 8))'))
        self.assertEqual(original.split('Proof.\n  intros P ks enabled.', 1)[1],
                         mutant.split('Proof.\n  intros P ks enabled.', 1)[1])
        self.assertIn('Read', (GATE / 'wrong-post-pointer-reject.log').read_text())

    def test_assumptions_are_bounded_for_all_seven_roots(self):
        production = (GATE / 'production.log').read_text()
        fixture = (GATE / 'fixture.log').read_text()
        self.assertEqual(production.count('Closed under the global context'), 3)
        self.assertEqual(production.count('Axioms:'), 1)
        self.assertEqual(fixture.count('Closed under the global context'), 1)
        self.assertEqual(fixture.count('Axioms:'), 2)
        actual = set(re.findall(r'^([A-Za-z][\w.]*)\s+:', production + fixture, re.M))
        self.assertEqual(actual, {'FunctionalExtensionality.functional_extensionality_dep',
                                  'Classical_Prop.classic'})

    def test_no_formal_coverage_or_whole_build_claim(self):
        result = json.loads((GATE / 'result.json').read_text())
        self.assertFalse(result['whole_source_clean_build'])
        self.assertTrue(result['reused_dependency_products'])
        self.assertFalse(result['full_function_proved'])
        self.assertFalse(result['good_os_proved'])
        for control in json.loads((GATE / 'ablations.json').read_text()):
            self.assertTrue(control['expected_rejection_observed'])
            self.assertFalse(control['downstream_credit'])

    def test_project_lists_new_modules_without_replacing_old_sources(self):
        baseline = json.loads((LOG / 'baseline.json').read_text())
        for path, digest in baseline['files'].items():
            if path.endswith('.v') and path.startswith(('certiucos/', 'framework/', 'tactics/')):
                self.assertEqual(sha(ROOT / path), digest, path)
        project = (ROOT / '_CoqProject').read_text().splitlines()
        self.assertEqual(project.count(CODE), 1)
        self.assertEqual(project.count(PROOF), 1)


if __name__ == '__main__':
    unittest.main()
