"""Check bounded countdown evidence; never upgrade whole-function coverage."""
import hashlib
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage29-time-tick-countdown'
GATE = LOG / 'gate02'
PROOF = 'certiucos/v293/proofs/V293TimeTickCountdown.v'
PROBE = 'audit/probes/V293TimeTickCountdownProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


class TimeTickCountdownTests(unittest.TestCase):
    def test_all_checked_inputs_are_current(self):
        result = json.loads((GATE / 'result.json').read_text())
        self.assertTrue(result['passed'])
        self.assertEqual(result['source_count'], 170)
        for path, digest in result['input_sha256'].items():
            self.assertEqual(sha(ROOT / path), digest, path)

    def test_fixed_source_and_unmodified_actual_statement_model(self):
        protocol = json.loads((LOG / 'protocol.json').read_text())
        report = json.loads((ROOT / 'audit/physical-access-inventory.json').read_text())
        function = next(f for f in report['functions'] if f['name'] == 'OSTimeTick')
        self.assertEqual(protocol['source_identity'], report['source_identity_sha256'])
        self.assertEqual(protocol['function_identity'], function['identity'])
        baseline = json.loads((LOG / 'baseline.json').read_text())['files']
        path = 'certiucos/v293/code/V293OSTimeTick.v'
        self.assertEqual(sha(ROOT / path), baseline[path])

    def test_existing_sources_preserved_project_append_only(self):
        baseline = json.loads((LOG / 'baseline.json').read_text())['files']
        paths = [p for p in baseline if p.endswith('.v') and
                 p.startswith(('certiucos/', 'framework/', 'tactics/'))]
        self.assertEqual(len(paths), 169)
        for path in paths:
            self.assertEqual(sha(ROOT / path), baseline[path], path)
        project = (ROOT / '_CoqProject').read_bytes()
        suffix = (PROOF + '\n').encode()
        self.assertTrue(project.endswith(suffix))
        self.assertEqual(hashlib.sha256(project[:-len(suffix)]).hexdigest(),
                         baseline['_CoqProject'])

    def test_seven_actual_commands_and_two_kernel_modules(self):
        commands = json.loads((GATE / 'commands.json').read_text())
        self.assertEqual(len(commands), 7)
        self.assertTrue(all(c['passed'] and c['exit'] == c['expected'] for c in commands))
        kernel = next(c for c in commands if c['name'] == 'kernel')
        self.assertEqual(kernel['exit'], 0)
        self.assertEqual(kernel['command'][-2:], [
            'CertiOS.certiucos.v293.proofs.V293TimeTickCountdown',
            'CertiOS.audit.probes.V293TimeTickCountdownProbe'])
        for name, path in [('production', PROOF), ('probe', PROBE)]:
            self.assertEqual((GATE / (name + '.v.snapshot.txt')).read_bytes(),
                             (ROOT / path).read_bytes())

    def test_strict_bound_control_changes_only_one_precondition(self):
        original = (ROOT / PROOF).read_text()
        mutant = (GATE / 'weaken-bound.v.snapshot.txt').read_text()
        self.assertEqual(mutant, original.replace('(2 <= d <= Int.max_unsigned)%Z ->',
                                                 '(1 <= d <= Int.max_unsigned)%Z ->', 1))
        self.assertEqual(mutant.split('Proof.', 1)[1], original.split('Proof.', 1)[1])
        log = (GATE / 'weaken-bound.log').read_text()
        self.assertIn('Tactic failure:  Cannot find witness.', log)
        self.assertNotIn('inconsistent assumptions', log)

    def test_wrong_final_delay_keeps_whole_execution_proof(self):
        original = (ROOT / PROOF).read_text()
        before = 'load Tint32 Mf (bt,(base+44)%Z) = Some (Vint32 (Int.repr (d-1))) /\\'
        after = 'load Tint32 Mf (bt,(base+44)%Z) = Some (Vint32 (Int.repr d)) /\\'
        self.assertEqual(original.count(before), 1)
        mutant = (GATE / 'wrong-delay-readback.v.snapshot.txt').read_text()
        self.assertEqual(mutant, original.replace(before, after))
        name = 'Theorem V293_tick_countdown_iteration_owned_execution :'
        self.assertEqual(mutant.split(name, 1)[1].split('Proof.', 1)[1],
                         original.split(name, 1)[1].split('Proof.', 1)[1])
        log = (GATE / 'wrong-delay-readback.log').read_text()
        self.assertIn('Error:', log)
        self.assertNotIn('inconsistent assumptions', log)

    def test_independent_spatial_entry_and_execution_endpoints(self):
        probe = (ROOT / PROBE).read_text()
        entry = probe.split('Theorem CountdownEntrySatisfiable :', 1)[1].split('Proof.', 1)[0]
        self.assertNotIn('CountdownExecution', entry)
        self.assertIn('OwnershipCellsSpatial', probe)
        self.assertIn('CountdownExecution P ks enabled 2%Z Mlow', probe)
        self.assertIn('CountdownExecution P ks enabled 4294967295%Z Mhigh', probe)
        self.assertIn('CountdownFrameCells -> load tp Mf a = Some v', probe)
        self.assertIn('CountdownOneReachesExpiry', probe)

    def test_six_root_assumptions_exactly_existing_classical_helpers(self):
        allowed = {'FunctionalExtensionality.functional_extensionality_dep',
                   'Classical_Prop.classic'}
        for name, closed, axioms in [('production', 1, 1), ('probe', 1, 3)]:
            log = (GATE / (name + '.log')).read_text()
            self.assertEqual(log.count('Closed under the global context'), closed)
            self.assertEqual(log.count('Axioms:'), axioms)
            self.assertEqual(set(re.findall(r'^([A-Za-z][\w.]*)\s+:', log, re.M)), allowed)
        self.assertIsNone(re.search(r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit)\b',
                                    (ROOT / PROOF).read_text()))

    def test_no_downstream_or_whole_kernel_credit_and_failed_gate_retained(self):
        result = json.loads((GATE / 'result.json').read_text())
        for key in ['whole_source_clean_build', 'full_function_proved', 'good_os_proved',
                    'formal_six_gates_promoted']:
            self.assertFalse(result[key])
        self.assertTrue(result['reused_dependency_products'])
        for item in json.loads((GATE / 'ablations.json').read_text()):
            self.assertFalse(item['downstream_credit'])
            self.assertTrue(item['expected_rejection_observed'])
        failure = json.loads((LOG / 'gate01/harness-failure.json').read_text())
        self.assertTrue(failure['kernel_not_run'])
        self.assertEqual(failure['actual_completed_commands'], 5)
