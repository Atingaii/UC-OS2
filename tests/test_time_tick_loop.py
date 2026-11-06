"""Check actual finite while execution evidence, without upgrading whole-kernel credit."""
import hashlib
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage31-time-tick-loop'
GATE = LOG / 'gate01'
PROOF = 'certiucos/v293/proofs/V293TimeTickLoop.v'
PROBE = 'audit/probes/V293TimeTickLoopProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


class TimeTickLoopTests(unittest.TestCase):
    def test_checked_inputs_are_current(self):
        result = json.loads((GATE / 'result.json').read_text())
        self.assertTrue(result['passed'])
        self.assertEqual(result['source_count'], 172)
        for path, digest in result['input_sha256'].items():
            self.assertEqual(sha(ROOT / path), digest, path)

    def test_fixed_actual_c_and_statement_identity(self):
        protocol = json.loads((LOG / 'protocol.json').read_text())
        inventory = json.loads((ROOT / 'audit/physical-access-inventory.json').read_text())
        function = next(f['identity'] for f in inventory['functions'] if f['name'] == 'OSTimeTick')
        self.assertEqual(protocol['function_identity'], function)
        self.assertEqual(inventory['source_identity_sha256'],
                         '74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da')
        core = ROOT / 'csrc/upstream/v2.93.01/checkout/Source/os_core.c'
        self.assertEqual(sha(core), function['source_file_sha256'])
        baseline = json.loads((LOG / 'baseline.json').read_text())['files']
        self.assertEqual(sha(ROOT / 'certiucos/v293/code/V293OSTimeTick.v'),
                         baseline['certiucos/v293/code/V293OSTimeTick.v'])
        self.assertIn('while (ptcb->OSTCBPrio != OS_TASK_IDLE_PRIO)', (LOG / 'source-excerpt.txt').read_text())

    def test_existing_171_sources_unchanged_and_registration_append_only(self):
        baseline = json.loads((LOG / 'baseline.json').read_text())['files']
        sources = [p for p in baseline if p.endswith('.v') and
                   p.startswith(('certiucos/v293/', 'framework/', 'tactics/'))]
        self.assertEqual(len(sources), 171)
        for path in sources:
            self.assertEqual(sha(ROOT / path), baseline[path], path)
        project = (ROOT / '_CoqProject').read_bytes()
        suffix = (PROOF + '\n').encode()
        self.assertEqual(project.count(suffix), 1)
        self.assertTrue(project.endswith(suffix))
        self.assertEqual(hashlib.sha256(project[:-len(suffix)]).hexdigest(), baseline['_CoqProject'])

    def test_seven_actual_commands_and_independent_kernel_check(self):
        commands = json.loads((GATE / 'commands.json').read_text())
        self.assertEqual(len(commands), 7)
        self.assertTrue(all(c['passed'] and c['exit'] == c['expected'] for c in commands))
        self.assertEqual([c['exit'] for c in commands], [0, 0, 0, 0, 1, 1, 0])
        kernel = commands[-1]
        self.assertEqual(kernel['name'], 'kernel')
        self.assertEqual(kernel['command'][-2:], [
            'CertiOS.certiucos.v293.proofs.V293TimeTickLoop',
            'CertiOS.audit.probes.V293TimeTickLoopProbe'])
        for name, path in [('production', PROOF), ('probe', PROBE)]:
            self.assertEqual((GATE / (name + '.v.snapshot.txt')).read_bytes(),
                             (ROOT / path).read_bytes())

    def test_wrong_final_pointer_single_factor(self):
        original = (ROOT / PROOF).read_text()
        before = 'load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr idle) /\\'
        after = 'load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr (V293_tick_head tasks idle)) /\\'
        self.check_mutant('wrong-final-pointer', original, before, after, 'FinalPointer')

    def test_nonidle_constraint_single_factor(self):
        original = (ROOT / PROOF).read_text()
        before = 'V293_tick_prio t<256 /\\ V293_tick_prio t<>12.'
        after = 'V293_tick_prio t<256 /\\ True.'
        self.check_mutant('drop-nonidle-constraint', original, before, after, 'Nonidle')

    def check_mutant(self, name, original, before, after, diagnostic):
        self.assertEqual(original.count(before), 1)
        mutant = (GATE / (name + '.v.snapshot.txt')).read_text()
        self.assertEqual(mutant, original.replace(before, after))
        self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.', mutant, re.S),
                         re.findall(r'Proof\.(.*?)Qed\.', original, re.S))
        log = (GATE / (name + '.log')).read_text()
        self.assertIn(diagnostic, log)
        self.assertIn('Error:', log)
        for text in ['Cannot find a physical path', 'Cannot find library', 'inconsistent assumptions']:
            self.assertNotIn(text, log)

    def test_independent_mixed_entry_literal_fields_and_real_idle_guard(self):
        probe = (ROOT / PROBE).read_text()
        entry = probe.split('Theorem LoopEntrySatisfiable :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('forall enabled', entry)
        self.assertNotIn('LoopExecution', entry)
        self.assertIn('OwnershipCellsSpatial', probe)
        self.assertIn('Theorem LoopIdleHasNoIterationFields', probe)
        self.assertIn('LoopMemory (87%positive,48%Z) = None', probe)
        self.assertIn('LoopMemory (87%positive,24%Z) = None', probe)
        self.assertIn('LoopExpectedCells -> load tp Mf a = Some v', probe)
        self.assertIn('LoopFrameCells -> load tp Mf a = Some v', probe)
        self.assertIn('Build_V293_tick_task 82%positive 12%Z 2%Z 0 7 0 1 1', probe)
        self.assertIn('Build_V293_tick_task 84%positive 12%Z 0%Z 8 1 1 1 9', probe)
        self.assertIn('Build_V293_tick_task 86%positive 12%Z 0%Z 8 0 1 3 11', probe)
        self.assertIn('93%positive 3 4 4', probe)
        self.assertIn('(enabled,(3%nat :: nil),(false :: nil))', probe)
        proof = (ROOT / PROOF).read_text()
        statement = proof.split('Theorem V293_tick_while_owned_execution :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('Forall V293_tick_task_valid tasks', statement)
        self.assertIn('map V293_tick_task_after tasks', statement)
        for text in ['swhile_step', 'svwhilef_step', 'svwhilet_step', 'exact RestExec',
                     'V293_tick_zero_iteration_owned_execution',
                     'V293_tick_countdown_iteration_owned_execution',
                     'V293_tick_expiry_iteration_owned_execution']:
            self.assertIn(text, proof)
        self.assertNotIn('V293_local_steps', statement.split('exists Mf,', 1)[0])

    def test_seven_roots_only_existing_classical_assumptions(self):
        allowed = {'FunctionalExtensionality.functional_extensionality_dep', 'Classical_Prop.classic'}
        for name, closed, axioms in [('production', 0, 4), ('probe', 0, 3)]:
            log = (GATE / (name + '.log')).read_text()
            self.assertEqual(log.count('Closed under the global context'), closed)
            self.assertEqual(log.count('Axioms:'), axioms)
            self.assertEqual(set(re.findall(r'^([A-Za-z][\w.]*)\s+:', log, re.M)), allowed)
        self.assertIsNone(re.search(r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit)\b',
                                    (ROOT / PROOF).read_text()))

    def test_no_downstream_or_whole_kernel_promotion(self):
        result = json.loads((GATE / 'result.json').read_text())
        for key in ['whole_source_clean_build', 'full_function_proved', 'good_os_proved',
                    'formal_six_gates_promoted']:
            self.assertFalse(result[key])
        self.assertTrue(result['reused_dependency_products'])
        self.assertEqual(sha(ROOT / 'audit/coverage.json'),
                         json.loads((LOG / 'baseline.json').read_text())['files']['audit/coverage.json'])
        for item in json.loads((GATE / 'ablations.json').read_text()):
            self.assertTrue(item['single_factor'])
            self.assertTrue(item['target_proof_suffix_unchanged'])
            self.assertTrue(item['expected_rejection_observed'])
            self.assertFalse(item['downstream_credit'])
        delta = json.loads((LOG / 'old-test-delta.json').read_text())
        self.assertEqual(delta['previous'], 361)
        self.assertEqual(delta['removed'], [])
        self.assertEqual(len(delta['added']), 2)
