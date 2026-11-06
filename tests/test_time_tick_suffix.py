"""Actual post-hook suffix evidence; no whole-function or whole-kernel credit."""
import hashlib
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage32-time-tick-suffix'
GATE = LOG / 'gate01'
PROOF = 'certiucos/v293/proofs/V293TimeTickSuffix.v'
PROBE = 'audit/probes/V293TimeTickSuffixProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


class TimeTickSuffixTests(unittest.TestCase):
    def test_checked_inputs_are_current(self):
        result = json.loads((GATE / 'result.json').read_text())
        self.assertTrue(result['passed'])
        self.assertEqual(result['source_count'], 173)
        self.assertEqual(len(result['input_sha256']), 182)
        for path, digest in result['input_sha256'].items():
            self.assertEqual(sha(ROOT / path), digest, path)

    def test_fixed_c_and_ast_identity(self):
        protocol = json.loads((LOG / 'protocol.json').read_text())
        inventory = json.loads((ROOT / 'audit/physical-access-inventory.json').read_text())
        function = next(f['identity'] for f in inventory['functions'] if f['name'] == 'OSTimeTick')
        self.assertEqual(protocol['function_identity'], function)
        self.assertEqual(inventory['source_identity_sha256'],
                         '74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da')
        self.assertEqual(sha(ROOT / 'csrc/upstream/v2.93.01/checkout/Source/os_core.c'),
                         function['source_file_sha256'])
        baseline = json.loads((LOG / 'baseline.json').read_text())['files']
        self.assertEqual(sha(ROOT / 'certiucos/v293/code/V293OSTimeTick.v'),
                         baseline['certiucos/v293/code/V293OSTimeTick.v'])
        proof = (ROOT / PROOF).read_text()
        exact = proof.split('Theorem V293_tick_post_hook_exact :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('scall hook nil', exact)
        self.assertIn('Proof. reflexivity.', exact)

    def test_cpu_hook_boundary_not_erased(self):
        protocol = json.loads((LOG / 'protocol.json').read_text())
        self.assertIn('OS_TIME_TICK_HOOK_EN=1u', protocol['hook_finding'])
        self.assertIn('OPEN_BOUNDARY_CONTRACT', protocol['hook_finding'])
        inventory = (ROOT / 'audit/repaired-source-inventory.json').read_text()
        self.assertIn('OSTimeTickHook', inventory)
        self.assertIn('OPEN_BOUNDARY_CONTRACT', inventory)
        proof = (ROOT / PROOF).read_text()
        self.assertIn('sseq (scall hook nil)', proof)
        self.assertNotIn('Definition OSTimeTickHook', proof)

    def test_existing_172_sources_and_registration_append(self):
        baseline = json.loads((LOG / 'baseline.json').read_text())['files']
        sources = [p for p in baseline if p.endswith('.v') and
                   p.startswith(('certiucos/v293/', 'framework/', 'tactics/'))]
        self.assertEqual(len(sources), 172)
        for path in sources:
            self.assertEqual(sha(ROOT / path), baseline[path], path)
        project = (ROOT / '_CoqProject').read_bytes()
        suffix = (PROOF + '\n').encode()
        self.assertEqual(project.count(suffix), 1)
        self.assertTrue(project.endswith(suffix))
        self.assertEqual(hashlib.sha256(project[:-len(suffix)]).hexdigest(), baseline['_CoqProject'])

    def test_eight_actual_commands_and_kernel_check(self):
        commands = json.loads((GATE / 'commands.json').read_text())
        self.assertEqual(len(commands), 8)
        self.assertTrue(all(c['passed'] and c['exit'] == c['expected'] for c in commands))
        self.assertEqual([c['exit'] for c in commands], [0, 0, 0, 0, 0, 1, 1, 0])
        self.assertEqual(commands[-1]['command'][-2:], [
            'CertiOS.certiucos.v293.proofs.V293TimeTickSuffix',
            'CertiOS.audit.probes.V293TimeTickSuffixProbe'])
        for name, path in [('production', PROOF), ('probe', PROBE)]:
            self.assertEqual((GATE / (name + '.v.snapshot.txt')).read_bytes(), (ROOT / path).read_bytes())

    def test_wrong_time_single_factor(self):
        self.check_mutant('wrong-final-time',
            'load Tint32 Mf (bn,0%Z) = Some (Vint32 (Int.add tick Int.one)) /\\',
            'load Tint32 Mf (bn,0%Z) = Some (Vint32 tick) /\\', 'FinalTime')

    def test_wrong_active_pointer_single_factor(self):
        self.check_mutant('wrong-active-pointer',
            'load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr (if Nat.eqb run 1 then idle else scan)) /\\',
            'load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr (if Nat.eqb run 1 then scan else scan)) /\\',
            'FinalPointer')

    def check_mutant(self, name, before, after, diagnostic):
        original = (ROOT / PROOF).read_text()
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

    def test_independent_entry_run_cases_and_unsigned_wrap(self):
        probe = (ROOT / PROBE).read_text()
        entry = probe.split('Theorem SuffixEntrySatisfiable :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('forall tick run enabled, run<256', entry)
        self.assertNotIn('SuffixExecution', entry)
        self.assertIn('OwnershipCellsSpatial', probe)
        self.assertIn('V293_tick_pointer_cell 70%positive LoopIdle :: tl LoopCells', probe)
        self.assertIn('SuffixRunningOneWrapped', probe)
        self.assertIn('SuffixRunningTwoNotTrue', probe)
        self.assertIn('SuffixRunningZeroStillTicks', probe)
        self.assertIn('SuffixExecution (Int.repr 4294967295) 1 enabled Mf', probe)
        self.assertIn('SuffixExecution Int.zero 2 enabled Mf', probe)
        self.assertIn('SuffixExecution (Int.repr 4294967295) 0 enabled Mf', probe)
        self.assertIn('In (a,tp,v) (SuffixExpectedCells tick run) -> load tp Mf a = Some v', probe)
        proof = (ROOT / PROOF).read_text()
        statement = proof.split('Theorem V293_tick_post_hook_owned_execution :', 1)[1].split('Proof.', 1)[0]
        self.assertNotIn('V293_local_steps', statement.split('exists Mf,', 1)[0])
        self.assertNotIn('store ', statement.split('exists Mf,', 1)[0])
        for text in ['V293_tick_while_owned_execution', 'V293_owned_record_cell_update',
                     'sassign (evar ptcb) (evar head)', 'Nat.eqb run 1']:
            self.assertIn(text, proof)

    def test_seven_roots_only_existing_assumptions(self):
        allowed = {'FunctionalExtensionality.functional_extensionality_dep', 'Classical_Prop.classic'}
        for name, closed, axioms in [('production', 1, 1), ('probe', 0, 5)]:
            log = (GATE / (name + '.log')).read_text()
            self.assertEqual(log.count('Closed under the global context'), closed)
            self.assertEqual(log.count('Axioms:'), axioms)
            self.assertEqual(set(re.findall(r'^([A-Za-z][\w.]*)\s+:', log, re.M)), allowed)
        for path in [PROOF, PROBE]:
            self.assertIsNone(re.search(r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit)\b',
                                        (ROOT / path).read_text()))

    def test_no_whole_kernel_promotion(self):
        result = json.loads((GATE / 'result.json').read_text())
        for key in ['whole_source_clean_build', 'full_function_proved', 'good_os_proved',
                    'formal_six_gates_promoted']:
            self.assertFalse(result[key])
        self.assertTrue(result['reused_dependency_products'])
        baseline = json.loads((LOG / 'baseline.json').read_text())['files']
        self.assertEqual(sha(ROOT / 'audit/coverage.json'), baseline['audit/coverage.json'])
        for item in json.loads((GATE / 'ablations.json').read_text()):
            for key in ['single_factor', 'target_proof_suffix_unchanged', 'expected_rejection_observed']:
                self.assertTrue(item[key])
            self.assertFalse(item['downstream_credit'])
