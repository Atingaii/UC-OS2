"""Check actual Dly=1 execution evidence, without upgrading whole-kernel credit."""
import hashlib
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage30-time-tick-expiry'
GATE = LOG / 'gate01'
PROOF = 'certiucos/v293/proofs/V293TimeTickExpiry.v'
PROBE = 'audit/probes/V293TimeTickExpiryProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


class TimeTickExpiryTests(unittest.TestCase):
    def test_checked_inputs_are_current(self):
        result = json.loads((GATE / 'result.json').read_text())
        self.assertTrue(result['passed'])
        self.assertEqual(result['source_count'], 171)
        for path, digest in result['input_sha256'].items():
            self.assertEqual(sha(ROOT / path), digest, path)

    def test_fixed_actual_c_and_statement_identity(self):
        protocol = json.loads((LOG / 'protocol.json').read_text())
        inventory = json.loads((ROOT / 'audit/physical-access-inventory.json').read_text())
        function = next(f['identity'] for f in inventory['functions'] if f['name'] == 'OSTimeTick')
        self.assertEqual(protocol['function_identity'], function)
        self.assertEqual(protocol['source_identity'], inventory['source_identity_sha256'])
        inspected = json.loads((LOG / 'source-inspection.json').read_text())
        self.assertTrue(inspected['equals_frozen_repaired_core'])
        self.assertEqual(inspected['sha256'], function['source_file_sha256'])
        self.assertEqual(sha(ROOT / inspected['physical_path']), inspected['sha256'])
        baseline = json.loads((LOG / 'baseline.json').read_text())['files']
        self.assertEqual(sha(ROOT / 'certiucos/v293/code/V293OSTimeTick.v'),
                         baseline['certiucos/v293/code/V293OSTimeTick.v'])
        self.assertIn('ptcb->OSTCBStat & OS_STAT_SUSPEND', (LOG / 'source-excerpt.txt').read_text())

    def test_existing_170_sources_unchanged_and_registration_append_only(self):
        baseline = json.loads((LOG / 'baseline.json').read_text())['files']
        sources = [p for p in baseline if p.endswith('.v') and
                   p.startswith(('certiucos/v293/', 'framework/', 'tactics/'))]
        self.assertEqual(len(sources), 170)
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
            'CertiOS.certiucos.v293.proofs.V293TimeTickExpiry',
            'CertiOS.audit.probes.V293TimeTickExpiryProbe'])
        for name, path in [('production', PROOF), ('probe', PROBE)]:
            self.assertEqual((GATE / (name + '.v.snapshot.txt')).read_bytes(),
                             (ROOT / path).read_bytes())

    def test_pending_negative_changes_only_one_final_readback(self):
        original = (ROOT / PROOF).read_text()
        before = 'load Tint8 Mf (bt,(base+49)%Z) = Some (V293_byteval (V293_tick_expired_pend s)) /\\'
        after = 'load Tint8 Mf (bt,(base+49)%Z) = Some (V293_byteval 0) /\\'
        self.check_mutant('wrong-pending-readback', original, before, after)

    def test_suspension_negative_changes_only_one_final_readback(self):
        original = (ROOT / PROOF).read_text()
        before = 'load Tint8 Mf (br,Z.of_nat y) = Some (V293_byteval (V293_tick_expired_row s r x)) /\\'
        after = 'load Tint8 Mf (br,Z.of_nat y) = Some (V293_byteval (Nat.setbit r x)) /\\'
        self.check_mutant('ignore-suspension-readback', original, before, after)

    def check_mutant(self, name, original, before, after):
        self.assertEqual(original.count(before), 1)
        mutant = (GATE / (name + '.v.snapshot.txt')).read_text()
        self.assertEqual(mutant, original.replace(before, after))
        marker = 'Theorem V293_tick_expiry_iteration_owned_execution :'
        self.assertEqual(mutant.split(marker, 1)[1].split('Proof.', 1)[1],
                         original.split(marker, 1)[1].split('Proof.', 1)[1])
        log = (GATE / (name + '.log')).read_text()
        self.assertIn('Tactic failure: Classical tauto failed.', log)
        for text in ['Cannot find a physical path', 'Cannot find library', 'inconsistent assumptions']:
            self.assertNotIn(text, log)

    def test_nonvacuous_entry_all_stat_bytes_and_literal_outcomes(self):
        probe = (ROOT / PROBE).read_text()
        entry = probe.split('Theorem ExpiryEntrySatisfiable :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('forall enabled s', entry)
        self.assertIn('s < 256', entry)
        self.assertNotIn('ExpiryExecution', entry)
        self.assertIn('OwnershipCellsSpatial', probe)
        self.assertIn('[(0,0,0,3,132);(1,0,1,3,132);(8,8,0,1,128);(9,8,1,1,128)]', probe)
        self.assertIn('[2;4;16;32;64;128;255]', probe)
        self.assertIn('ExpiryFrameCells -> load tp Mf a = Some v', probe)
        self.assertIn('((93%positive,0%Z),Tint8,V293_byteval 85)', probe)
        self.assertIn('(enabled,(3%nat :: nil),(false :: nil))', probe)
        proof = (ROOT / PROOF).read_text()
        self.assertIn('V293_tick_expiry_cells bc bt base next Int.zero next', proof)
        self.assertIn('apply ExpiryExec.', proof)
        self.assertIn('apply excrit_step;', proof)

    def test_seven_roots_only_existing_classical_assumptions(self):
        allowed = {'FunctionalExtensionality.functional_extensionality_dep', 'Classical_Prop.classic'}
        for name, closed, axioms in [('production', 1, 2), ('probe', 0, 4)]:
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
        self.assertEqual(delta['previous'], 359)
        self.assertEqual(delta['removed'], [])
        self.assertEqual(len(delta['added']), 2)
