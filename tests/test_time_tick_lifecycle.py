"""Actual call/local lifecycle evidence, keeping the hook boundary open."""
import hashlib
import json
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage34-time-tick-lifecycle'
GATE = LOG / 'gate01'
PROOF = 'certiucos/v293/proofs/V293TimeTickLifecycle.v'
PROBE = 'audit/probes/V293TimeTickLifecycleProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()


class TimeTickLifecycleTests(unittest.TestCase):
    def test_checked_inputs_current(self):
        gate = json.loads((GATE / 'result.json').read_text())
        self.assertTrue(gate['passed'])
        self.assertEqual(gate['source_count'], 175)
        self.assertEqual(len(gate['input_sha256']), 185)
        for p, h in gate['input_sha256'].items():
            self.assertEqual(sha(ROOT / p), h, p)

    def test_fixed_function_identity(self):
        protocol = json.loads((LOG / 'protocol.json').read_text())
        inventory = json.loads((ROOT / 'audit/physical-access-inventory.json').read_text())
        identity = next(f['identity'] for f in inventory['functions'] if f['name'] == 'OSTimeTick')
        self.assertEqual(protocol['function_identity'], identity)
        self.assertEqual(sha(ROOT / 'csrc/upstream/v2.93.01/checkout/Source/os_core.c'), identity['source_file_sha256'])
        self.assertEqual(inventory['source_identity_sha256'], protocol['source_identity_sha256'])

    def test_old_sources_and_exact_project_append(self):
        files = json.loads((LOG / 'baseline.json').read_text())['files']
        sources = [p for p in files if p.endswith('.v') and p.startswith(('certiucos/v293/', 'framework/', 'tactics/'))]
        self.assertEqual(len(sources), 174)
        for p in sources:
            self.assertEqual(sha(ROOT / p), files[p], p)
        project = (ROOT / '_CoqProject').read_bytes()
        suffix = (PROOF + '\n').encode()
        self.assertEqual(project.count(suffix), 1)
        self.assertTrue(project.endswith(suffix))
        self.assertEqual(hashlib.sha256(project[:-len(suffix)]).hexdigest(), files['_CoqProject'])

    def test_real_call_two_allocations_and_hook_stop(self):
        source = (ROOT / PROOF).read_text()
        prefix = source.split('Theorem V293_tick_call_to_hook :', 1)[1].split('Qed.', 1)[0]
        premises = prefix.split('exists Ms,', 1)[0]
        for oracle in ['V293_local_steps', 'cstep', 'store ', 'free ']:
            self.assertNotIn(oracle, premises)
        for term in ['snpcall_step', 'sfexec_step', 'sallocend_step', 'V293_success_assign_zero', 'scall hook nil', 'Some Vundef']:
            self.assertIn(term, prefix)
        self.assertEqual(prefix.count('eapply salloclv_step'), 2)
        self.assertIn('sseq (V293_tick_body ptcb rows group saved now running head hook) sret', source)

    def test_real_suffix_and_free_from_ownership(self):
        source = (ROOT / PROOF).read_text()
        tail = source.split('Theorem V293_tick_suffix_void_lifecycle :', 1)[1]
        premises = tail.split('exists Ms Mf,', 1)[0]
        for oracle in ['V293_local_steps', 'cstep', 'store ', 'free ', 'V293_bytes_writable']:
            self.assertNotIn(oracle, premises)
        for term in ['V293_tick_uninitialized_suffix_execution', 'V293_tick_raw_owned_writable', 'V293_tick_local_addresses', 'V293_tick_void_return', 'exact Returned']:
            self.assertIn(term, tail)
        returning = source.split('Theorem V293_tick_void_return :', 1)[1].split('Qed.', 1)[0]
        for term in ['sret_step', 'sfreeend_step', 'V293_sfree_construct_execution', '(sskip None)']:
            self.assertIn(term, returning)
        self.assertNotIn('srete', returning)

    def test_independent_same_memory_and_final_readbacks(self):
        source = (ROOT / PROBE).read_text()
        for term in ['OwnershipCellsSpatial', 'LifecycleFreshSaved', 'V293_tick_call_to_hook', 'V293_tick_suffix_void_lifecycle', 'LifecycleReadExpected', 'StorageExpectedCells tick run', 'LifecycleRunOneWrap', 'LifecycleRunTwoNotTrue', 'LifecycleHookNotDefined']:
            self.assertIn(term, source)
        self.assertIn('LifecycleTail enabled Mp Mf', source)
        self.assertIn('forall tick run enabled, run<256', source)
        self.assertIn('TWO checkpoints', source)
        self.assertIn('LifecycleProgram 2002%Z = None', source)

    def test_actual_commands_and_kernel(self):
        commands = json.loads((GATE / 'commands.json').read_text())
        self.assertEqual([c['exit'] for c in commands], [0, 0, 0, 0, 0, 0, 1, 1, 0])
        self.assertTrue(all(c['passed'] and c['exit'] == c['expected'] for c in commands))
        self.assertEqual(commands[-1]['command'][-2:], ['CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle', 'CertiOS.audit.probes.V293TimeTickLifecycleProbe'])
        for name, path in [('production', PROOF), ('probe', PROBE)]:
            self.assertEqual((GATE / (name + '.v.snapshot.txt')).read_bytes(), (ROOT / path).read_bytes())

    def check_mutant(self, name, before, after, marker):
        original = (ROOT / PROOF).read_text()
        mutant = (GATE / (name + '.v.snapshot.txt')).read_text()
        self.assertEqual(original.count(before), 1)
        self.assertEqual(mutant, original.replace(before, after))
        self.assertEqual(re.findall(r'Proof\.(.*?)Qed\.', original, re.S), re.findall(r'Proof\.(.*?)Qed\.', mutant, re.S))
        log = (GATE / (name + '.log')).read_text()
        self.assertIn('Error:', log)
        self.assertIn(marker, log)
        self.assertNotIn('Cannot find a physical path', log)

    def test_single_factor_saved_zero(self):
        self.check_mutant('wrong-saved-zero', 'load Tint32 Ms (bs,0%Z) = Some (Vint32 Int.zero) /\\', 'load Tint32 Ms (bs,0%Z) = Some (Vint32 Int.one) /\\', 'FinalSaved')

    def test_single_factor_freed_scan(self):
        self.check_mutant('wrong-freed-scan', 'get Mf (bc,Z.of_nat k) = None /\\ get Mf (bs,Z.of_nat k) = None).', 'get Mf (bc,Z.of_nat k) = Some (true,Undef) /\\ get Mf (bs,Z.of_nat k) = None).', 'Removed')

    def test_assumptions_and_bounded_claim(self):
        allowed = {'FunctionalExtensionality.functional_extensionality_dep', 'Classical_Prop.classic'}
        for name, axioms, closed in [('production', 3, 0), ('probe', 4, 1)]:
            log = (GATE / (name + '.log')).read_text()
            self.assertEqual(log.count('Axioms:'), axioms)
            self.assertEqual(log.count('Closed under the global context'), closed)
            self.assertEqual(set(re.findall(r'^([A-Za-z][\w.]*)\s+:', log, re.M)), allowed)
        gate = json.loads((GATE / 'result.json').read_text())
        self.assertTrue(gate['cpu_hook_boundary_open'])
        for key in ['full_function_proved', 'good_os_proved', 'whole_source_clean_build', 'formal_six_gates_promoted']:
            self.assertFalse(gate[key])
        self.assertFalse(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture)\b', (ROOT / PROOF).read_text()))


if __name__ == '__main__':
    unittest.main()
