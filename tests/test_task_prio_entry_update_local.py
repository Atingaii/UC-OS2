"""Static regression checks; semantic execution is checked by --entry-update."""
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage26-task-prio-entry-update'
spec = importlib.util.spec_from_file_location('entry_update_gate', ROOT / 'scripts/check-v293-task-prio-rekey.py')
GATE = importlib.util.module_from_spec(spec)
spec.loader.exec_module(GATE)
NAME = 'Theorem V293_task_prio_entry_update_execution :'


class EntryUpdateLocalTests(unittest.TestCase):
    def setUp(self):
        self.proof = (ROOT / GATE.PROOF).read_text()
        self.code = (ROOT / GATE.CODE).read_text()
        section = self.proof.split(NAME, 1)[1]
        self.header, body = section.split('Proof.', 1)
        self.entry, self.post = self.header.split('  exists Mg,', 1)
        self.body = body.split('Qed.', 1)[0]
        self.probe = (ROOT / 'audit/probes/V293TaskPrioEntryUpdateProbe.v').read_text()

    def test_append_only_and_other_sources_protected_unchanged(self):
        base = json.loads((LOG / 'baseline.json').read_text())
        self.assertEqual(len(base['sources']), 165)
        self.assertEqual(len(base['protected']), 8)
        for path, sha in {**base['sources'], **base['protected']}.items():
            if path not in [GATE.CODE, GATE.PROOF]:
                self.assertEqual(hashlib.sha256((ROOT / path).read_bytes()).hexdigest(), sha, path)
        for path in [GATE.CODE, GATE.PROOF]:
            self.assertTrue((ROOT / path).read_bytes().startswith((LOG / (Path(path).name + '.before.txt')).read_bytes()))

    def test_same_configured_function_identity(self):
        identity = json.loads((LOG / 'configured-function-identity.json').read_text())
        self.assertEqual(identity['preprocessed_definition_sha256'], 'c29b633e71cf54c2d244eb87c7a5910a1f2973e6cd23d7a23769070b24bc2dbf')
        for part in ['entry', 'reserved', 'coordinate', 'event', 'tcb-update']:
            self.assertTrue(json.loads((LOG / ('configured-' + part + '-ast.json')).read_text()))

    def test_program_reuses_actual_entry_and_suffix_in_order(self):
        fragment = self.code.split('Definition V293_task_prio_entry_update', 1)[1]
        self.assertIn('sseq (V293_task_prio_entry_reserved', fragment)
        self.assertIn('(V293_task_prio_coordinates_update', fragment)
        self.assertLess(fragment.index('V293_task_prio_entry_reserved'), fragment.index('V293_task_prio_coordinates_update'))

    def test_initial_resources_not_intermediate_or_execution_oracles(self):
        for token in ['cstepstar', 'store ', 'exists Ma', 'load (Tptr V293_tcb_type) M (bc,0%Z)', 'old <> new ->']:
            self.assertNotIn(token, self.entry)
        for token in ['initial < 256 -> new < 12 ->', 'if initial =? 255 then curprio else initial',
                      'V293_bytes_writable M bc 0%Z 4 ->', '(bt,Int.repr base) <> (rb,Int.zero) ->']:
            self.assertIn(token, self.entry)
        for c in ['ny', 'bi', 'nby', 'nbx']:
            self.assertNotIn('load Tint8 M (' + c + ',', self.entry)

    def test_actual_continuation_and_derived_inequality(self):
        self.assertIn('V293_task_prio_entry_reserved_execution P\n    (kseq (V293_task_prio_coordinates_update', self.body)
        self.assertIn('Ma & Different & Entry', self.body)
        self.assertIn('V293_task_prio_coordinates_update_execution P ks ge le Ma', self.body)
        self.assertIn('exact Entry', self.body)
        self.assertIn('exact Exec', self.body)

    def test_resource_transport_and_original_memory_frame(self):
        for token in ['apply V293_load_block_frame', 'apply EntryFrame', 'rewrite LF', 'rewrite CF',
                      'Aold Anew Pointer AWo AWn', 'rewrite Untouched', 'rewrite Frame']:
            self.assertIn(token, self.body)
        self.assertIn('forall c i, c <> bo -> c <> bc ->', self.post)
        self.assertIn('get Mh (bt,i) = get M (bt,i)', self.post)
        self.assertIn('get Mh (c,i) = get M (c,i)', self.post)

    def test_direct_fixture_witness_and_single_selector_delta(self):
        witness = self.proof.split('Theorem V293_task_prio_entry_update_witness :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('V293_task_prio_entry_update_execution P ks', witness)
        self.assertIn('(40%positive,0%Z) = Some Vnull', witness)
        self.assertIn('Some (V293_byteval 255)', witness)
        self.assertIn('V293_entry_update_fixture_selector_only', self.proof)
        self.assertNotIn('V293_generic_coordinate_update_witness', witness)
        self.assertNotIn('V293_coordinate_fixture_restore', witness)

    def test_three_independent_literal_roots(self):
        self.assertEqual(self.probe.count('Print Assumptions checked_'), 3)
        for root in ['V293_task_prio_entry_update_execution', 'V293_entry_update_fixture_selector_only', 'V293_task_prio_entry_update_witness']:
            self.assertIn(':= ' + root + '.', self.probe)
        for alias in ['V293_tcb_type', 'V293_task_prio_entry_update ', 'V293_entry_update_fixture_mem',
                      'V293_entry_update_fixture_ge', 'V293_bytes_writable', 'V293_tcb_updated_loads']:
            self.assertNotIn(alias, self.probe)
        writer = (LOG / 'write-literal-probe.py').read_text()
        self.assertNotIn('certiucos/v293/proofs', writer)
        self.assertIn('checked_combined_mem', self.probe)

    def test_four_single_header_controls_preserve_proof_suffix(self):
        controls = GATE.mutations(self.proof, entry_update=True)
        self.assertEqual(len(controls), 4)
        for label, (candidate, decl) in controls.items():
            a = self.proof.index(decl)
            b = self.proof.index('Proof.', a)
            c = candidate.index('Proof.', a)
            self.assertEqual(decl, NAME)
            self.assertEqual(self.proof[:a], candidate[:a], label)
            self.assertEqual(self.proof[b:], candidate[c:], label)
            self.assertNotEqual(self.proof[a:b], candidate[a:c], label)
        gate = (ROOT / 'scripts/check-v293-task-prio-rekey.py').read_text()
        self.assertIn('if entry or reserved or entry_update:', gate)
        self.assertIn("control['line'] > proof_line", gate)

    def test_all_actual_assumptions_prints_required(self):
        self.assertEqual(GATE.checked_assumptions('Closed under the global context\n' * 3, 3), [])
        for output in ['Closed under the global context\n' * 2, 'Axioms:\nInjected : False\n' * 3]:
            with self.assertRaises(ValueError):
                GATE.checked_assumptions(output, 3)


if __name__ == '__main__':
    unittest.main()
