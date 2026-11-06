"""Static regression; --entry-null performs actual Coq checks and controls."""
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage26-task-prio-entry-null'
spec = importlib.util.spec_from_file_location('entry_null_gate', ROOT / 'scripts/check-v293-task-prio-rekey.py')
GATE = importlib.util.module_from_spec(spec)
spec.loader.exec_module(GATE)
NAME = 'Theorem V293_task_prio_entry_null_update_execution :'


class EntryNullTests(unittest.TestCase):
    def setUp(self):
        self.proof = (ROOT / GATE.PROOF).read_text()
        self.code = (ROOT / GATE.CODE).read_text()
        self.header, body = self.proof.split(NAME, 1)[1].split('Proof.', 1)
        self.pre, self.post = self.header.split('  exists Mg,', 1)
        self.body = body.split('Qed.', 1)[0]
        self.probe = (ROOT / 'audit/probes/V293TaskPrioEntryNullProbe.v').read_text()

    def test_only_proof_appended_program_and_other_sources_unchanged(self):
        base = json.loads((LOG / 'baseline.json').read_text())
        self.assertEqual(len(base['sources']), 165)
        self.assertEqual(len(base['protected']), 8)
        for path, h in {**base['sources'], **base['protected']}.items():
            if path != GATE.PROOF:
                self.assertEqual(hashlib.sha256((ROOT / path).read_bytes()).hexdigest(), h, path)
        self.assertTrue((ROOT / GATE.PROOF).read_bytes().startswith((LOG / 'V293TaskPrioRekey.v.before.txt').read_bytes()))

    def test_actual_source_still_has_independent_event_if(self):
        ident = json.loads((LOG / 'configured-function-identity.json').read_text())
        self.assertEqual(ident['preprocessed_definition_sha256'], 'c29b633e71cf54c2d244eb87c7a5910a1f2973e6cd23d7a23769070b24bc2dbf')
        ast = json.loads((LOG / 'configured-event-ast.json').read_text())
        self.assertEqual(ast['independent_if']['inner'][0]['opcode'], '!=')
        self.assertIn('sifthen (V293_task_prio_event_test pevent)', self.code)

    def test_raw_entry_no_correct_locals_execution_or_store_oracle(self):
        for token in ['cstepstar', 'store ', 'exists Ma', 'load (Tptr V293_tcb_type) M (bc,0%Z)', 'old <> new ->']:
            self.assertNotIn(token, self.pre)
        for c in ['ny', 'bi', 'nby', 'nbx']:
            self.assertNotIn('load Tint8 M (' + c + ',', self.pre)
        self.assertIn('initial < 256 -> new < 12 ->', self.pre)
        self.assertIn('if initial =? 255 then curprio else initial', self.pre)

    def test_null_does_not_require_fictitious_event_object(self):
        self.assertIn('load (Tcom_ptr 411%Z) M (bt,(base+28)%Z) = Some Vnull ->', self.pre)
        for token in ['be ebase', 'V293_event_bitmap_loads', 'V293_event_bitmap_writable', 'c <> be']:
            self.assertNotIn(token, self.header)
        self.assertIn('load (Tptr V293_event_type) Mh (bp,0%Z) = Some Vnull', self.post)
        self.assertIn('load (Tcom_ptr 411%Z) Mh (bt,(base+28)%Z) = Some Vnull', self.post)

    def test_actual_continuation_and_resource_transport(self):
        for token in ['V293_task_prio_entry_reserved_execution P\n    (kseq (V293_task_prio_coordinates_update',
                      'Ma & Different & Entry', 'V293_task_prio_coordinates_null_update_execution P ks ge le Ma',
                      'apply EntryFrame', 'rewrite LF', 'rewrite CF', 'exact Entry', 'exact Exec']:
            self.assertIn(token, self.body)
        suffix = self.proof.split('Theorem V293_task_prio_coordinates_null_update_execution :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('V293_task_prio_prefix_null_update_execution P ks ge le Mc', suffix)

    def test_frame_is_original_and_has_no_event_block_exclusion(self):
        self.assertIn('forall c i, c <> bo -> c <> bc ->', self.post)
        self.assertIn('get Mh (bt,i) = get M (bt,i)', self.post)
        self.assertIn('get Mh (c,i) = get M (c,i)', self.post)
        self.assertNotIn('c <> be', self.post)
        self.assertIn('rewrite Untouched', self.body)

    def test_direct_witness_stale_locals_and_unwritten_event_sentinel(self):
        witness = self.proof.split('Theorem V293_task_prio_entry_null_update_witness :', 1)[1].split('Qed.', 1)[0]
        for token in ['V293_task_prio_entry_null_update_execution P ks', '(40%positive,0%Z) = Some Vnull',
                      'Some (V293_byteval 255)', 'forall i, get Mh (72%positive,i)']:
            self.assertIn(token, witness)
        self.assertNotIn('V293_task_prio_entry_update_witness', witness)
        self.assertNotIn('V293_null_update_continuous_witness', witness)
        self.assertIn('c <> 41%positive \/ (i < 36)%Z \/ (40 <= i)%Z', self.proof)

    def test_three_independent_literal_roots(self):
        self.assertEqual(self.probe.count('Print Assumptions checked_'), 3)
        for root in ['V293_task_prio_entry_null_update_execution', 'V293_entry_null_fixture_outside', 'V293_task_prio_entry_null_update_witness']:
            self.assertIn(':= ' + root + '.', self.probe)
        for alias in ['V293_task_prio_entry_update ', 'V293_entry_null_fixture_mem', 'V293_tcb_type', 'V293_bytes_writable']:
            self.assertNotIn(alias, self.probe)
        writer = (LOG / 'write-literal-probe.py').read_text()
        self.assertNotIn('certiucos/v293/proofs', writer)
        self.assertIn('checked_put_bytes (checked_combined_mem', self.probe)

    def test_four_single_header_controls_and_strict_proof_gate(self):
        controls = GATE.mutations(self.proof, entry_null=True)
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
        self.assertIn('if entry or reserved or entry_update or entry_null:', gate)
        self.assertIn("control['line'] > proof_line", gate)

    def test_all_assumption_prints_required(self):
        self.assertEqual(GATE.checked_assumptions('Closed under the global context\n' * 3, 3), [])
        for s in ['Closed under the global context\n' * 2, 'Axioms:\nInjected : False\n' * 3]:
            with self.assertRaises(ValueError):
                GATE.checked_assumptions(s, 3)


if __name__ == '__main__':
    unittest.main()
