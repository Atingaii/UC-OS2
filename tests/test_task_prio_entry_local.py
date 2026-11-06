"""Static entry scope/contracts; actual Coq checking is --entry."""
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage26-task-prio-entry'
spec = importlib.util.spec_from_file_location('entry_gate', ROOT / 'scripts/check-v293-task-prio-rekey.py')
GATE = importlib.util.module_from_spec(spec)
spec.loader.exec_module(GATE)
NAME = 'Theorem V293_task_prio_entry_lookup_execution :'


class EntryLocalTests(unittest.TestCase):
    def setUp(self):
        self.proof = (ROOT / GATE.PROOF).read_text()
        self.code = (ROOT / GATE.CODE).read_text()
        self.header = self.proof.split(NAME, 1)[1].split('Proof.', 1)[0]
        self.entry, self.post = self.header.split('  exists Mf,', 1)
        self.body = self.proof.split(NAME, 1)[1].split('Proof.', 1)[1].split('Qed.', 1)[0]
        self.probe = (ROOT / 'audit/probes/V293TaskPrioEntryProbe.v').read_text()

    def test_append_only_two_sources_others_and_protected_unchanged(self):
        base = json.loads((LOG / 'baseline.json').read_text())
        for path, sha in {**base['sources'], **base['protected']}.items():
            if path not in [GATE.CODE, GATE.PROOF]:
                self.assertEqual(hashlib.sha256((ROOT / path).read_bytes()).hexdigest(), sha, path)
        for path in [GATE.CODE, GATE.PROOF]:
            self.assertTrue((ROOT / path).read_bytes().startswith((LOG / (Path(path).name + '.before.txt')).read_bytes()))

    def test_real_c_identity_and_entry_ast(self):
        identity = json.loads((LOG / 'configured-function-identity.json').read_text())
        self.assertEqual(identity['preprocessed_definition_sha256'], 'c29b633e71cf54c2d244eb87c7a5910a1f2973e6cd23d7a23769070b24bc2dbf')
        ast = json.loads((LOG / 'configured-entry-ast.json').read_text())
        self.assertEqual(ast['name'], 'OSTaskChangePrio')
        def walk(node):
            yield node
            for child in node.get('inner', []):
                yield from walk(child)
        nodes = list(walk(ast))
        literals = {n.get('value') for n in nodes if n.get('kind') == 'IntegerLiteral'}
        self.assertTrue({'12', '255', '42', '40', '41', '67'}.issubset(literals))
        self.assertTrue(any(n.get('kind') == 'MemberExpr' and n.get('name') == 'OSTCBPrio' for n in nodes))
        source = (LOG / 'source-lines-60-108.txt').read_text()
        self.assertIn('100:     ptcb = OSTCBPrioTbl[oldprio];', source)
        self.assertIn('105:     if (ptcb == OS_TCB_RESERVED)', source)

    def test_api_bounds_return_cursor_and_real_exit_argument(self):
        self.assertIn('old < 256 -> new < 256 ->', self.proof)
        self.assertIn('old < 12 \/ old = 255', self.proof)
        self.assertIn('new < 12', self.entry)
        self.assertIn('resolved < 13', self.entry)
        self.assertIn('kret (kseq', self.proof)
        self.assertIn('scall exit_id (evar cpu_sr :: nil)', self.code)
        self.assertNotIn('scall exit_id nil', self.code)

    def test_generic_entry_has_no_preloaded_ptcb_or_execution_oracle(self):
        self.assertNotIn('load (Tptr V293_tcb_type) M (bc,0%Z)', self.entry)
        for token in ['cstepstar', 'store ', 'exists Mf', 'resolved <> new']:
            self.assertNotIn(token, self.entry)
        self.assertIn('load (Tptr V293_tcb_type) M (b,(4*Z.of_nat resolved)%Z)', self.entry)
        self.assertIn('V293_bytes_writable M bc 0%Z 4 ->', self.entry)
        self.assertIn('old = 255 ->', self.entry)
        self.assertNotIn('8 6', self.header)

    def test_actual_current_read_store_frame_and_derived_distinction(self):
        for token in ['V293_entry_current_prio_eval', 'V293_coordinate_local_assignment',
                      'V293_storebytes_exists', 'V293_assign_pointer_execution',
                      'V293_rekey_sequence_execution', 'intro E. rewrite E in Slot',
                      'assert (SF :', 'assert (PF :']:
            self.assertIn(token, self.body)
        self.assertIn('load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr next)', self.post)
        self.assertIn('c <> bo -> c <> bc ->', self.post)

    def test_both_selectors_same_fixture_and_initial_pointer_null(self):
        witness = self.proof.split('Theorem V293_task_prio_entry_witness :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('forall self P ks', witness)
        self.assertIn('V293_task_prio_entry_lookup_execution P ks', witness)
        self.assertIn('V293_task_prio_argument_accepts', witness)
        self.assertIn('(V293_entry_fixture_mem self) (40%positive,0%Z) = Some Vnull', witness)
        self.assertIn('Lemma V293_entry_fixture_delta', self.proof)
        self.assertIn('(c,i) <> (51%positive,0%Z)', self.proof)

    def test_three_handwritten_literal_roots(self):
        self.assertEqual(self.probe.count('Print Assumptions checked_'), 3)
        for root in ['argument_execution', 'entry_lookup_execution', 'entry_witness']:
            self.assertIn(':= V293_task_prio_' + root + '.', self.probe)
        for alias in ['V293_tcb_type', 'V293_task_prio_entry_lookup ', 'V293_entry_fixture_mem',
                      'V293_bytes_writable', 'V293_argument_stop', 'V293_prefix_fixture_entries']:
            self.assertNotIn(alias, self.probe)
        self.assertIn('Definition checked_lookup', self.probe)
        self.assertIn('Definition checked_memory', self.probe)

    def test_four_prospective_single_header_controls(self):
        cases = GATE.mutations(self.proof, entry=True)
        self.assertEqual(len(cases), 4)
        for label, (candidate, decl) in cases.items():
            a = self.proof.index(decl)
            b = self.proof.index('Proof.', a)
            c = candidate.index('Proof.', a)
            self.assertEqual(self.proof[:a], candidate[:a], label)
            self.assertEqual(self.proof[b:], candidate[c:], label)
            self.assertNotEqual(self.proof[a:b], candidate[a:c], label)
            self.assertEqual(decl, NAME)

    def test_skip_control_keeps_unused_parameter_types_and_rejects_in_proof(self):
        self.assertIn('(cpu_sr : var) (exit_id : fid)', self.header)
        candidate, _ = GATE.mutations(self.proof, entry=True)['entry-program-claimed-skip-only']
        candidate_header = candidate.split(NAME, 1)[1].split('Proof.', 1)[0]
        self.assertIn('(cpu_sr : var) (exit_id : fid)', candidate_header)
        self.assertIn("control['line'] > proof_line", (ROOT / 'scripts/check-v293-task-prio-rekey.py').read_text())

    def test_requires_all_actual_assumption_prints(self):
        self.assertEqual(GATE.checked_assumptions('Closed under the global context\n' * 3, 3), [])
        for output in ['Closed under the global context\n' * 2, 'Axioms:\nInjected : False\n' * 3]:
            with self.assertRaises(ValueError):
                GATE.checked_assumptions(output, 3)


if __name__ == '__main__':
    unittest.main()
