"""Static scope/contracts; executable semantic checks are --reserved, not these tests."""
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage26-task-prio-reserved'
spec = importlib.util.spec_from_file_location('reserved_gate', ROOT / 'scripts/check-v293-task-prio-rekey.py')
GATE = importlib.util.module_from_spec(spec)
spec.loader.exec_module(GATE)
NAME = 'Theorem V293_task_prio_entry_reserved_execution :'


class ReservedLocalTests(unittest.TestCase):
    def setUp(self):
        self.proof = (ROOT / GATE.PROOF).read_text()
        self.code = (ROOT / GATE.CODE).read_text()
        self.header = self.proof.split(NAME, 1)[1].split('Proof.', 1)[0]
        self.entry, self.post = self.header.split('  exists Mf,', 1)
        self.body = self.proof.split(NAME, 1)[1].split('Proof.', 1)[1].split('Qed.', 1)[0]
        self.probe = (ROOT / 'audit/probes/V293TaskPrioReservedProbe.v').read_text()

    def test_append_only_other_sources_and_protected_unchanged(self):
        base = json.loads((LOG / 'baseline.json').read_text())
        self.assertEqual(len(base['sources']), 165)
        self.assertEqual(len(base['protected']), 8)
        for path, sha in {**base['sources'], **base['protected']}.items():
            if path not in [GATE.CODE, GATE.PROOF]:
                self.assertEqual(hashlib.sha256((ROOT / path).read_bytes()).hexdigest(), sha, path)
        for path in [GATE.CODE, GATE.PROOF]:
            self.assertTrue((ROOT / path).read_bytes().startswith((LOG / (Path(path).name + '.before.txt')).read_bytes()))

    def test_frozen_c_cast_guard_and_all_source_occurrences(self):
        identity = json.loads((LOG / 'configured-function-identity.json').read_text())
        self.assertEqual(identity['preprocessed_definition_sha256'], 'c29b633e71cf54c2d244eb87c7a5910a1f2973e6cd23d7a23769070b24bc2dbf')
        def walk(node):
            yield node
            for child in node.get('inner', []):
                yield from walk(child)
        nodes = list(walk(json.loads((LOG / 'configured-reserved-ast.json').read_text())))
        self.assertTrue(any(n.get('castKind') == 'IntegralToPointer' for n in nodes))
        self.assertTrue(any(n.get('kind') == 'IntegerLiteral' and n.get('value') == '67' for n in nodes))
        occurrences = json.loads((LOG / 'reserved-source-occurrences.json').read_text())
        self.assertEqual(len(occurrences), 16)
        self.assertTrue(any('#define' in n['text'] for n in occurrences))
        self.assertIn('105:     if (ptcb == OS_TCB_RESERVED)', (LOG / 'source-lines-60-108.txt').read_text())

    def test_symbol_address_is_static_not_mutable_load_or_integer_cast(self):
        expr = self.code.split('Definition V293_task_prio_reserved_expr', 1)[1].split('Definition ', 1)[0]
        self.assertIn('ecast (eaddrof (evar reserved)) (Tptr V293_tcb_type)', expr)
        self.assertNotIn('econst32', expr)
        symbol = self.proof.split('Lemma V293_reserved_symbol_eval :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('forall ge le M reserved br', symbol)
        self.assertNotIn('load ', symbol)
        self.assertIn('get le reserved = None', symbol)
        self.assertIn('get ge reserved = Some (br,Tint8)', symbol)
        self.assertIn('evaltype=None', (ROOT / 'docs/adr/0004-保留指针采用显式符号地址.md').read_text())

    def test_generic_entry_exposes_noncollision_without_execution_oracle(self):
        for token in ['get le reserved = None ->', 'get ge reserved = Some (br,Tint8) ->',
                      'next <> (br,Int.zero) ->', 'V293_bytes_writable M bc 0%Z 4 ->']:
            self.assertIn(token, self.entry)
        for token in ['cstepstar', 'store ', 'load (Tptr V293_tcb_type) M (bc,0%Z)', '8 6']:
            self.assertNotIn(token, self.entry)
        self.assertIn('load (Tptr V293_tcb_type) Mf (bc,0%Z) = Some (Vptr next)', self.post)

    def test_real_two_choices_stop_before_error_call(self):
        select = self.proof.split('Theorem V293_task_prio_reserved_select :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('if V293_reserved_matches br value', select)
        self.assertIn('then V293_task_prio_reserved_error cpu_sr exit_id else sskip None', select)
        error = self.code.split('Definition V293_task_prio_reserved_error', 1)[1].split('Definition ', 1)[0]
        self.assertIn('scall exit_id (evar cpu_sr :: nil)', error)
        self.assertIn('srete (econst32 (Int.repr 67))', error)
        self.assertNotIn('kret', select)

    def test_real_continuation_composition_and_frame(self):
        self.assertIn('V293_task_prio_entry_lookup_execution P (kseq (V293_task_prio_reserved_guard', self.body)
        self.assertIn('V293_task_prio_reserved_accepts', self.body)
        self.assertIn('exact Lookup', self.body)
        self.assertIn('exact Post', self.body)
        self.assertIn('c <> bo -> c <> bc ->', self.post)

    def test_both_selectors_reuse_same_physical_memory(self):
        witness = self.proof.split('Theorem V293_task_prio_reserved_witness :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('forall self P ks', witness)
        self.assertIn('V293_task_prio_entry_reserved_execution P ks', witness)
        self.assertIn('(V293_entry_fixture_mem self) (40%positive,0%Z) = Some Vnull', witness)
        self.assertIn('Definition V293_reserved_fixture_ge : env :=\n  set V293_entry_fixture_ge 900%Z (99%positive,Tint8).', self.proof)
        self.assertNotIn('Definition V293_reserved_fixture_mem', self.proof)

    def test_six_independent_literal_roots(self):
        self.assertEqual(self.probe.count('Print Assumptions checked_'), 6)
        for root in ['V293_reserved_symbol_eval', 'V293_reserved_three_way_equality',
                     'V293_task_prio_reserved_select', 'V293_task_prio_entry_reserved_execution',
                     'V293_reserved_noncollision_needed', 'V293_task_prio_reserved_witness']:
            self.assertIn(':= ' + root + '.', self.probe)
        for alias in ['V293_tcb_type', 'V293_task_prio_entry_reserved ', 'V293_entry_fixture_mem',
                      'V293_bytes_writable', 'V293_reserved_fixture_ge', 'V293_reserved_matches ']:
            self.assertNotIn(alias, self.probe)
        self.assertIn('Definition checked_program', self.probe)
        self.assertIn('Definition checked_memory', self.probe)

    def test_four_header_only_controls_and_typed_unused_arguments(self):
        controls = GATE.mutations(self.proof, reserved=True)
        self.assertEqual(len(controls), 4)
        self.assertIn('(cpu_sr : var) (exit_id : fid)', self.header)
        for label, (candidate, decl) in controls.items():
            a = self.proof.index(decl)
            b = self.proof.index('Proof.', a)
            c = candidate.index('Proof.', a)
            self.assertEqual(decl, NAME)
            self.assertEqual(self.proof[:a], candidate[:a], label)
            self.assertEqual(self.proof[b:], candidate[c:], label)
            self.assertNotEqual(self.proof[a:b], candidate[a:c], label)
        gate = (ROOT / 'scripts/check-v293-task-prio-rekey.py').read_text()
        self.assertIn('if entry or reserved:', gate)
        self.assertIn("control['line'] > proof_line", gate)

    def test_actual_assumptions_require_all_six_prints(self):
        self.assertEqual(GATE.checked_assumptions('Closed under the global context\n' * 6, 6), [])
        for output in ['Closed under the global context\n' * 5, 'Axioms:\nInjected : False\n' * 6]:
            with self.assertRaises(ValueError):
                GATE.checked_assumptions(output, 6)


if __name__ == '__main__':
    unittest.main()
