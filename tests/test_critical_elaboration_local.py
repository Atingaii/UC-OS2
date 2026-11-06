"""Narrow mapping/interface checks; actual proof validity is checked by Coq gate."""
import hashlib
import importlib.util
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT/'certiucos/v293/proofs/V293CriticalReturn.v'
LOG = ROOT/'audit/logs/stage26-critical-elaboration'


def gate():
    spec = importlib.util.spec_from_file_location('elaboration', ROOT/'scripts/check-v293-critical-elaboration.py')
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def header(name):
    return SOURCE.read_text().split('Theorem '+name+' :', 1)[1].split('Proof.', 1)[0]


class CriticalElaborationTests(unittest.TestCase):
    def test_original_raw_model_and_missing_port_fact_preserved(self):
        old = (LOG/'original-critical-return.v.snapshot.txt').read_bytes()
        self.assertEqual(hashlib.sha256(old).hexdigest(), 'ac153d62802324b65df0008a8df26a7780b9124a0274255d056f5cc2211ec5ad')
        self.assertTrue(SOURCE.read_bytes().startswith(old))
        h = header('V293_missing_port_has_no_step')
        self.assertIn('P exit_id = None ->', h)
        self.assertIn('sfexec exit_id args types', h)
        bare = re.sub(r'\(\*.*?\*\)', '', SOURCE.read_text(), flags=re.S)
        self.assertIsNone(re.search(r'\b(?:Inductive|Axiom|Parameter|Conjecture|Admitted|admit)\b', bare))

    def test_explicit_normalizer_rejects_unsupported_runtime_syntax(self):
        text = SOURCE.read_text().split('Fixpoint V293_port_calls ', 1)[1].split('Theorem ', 1)[0]
        self.assertIn('| sfexec _ _ _ | salloc _ _ | sfree _ _ => None', text)
        self.assertIn('if Z.eq_dec enter exit then None', text)
        self.assertEqual(text.count('| eaddrof (evar x) :: nil =>'), 2)
        reject = header('V293_port_rejects_wrong_token')
        for case in ['eaddrof (evar other)', '(evar saved::nil)', 'enter enter saved']:
            self.assertIn(case, reject)
        self.assertEqual(reject.count('= None'), 3)

    def test_occupied_root_has_no_execution_or_saved_memory_oracle(self):
        h = header('V293_occupied_critical_return')
        pre = h.split('exists Mf,', 1)[0]
        for forbidden in ['cstepstar', 'loststep', 'V293_local_steps', 'V293_saved_ie', 'store ', 'free ']:
            self.assertNotIn(forbidden, pre)
        self.assertIn('NoDup (map fst (getaddr le))', pre)
        self.assertIn('V293_bytes_writable M c 0%Z (typelen t)', pre)
        self.assertIn('V293_primitive_critical_prefix', h)
        self.assertIn('(ge,caller,Mf),ir,(enabled,si,ci)', h)
        self.assertIn('get Mf (c,Z.of_nat k) = None', h)
        self.assertNotIn('V293_raw_critical_prefix', h)

    def test_closure_reuses_original_loststep(self):
        text = SOURCE.read_text().split('Definition V293_local_steps ', 1)[1].split('Lemma ', 1)[0]
        self.assertIn('clos_refl_trans_1n (code * taskst)', text)
        self.assertIn('loststep P (fst a) (snd a) (fst b) (snd b)', text)
        proof = SOURCE.read_text().split('Theorem V293_occupied_critical_return :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('apply encrit_step', proof)
        self.assertIn('apply excrit_step', proof)
        self.assertIn('V293_task_prio_argument_accepts', proof)
        self.assertIn('V293_error_return_execution', proof)

    def test_nonvacuity_both_states_same_program_and_ignored_suffix(self):
        h = header('V293_occupied_critical_witness')
        self.assertIn('forall P self enabled ir,', h)
        self.assertIn('scall 999%Z nil', h)
        self.assertNotIn('P 999', h)
        self.assertEqual(h.count('(enabled,nil,nil)'), 2)
        text = SOURCE.read_text().split('Definition V293_critical_fixture_mem ', 1)[1].split('Theorem ', 1)[0]
        self.assertIn('(Int.repr 23)', text)
        self.assertNotIn('enabled', text)
        self.assertIn('k < 4 -> get Mf (61%positive,Z.of_nat k) = None', h)
        self.assertIn('get Mf (52%positive,0%Z) = None', h)
        self.assertIn('Some (Vptr (90%positive,Int.zero))', h)

    def test_control_projections_and_suffixes(self):
        g = gate()
        source = SOURCE.read_text()
        normal, occupied = g.projections(source)
        self.assertNotIn('Theorem '+g.NORMAL, occupied)
        self.assertIn('Theorem '+g.OCCUPIED, occupied)
        self.assertTrue(normal.rstrip().endswith('Qed.'))
        self.assertTrue(occupied.rstrip().endswith('Qed.'))
        cases = g.controls(source)
        self.assertEqual([x[0] for x in cases], ['ExitSti', 'EnterCli', 'WrongReturn', 'ValueArgument'])
        for label, changed, root, positive in cases:
            i = positive.index('Proof.', positive.index('Theorem '+root+' :'))
            j = changed.index('Proof.', changed.index('Theorem '+root+' :'))
            self.assertEqual(positive[i:], changed[j:], label)
            self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn', changed)
        self.assertIn('sseq (sprim sti) (srete (econst32 (Int.repr error)))', cases[0][1])
        self.assertIn('(sseq (sprim cli) (V293_primitive_entry', cases[1][1])
        self.assertIn('(Int.repr 41)', cases[2][1].split('Theorem '+g.OCCUPIED)[1].split('Proof.')[0])
        self.assertEqual(cases[3][1].count('| evar x :: nil =>'), 2)

    def test_handwritten_probe_not_rewritten_by_gate(self):
        text = (ROOT/'audit/probes/V293CriticalElaborationProbe.v').read_text()
        for name in ['checked_normalize', 'checked_reject', 'checked_occupied', 'checked_physical', 'checked_disabled', 'checked_raw_missing']:
            self.assertRegex(text, r'Definition '+name+r'\s*:\s*(?:\n\s*)?forall')
        self.assertEqual(text.count('Print Assumptions '), 6)
        literal = text.split('Definition expected_critical_prefix ', 1)[1].split('Definition checked_normalize', 1)[0]
        self.assertNotIn('V293_primitive_', literal)
        self.assertEqual(literal.count('sprim excrit'), 3)
        script = (ROOT/'scripts/check-v293-critical-elaboration.py').read_text()
        self.assertNotIn('(ROOT/PROBE).write_text', script)
        self.assertIn("int(match[1]) > entry['target_proof_line']", script)
        self.assertIn("'downstream_credit': False", script)

    def test_saved_use_shape_rejects_extra_read_and_value_argument(self):
        g = gate()
        def walk(node):
            yield node
            for child in node.get('inner', []):
                yield from walk(child)
        def ref(i):
            return {'kind': 'DeclRefExpr', 'id': str(i), 'referencedDecl': {'id': 'saved', 'name': 'cpu_sr'}}
        decl = {'kind': 'VarDecl', 'id': 'saved', 'name': 'cpu_sr', 'type': {'desugaredQualType': 'unsigned int'},
                'inner': [{'kind': 'IntegerLiteral', 'value': '0'}]}
        calls = []
        for i, name in enumerate(['V293_EnterCritical']+['V293_ExitCritical']*4):
            calls.append({'kind': 'CallExpr', 'inner': [
                {'kind': 'DeclRefExpr', 'referencedDecl': {'name': name}},
                {'kind': 'UnaryOperator', 'opcode': '&', 'type': {'qualType': 'OS_CPU_SR *'}, 'inner': [ref(i)]}]})
        fn = {'inner': [decl]+calls}
        self.assertEqual(g.check_saved_uses(fn, walk)['use_count'], 5)
        with self.assertRaises(AssertionError):
            g.check_saved_uses({'inner': [decl]+calls+[ref(99)]}, walk)
        calls[0]['inner'][1] = ref(0)
        with self.assertRaises(AssertionError):
            g.check_saved_uses(fn, walk)


if __name__ == '__main__':
    unittest.main()
