"""Check audit provenance as well as the actual Coq gate, without inventing proof credit."""
import ast
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT/'audit/logs/stage26-ready-owned-transition'
SOURCE = ROOT/'certiucos/v293/proofs/V293CriticalReturn.v'


def gate():
    spec = importlib.util.spec_from_file_location('owned_gate', ROOT/'scripts/check-v293-ready-owned.py')
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def result():
    return json.loads((LOG/'gate01/result.json').read_text())


def declaration(name):
    return gate().declaration(SOURCE.read_text(), name)


class ReadyOwnedLocalTests(unittest.TestCase):
    def test_previous_4586_line_source_is_exact_prefix(self):
        old = (LOG/'V293CriticalReturn.v.before.snapshot.txt').read_bytes()
        self.assertEqual(len(old), gate().PREFIX_BYTES)
        self.assertEqual(hashlib.sha256(old).hexdigest(), gate().PREFIX_SHA)
        self.assertTrue(SOURCE.read_bytes().startswith(old))
        self.assertEqual(len(old.splitlines()), 4586)

    def test_no_active_source_count_inflation(self):
        baseline = json.loads((LOG/'baseline.json').read_text())
        current = {str(p.relative_to(ROOT)) for d in ['framework','tactics','certiucos/v293']
                   for p in (ROOT/d).rglob('*.v')}
        self.assertEqual(current, set(baseline['active']))
        changed = [p for p,h in baseline['active'].items()
                   if hashlib.sha256((ROOT/p).read_bytes()).hexdigest() != h]
        self.assertEqual(changed, [gate().SOURCE])

    def test_ready_primitive_requires_actual_entry_and_free_new_priority(self):
        suffix = SOURCE.read_bytes()[gate().PREFIX_BYTES:].decode()
        definition = suffix[suffix.index('Definition V293_ready_prio_step'):suffix.index('Lemma V293_ready_prio_eqdom')]
        for item in ['old < 13', 'new < 12', 'get O abstcblsid', 'get tasks next',
                     'forall t status msg', 'set O abstcblsid', 'set tasks next', 'Some (Vint32 Int.zero)']:
            self.assertIn(item, definition)
        self.assertNotIn('V293_highest_ready', definition)

    def test_owned_step_is_framed_and_constructed_not_assumed(self):
        text = declaration(gate().OWNED)
        header, proof = text.split('Proof.', 1)
        self.assertNotIn('spec_step', header.split('exists O\' OO\'',1)[0])
        for item in ['V293_shared_fields current tasks events now ** R', 'join O Of OO', 'join O\' Of OO\'']:
            self.assertIn(item, header)
        for item in ['eapply spec_prim_step', 'V293_ready_prio_eqdom', 'OSAbstMod.join_set_l',
                     'V293_ready_prio_shared_fields', 'V293_shared_fields_get']:
            self.assertIn(item, proof)

    def test_real_branch_is_derived_from_entry_map(self):
        text = declaration(gate().BRANCH)
        for item in ['V293_ready_test_from_task', 'V293_rekey_ready_tasks_preserved',
                     'V293_rekey_task_table_preserved']:
            self.assertIn(item, text)
        self.assertIn('V293_ready_branch_rows lo hi old new', text)
        self.assertNotIn('V293_ready_test_flag lo hi old = true ->', text)

    def test_same_final_heap_has_full_trace_and_owned_table(self):
        text = declaration(gate().COMPLETE)
        header, proof = text.split('Proof.',1)
        for item in ['V293_local_steps V293_success_tail_fixture_program', 'V293_tcb_updated_loads Mf',
                     'V293_rekey_bitmap_loads Mf', 'V293_table_loads V293_tcb_type Mf',
                     'get Mf (c,Z.of_nat k) = None', 'get O\' abstcblsid',
                     '(V293_complete_fixture_ge,emp,Mf,ir,(enabled,si,ci),OO\',op)',
                     'V293_bitmap_tasks 80 0 tasks\'', 'V293_priority_table entries\' tasks\'']:
            self.assertIn(item, header)
        for item in ['V293_critical_null_success_return_witness', 'V293_ready_prio_owned_step',
                     'V293_ready_prio_branch_relations', 'V293_ready_selection_task',
                     'V293_shared_fields_heap_lift', 'V293_shared_fields_rebase']:
            self.assertIn(item, proof)
        self.assertNotIn('V293_local_steps', header.split('exists Mf O\' OO\'',1)[0])

    def test_semantic_counterexamples_are_kernel_propositions(self):
        for name, statement in [('V293_ready_prio_stale_bitmap_rejected', '~ V293_bitmap_tasks 80 0'),
                                ('V293_ready_prio_moving_not_highest', '~ V293_highest_ready')]:
            text = declaration(name)
            self.assertIn(statement, text)
            self.assertTrue(text.rstrip().endswith('Qed.'))
        self.assertIn('change (6 <= 4)%Z in Minimal', declaration('V293_ready_prio_moving_not_highest'))

    def test_fixed_literal_probe_and_nonvacuity(self):
        probe = (ROOT/gate().PROBE).read_text()
        for item in ['Definition expected_ready_step', 'Definition expected_owned_tasks',
                     'Definition expected_owned_post', 'expected_entry_trace false',
                     'Theorem expected_owned_nonvacuity', 'apply V293_shared_fixture_fields']:
            self.assertIn(item, probe)
        self.assertNotIn('(ROOT/PROBE).write_text', (ROOT/'scripts/check-v293-ready-owned.py').read_text())

    def test_gate_really_passed_fifteen_tool_checks(self):
        r = result()
        self.assertTrue(r['passed'])
        self.assertTrue(r['inputs_unchanged'])
        self.assertTrue(r['temporary_tree_removed'])
        self.assertEqual(len(r['checks']), 15)
        for k,v in r['checks'].items():
            self.assertEqual(v['exit_code'], 1 if k.startswith('negative-') else 0)

    def test_current_inputs_match_checked_identity(self):
        for p,h in result()['inputs'].items():
            self.assertEqual(hashlib.sha256((ROOT/p).read_bytes()).hexdigest(), h, p)

    def test_positives_do_not_import_candidate_production(self):
        for name in ['PositiveRoots','PositiveOwned','PositiveBranch','PositiveComplete']:
            text = (LOG/('gate01/'+name+'.v.snapshot.txt')).read_text()
            self.assertIn('Require Import ReadyOwnedGate.FrozenPrefix.', text)
            self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.',text)

    def test_single_factor_controls_preserve_entire_target_proof(self):
        controls = gate().controls(SOURCE.read_text())
        self.assertEqual({x[0] for x in controls}, {'NoAbstractWrite','ReadyNotUpdated','TableNotUpdated'})
        protocol = {x['label']:x for x in json.loads((LOG/'gate01/control-protocol.json').read_text())}
        for label,target,changed,original,_ in controls:
            i = changed.index('Proof.', changed.index('Theorem '+target+' :'))
            j = original.index('Proof.', original.index('Theorem '+target+' :'))
            self.assertEqual(changed[i:], original[j:])
            self.assertEqual(hashlib.sha256(changed.encode()).hexdigest(), protocol[label]['sha256'])
            self.assertGreater(result()['checks']['negative-'+label]['error_line'], protocol[label]['target_proof_line'])
            self.assertFalse(protocol[label]['downstream_credit'])

    def test_checked_assumptions_and_no_new_axioms(self):
        r=result(); allowed={'Classical_Prop.classic','FunctionalExtensionality.functional_extensionality_dep'}
        for names in [r['probe_assumptions'], *r['positive_assumptions'].values()]:
            self.assertLessEqual(set(names),allowed)
        suffix = SOURCE.read_bytes()[gate().PREFIX_BYTES:].decode()
        bare=re.sub(r'\(\*.*?\*\)','',suffix,flags=re.S)
        self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|vm_compute)\b',bare))

    def test_old_assertions_retained_and_gates_actually_replayed(self):
        def assertions(text):
            return [ast.dump(n,include_attributes=False) for n in ast.walk(ast.parse(text))
                    if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr.startswith('assert')]
        for f in ['test_success_entry_witness_local.py','test_success_complete_return_local.py']:
            self.assertEqual(assertions((LOG/(f+'.before.snapshot.txt')).read_text()),
                             assertions((ROOT/'tests'/f).read_text()))
        for f,count in [('replayed-entry/gate02/result.json',13),
                        ('replayed-entry/complete-return-replay/gate02/result.json',17)]:
            r=json.loads((LOG/f).read_text())
            self.assertTrue(r['passed'])
            self.assertEqual(len(r['checks']),count)
            for p,h in r['inputs'].items():
                self.assertEqual(hashlib.sha256((ROOT/p).read_bytes()).hexdigest(),h,p)


if __name__ == '__main__':
    unittest.main()
