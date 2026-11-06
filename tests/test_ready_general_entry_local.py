"""Current local proof provenance; historical stale failures are not rewritten."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT/'audit/logs/stage26-ready-general-entry'


def gate():
    sp = importlib.util.spec_from_file_location('general_ready_gate', ROOT/'scripts/check-v293-ready-general-entry.py')
    g = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(g)
    return g


def result():
    return json.loads((LOG/'gate01/result.json').read_text())


def target():
    s = (ROOT/gate().SOURCE).read_text()
    return s[s.index('Theorem '+gate().TARGET+' :'):]


class ReadyGeneralEntryLocalTests(unittest.TestCase):
    def test_previous_4849_line_prefix_unchanged(self):
        g = gate()
        before = (LOG/'V293CriticalReturn.v.before.snapshot.txt').read_bytes()
        self.assertEqual(len(before), g.PREFIX_BYTES)
        self.assertEqual(hashlib.sha256(before).hexdigest(), g.PREFIX_SHA)
        self.assertEqual(len(before.splitlines()), 4849)
        self.assertTrue((ROOT/g.SOURCE).read_bytes().startswith(before))

    def test_fixed_scope_and_active_source_set(self):
        b = json.loads((LOG/'baseline.json').read_text())
        current = {str(p.relative_to(ROOT)) for d in ['framework', 'tactics', 'certiucos/v293']
                   for p in (ROOT/d).rglob('*.v')}
        self.assertEqual(set(b['active']), current)
        self.assertEqual([p for p,h in b['active'].items()
                          if hashlib.sha256((ROOT/p).read_bytes()).hexdigest() != h], [gate().SOURCE])
        for p,h in b['protected'].items():
            self.assertEqual(hashlib.sha256((ROOT/p).read_bytes()).hexdigest(), h, p)

    def test_entry_requires_no_execution_or_freshness_oracle(self):
        header = target().split('Proof.', 1)[0].split('exists Mf Os\' OO\'', 1)[0]
        for forbidden in ['V293_local_steps', 'spec_step', 'store ', 'free ', 'forall t status msg']:
            self.assertNotIn(forbidden, header)
        for required in ['forall P ks ge le caller M', 'V293_priority_table entries tasks',
                         'V293_bitmap_tasks lo hi tasks', 'get tasks (bt,Int.repr base)',
                         'V293_shared_fields abstract_current tasks events now ** R', 'join Os Of OO']:
            self.assertIn(required, header)

    def test_empty_slot_and_freshness_derived_from_same_physical_entry(self):
        proof = target().split('Proof.', 1)[1]
        for required in ['View new', 'rewrite Empty in Loaded', 'V293_rekey_task_entry',
                         'rewrite EmptyEntry in Entry', 'V293_ready_prio_owned_step',
                         'V293_ready_prio_branch_relations', 'V293_critical_null_success_return_execution']:
            self.assertIn(required, proof)
        self.assertNotIn('V293_critical_null_success_return_witness', proof)

    def test_same_final_heap_and_same_updated_task_table(self):
        header = target().split('Proof.', 1)[0]
        for required in ['V293_local_steps P', '(ge,caller,Mf)', 'V293_tcb_updated_loads Mf',
                         'V293_rekey_bitmap_loads Mf', 'V293_table_loads V293_tcb_type Mf',
                         'get Mf (c,Z.of_nat k) = None', '(ge,caller,Mf,ir,(enabled,si,ci),OO\',op)',
                         'V293_bitmap_tasks (fst fr) (snd fr)', 'V293_highest_ready',
                         'load (Tptr V293_tcb_type) Mf']:
            self.assertIn(required, header)
        self.assertNotIn('V293_ready_inv', header)
        self.assertNotIn('** R /\\', header)
        self.assertIn('** Atrue /\\', header)

    def test_transport_forgets_arbitrary_physical_frame(self):
        _, suffix, _ = gate().parts((ROOT/gate().SOURCE).read_text())
        transport = suffix[suffix.index('Lemma V293_shared_fields_owned_transport'):suffix.index('(* General original entry')]
        self.assertIn('** R ->', transport)
        self.assertIn('** Atrue.', transport)
        self.assertIn('V293_shared_fields_empty_heap', transport)
        self.assertIn('map_join_assoc JO Frame', transport)
        self.assertIn('V293_shared_fields_heap_lift', transport)

    def test_literal_probe_constructs_general_interface_entry(self):
        p = (ROOT/gate().PROBE).read_text()
        nonvac = p[p.index('Theorem expected_general_owned_nonvacuity'):]
        for required in ['expected_general_owned_contract V293_success_tail_fixture_program',
                         'V293_prefix_fixture_relations true', 'V293_shared_fixture_fields',
                         'V293_shared_fields_heap_lift', 'AllWritable', 'expected_entry_trace false']:
            self.assertIn(required, nonvac)
        self.assertNotIn('V293_critical_null_success_return_witness', nonvac)
        self.assertNotIn('V293_critical_ready_owned_success', nonvac)
        self.assertNotIn('(ROOT/PROBE).write_text', (ROOT/'scripts/check-v293-ready-general-entry.py').read_text())

    def test_actual_eleven_checks_passed_at_current_identity(self):
        r = result()
        self.assertTrue(r['passed'])
        self.assertTrue(r['inputs_unchanged'])
        self.assertTrue(r['temporary_tree_removed'])
        self.assertEqual(len(r['checks']), 11)
        for label,row in r['checks'].items():
            self.assertEqual(row['exit_code'], 1 if label.startswith('negative-') else 0, label)
        for p,h in r['inputs'].items():
            self.assertEqual(hashlib.sha256((ROOT/p).read_bytes()).hexdigest(), h, p)

    def test_independent_positive_does_not_import_candidate(self):
        s = (LOG/'gate01/PositiveRoots.v.snapshot.txt').read_text()
        self.assertIn('Require Import GeneralReadyGate.FrozenPrefix.', s)
        self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.', s)
        self.assertIn('Theorem '+gate().TARGET, s)

    def test_single_factor_controls_preserve_entire_proof(self):
        controls = gate().controls((ROOT/gate().SOURCE).read_text())
        self.assertEqual({c[0] for c in controls}, {'NoOwnedEntry', 'StaleTaskRelation'})
        for label,changed,original,_ in controls:
            i = changed.index('Proof.', changed.index('Theorem '+gate().TARGET+' :'))
            j = original.index('Proof.', original.index('Theorem '+gate().TARGET+' :'))
            self.assertEqual(changed[i:], original[j:])
            row = result()['checks']['negative-'+label]
            self.assertGreater(row['error_line'], row['target_proof_line'])
            self.assertFalse(row['downstream_credit'])
            self.assertEqual(hashlib.sha256(changed.encode()).hexdigest(), row['sha256'])

    def test_assumptions_and_no_added_axioms_or_placeholders(self):
        r = result()
        allowed = {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
        for names in [r['probe_assumptions'], r['positive_assumptions']]:
            self.assertLessEqual(set(names), allowed)
        _, s, _ = gate().parts((ROOT/gate().SOURCE).read_text())
        s = re.sub(r'\(\*.*?\*\)', '', s, flags=re.S)
        self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|vm_compute)\b', s))

    def test_historical_tests_drivers_and_evidence_not_rewritten(self):
        for p,h in json.loads((LOG/'historical-inputs-before.json').read_text()).items():
            self.assertEqual(hashlib.sha256((ROOT/p).read_bytes()).hexdigest(), h, p)


if __name__ == '__main__':
    unittest.main()
