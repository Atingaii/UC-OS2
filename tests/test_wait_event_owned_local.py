"""Local source/provenance checks; semantic claims are checked by Coq gate."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT/'audit/logs/stage26-wait-event-owned'


def driver():
    spec = importlib.util.spec_from_file_location('wait_event_gate', ROOT/'scripts/check-v293-wait-event-owned.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def report():
    return json.loads((LOG/'gate01/result.json').read_text())


def source():
    return (ROOT/driver().SOURCE).read_text()


class WaitEventOwnedTests(unittest.TestCase):
    def test_frozen_prefix_and_target_scope_unchanged(self):
        g = driver()
        raw = (ROOT/g.SOURCE).read_bytes()
        self.assertEqual(hashlib.sha256(raw[:g.PREFIX_BYTES]).hexdigest(), g.PREFIX_SHA)
        self.assertEqual(raw[:g.PREFIX_BYTES], (LOG/'V293CriticalReturn.v.before.snapshot.txt').read_bytes())
        b = json.loads((LOG/'baseline.json').read_text())
        current = {str(p.relative_to(ROOT)) for d in ['framework', 'tactics', 'certiucos/v293']
                   for p in (ROOT/d).rglob('*.v')}
        self.assertEqual(current, set(b['active']))
        self.assertEqual([p for p,h in b['active'].items()
                          if hashlib.sha256((ROOT/p).read_bytes()).hexdigest() != h], [g.SOURCE])
        for p,h in b['protected'].items():
            self.assertEqual(hashlib.sha256((ROOT/p).read_bytes()).hexdigest(), h, p)

    def test_wait_primitive_preserves_reason_timeout_message(self):
        suffix = driver().parts(source())[1]
        primitive = suffix[suffix.index('Definition V293_wait_prio_step'):suffix.index('Lemma V293_wait_prio_eqdom')]
        self.assertIn('wait reason delay,message', primitive)
        self.assertNotIn(',rdy,', primitive)
        owned = suffix[suffix.index('Theorem V293_wait_prio_owned_step'):suffix.index('Lemma V293_wait_test_from_task')]
        self.assertIn('spec_prim_step', owned)
        self.assertIn('V293_wait_prio_eqdom', owned)
        self.assertIn('V293_wait_prio_shared_fields', owned)

    def test_general_entry_has_no_completed_execution_or_freshness_oracle(self):
        s = source().split('Theorem '+driver().TARGET+' :', 1)[1]
        header = s.split('  exists Mf Os\' OO\',', 1)[0]
        for bad in ['V293_local_steps', 'spec_step', 'store ', 'free ', 'forall t status msg']:
            self.assertNotIn(bad, header)
        for required in ['V293_priority_table entries tasks', 'V293_bitmap_tasks lo hi tasks',
                         'V293_event_wait_tasks elo ehi tasks reason', 'wait reason delay,message',
                         'reason = os_stat_sem (be,Int.repr ebase)', 'join Os Of OO']:
            self.assertIn(required, header)
        proof = s.split('Proof.', 1)[1]
        for required in ['rewrite Empty in Loaded', 'V293_rekey_task_entry', 'V293_wait_prio_owned_step',
                         'V293_wait_prio_branch_relations', 'V293_critical_event_success_return_execution']:
            self.assertIn(required, proof)
        self.assertNotIn('V293_critical_event_success_return_witness', proof)

    def test_same_final_memory_covers_wait_ready_event_and_return(self):
        s = source().split('Theorem '+driver().TARGET+' :', 1)[1].split('Proof.', 1)[0]
        for required in ['((ge,caller,Mf),ir,(enabled,si,ci))',
                         'V293_rekey_bitmap_loads Mf br bg lo hi', 'V293_event_bitmap_loads Mf be ebase',
                         'V293_tcb_updated_loads Mf bt base new', 'get Mf (c,Z.of_nat k) = None',
                         'shared_fields abstract_current', 'events now ** Atrue',
                         'Some (Int.repr (Z.of_nat new),wait reason delay,message)', '<> Some (p,rdy,msg)']:
            self.assertIn(required, s)
        self.assertNotIn('events now ** R /\\', s)
        self.assertNotIn('V293_ready_inv', s)

    def test_probe_constructs_entry_and_calls_general_contract(self):
        p = (ROOT/driver().PROBE).read_text()
        witness = p.split('Theorem expected_wait_event_nonvacuity', 1)[1]
        for required in ['expected_wait_event_contract V293_success_tail_fixture_program',
                         'expected_wait_fixture_relations', 'expected_wait_entry_mem',
                         'V293_shared_fixture_fields', 'FinalEvent', 'FinalBitmap', 'NotReady']:
            self.assertIn(required, witness)
        self.assertNotIn('V293_critical_event_success_return_witness', witness)
        self.assertNotIn('(ROOT/PROBE).write_text', (ROOT/'scripts/check-v293-wait-event-owned.py').read_text())
        self.assertIn('Theorem expected_wait_stale_event_rejected', p)

    def test_actual_twelve_checks_and_input_identity(self):
        r = report()
        self.assertTrue(r['passed'])
        self.assertTrue(r['inputs_unchanged'])
        self.assertTrue(r['temporary_tree_removed'])
        self.assertEqual(len(r['checks']), 12)
        self.assertEqual(len(r['inputs']), 176)
        for name,row in r['checks'].items():
            self.assertEqual(row['exit_code'], 1 if name.startswith('negative-') else 0, name)
        for p,h in r['inputs'].items():
            self.assertEqual(hashlib.sha256((ROOT/p).read_bytes()).hexdigest(), h, p)
        allowed = {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
        for names in [r['probe_assumptions'], r['positive_assumptions']]:
            self.assertLessEqual(set(names), allowed)

    def test_isolated_positive_and_full_proof_single_factor_negatives(self):
        g = driver()
        positive = (LOG/'gate01/PositiveRoots.v.snapshot.txt').read_text()
        self.assertIn('Require Import WaitEntryGate.FrozenPrefix.', positive)
        self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.', positive)
        controls = g.controls(source())
        self.assertEqual({row[0] for row in controls}, {'WakeWaiter', 'StaleEventRelation'})
        for label,changed,original,_ in controls:
            marker = 'Theorem '+g.TARGET+' :'
            cp = changed[changed.index('Proof.',changed.index(marker)):]
            op = original[original.index('Proof.',original.index(marker)):]
            self.assertEqual(cp, op)
            row = report()['checks']['negative-'+label]
            self.assertEqual(hashlib.sha256(changed.encode()).hexdigest(), row['sha256'])
            self.assertGreater(row['error_line'], row['target_proof_line'])
            self.assertFalse(row['downstream_credit'])

    def test_no_new_axioms_and_historical_inputs_untouched(self):
        suffix = driver().parts(source())[1]
        self.assertIsNone(re.search(r'\b(Admitted|admit|Axiom|Parameter|Conjecture)\b', suffix))
        history = json.loads((LOG/'historical-inputs-before.json').read_text())
        for p,h in history.items():
            self.assertEqual(hashlib.sha256((ROOT/p).read_bytes()).hexdigest(), h, p)


if __name__ == '__main__':
    unittest.main()
