"""Provenance checks for the real ECB waiter-list connection; Coq checks semantics."""
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT/'audit/logs/stage26-event-queue'


def driver():
    spec = importlib.util.spec_from_file_location('queue_gate', ROOT/'scripts/check-v293-event-queue.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def report():
    return json.loads((LOG/'gate02/result.json').read_text())


class EventQueueTests(unittest.TestCase):
    def test_prefix_and_frozen_inputs_preserved(self):
        g = driver()
        raw = (ROOT/g.SOURCE).read_bytes()
        self.assertEqual(raw[:g.PREFIX_BYTES], (LOG/'Before.v.snapshot.txt').read_bytes())
        self.assertEqual(hashlib.sha256(raw[:g.PREFIX_BYTES]).hexdigest(), g.PREFIX_SHA)
        baseline = json.loads((LOG/'baseline.json').read_text())
        for p,h in baseline['protected'].items():
            self.assertEqual(hashlib.sha256((ROOT/p).read_bytes()).hexdigest(), h, p)

    def test_no_new_active_module_or_historical_rewrite(self):
        b = json.loads((LOG/'baseline.json').read_text())
        active = {str(p.relative_to(ROOT)) for d in ['framework','tactics','certiucos/v293']
                  for p in (ROOT/d).rglob('*.v')}
        self.assertEqual(active, set(b['active']))
        for p,h in b['historical'].items():
            self.assertEqual(hashlib.sha256((ROOT/p).read_bytes()).hexdigest(), h, p)

    def test_queue_binds_actual_ecb_kind_and_both_membership_directions(self):
        s = driver().parts((ROOT/driver().SOURCE).read_text())[1]
        relation = s.split('Definition V293_event_wait_queue ',1)[1].split('Theorem V293_event_wait_queue_rekey',1)[0]
        for item in ['get events eid = Some (data,waiters)', 'In t waiters <->',
                     'os_stat_sem e,abssem _', 'os_stat_mbox e,absmbox _',
                     'os_stat_q e,absmsgq _ _', 'os_stat_mutexsem e,absmutexsem _ _', '| _,_ => False']:
            self.assertIn(item,relation)
        self.assertNotIn('NoDup', relation)
        self.assertNotIn('load Tint8', relation)

    def test_new_root_has_original_entry_not_completed_execution_oracle(self):
        s = (ROOT/driver().SOURCE).read_text().split('Theorem '+driver().TARGET+' :',1)[1]
        entry,post = s.split("  exists Mf Os' OO',",1)
        self.assertIn('V293_event_wait_queue events tasks (be,Int.repr ebase) reason data waiters ->', entry)
        for bad in ['V293_local_steps', 'spec_step', 'get Mf', 'V293_event_queue_priorities']:
            self.assertNotIn(bad,entry)
        proof = post.split('Proof.',1)[1]
        for needed in ['V293_critical_wait_payload_execution','V293_event_wait_queue_rekey',
                       'V293_event_queue_priorities_bound','exact FinalQueue','exact Exec','exact PayloadOut']:
            self.assertIn(needed,proof)

    def test_fixed_literal_fixture_invokes_new_generic_contract(self):
        p = (ROOT/driver().PROBE).read_text()
        self.assertIn('Proof. exact V293_critical_event_queue_execution. Qed.',p)
        self.assertIn('EcbMod.sig (72%positive,Int.repr 5) (abssem Int.zero,expected_queue_waiters)',p)
        self.assertIn('Definition expected_queue_waiters : waitset := [(41%positive,Int.repr 8)]',p)
        w = p.split('Theorem expected_event_queue_nonvacuity :',1)[1].split('Print Assumptions expected_event_queue_nonvacuity',1)[0]
        self.assertIn('destruct (expected_event_queue_contract ',w)
        self.assertIn('exact expected_queue_fixture_bound',w)
        self.assertNotIn('exact expected_payload_nonvacuity',w)
        self.assertIn('expected_queue_priorities 64 0 expected_payload_tasks_updated',w)

    def test_actual_fourteen_checks_and_assumptions(self):
        r = report()
        self.assertTrue(r['passed'])
        self.assertTrue(r['inputs_unchanged'])
        self.assertTrue(r['temporary_tree_removed'])
        self.assertEqual(len(r['checks']),14)
        self.assertEqual(len(r['inputs']),178)
        for p,h in r['inputs'].items():
            self.assertEqual(hashlib.sha256((ROOT/p).read_bytes()).hexdigest(),h,p)
        for name,row in r['checks'].items():
            self.assertEqual(row['exit_code'],1 if name.startswith('negative-') else 0,name)
        for label in ['probe_assumptions','positive_assumptions']:
            self.assertEqual(set(r[label]),{'Classical_Prop.classic','FunctionalExtensionality.functional_extensionality_dep'})

    def test_isolated_prefix_positive_and_full_proof_single_factor_negatives(self):
        g = driver();source = (ROOT/g.SOURCE).read_text();_,_,harness = g.parts(source)
        self.assertIn('Require Import EventQueueGate.FrozenPrefix.',harness)
        self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.',harness)
        controls = g.controls(source)
        self.assertEqual([x[0] for x in controls],['WaiterDropped','EventDataChanged'])
        for label,changed,original,_ in controls:
            start = lambda s: s.index('Proof.',s.index('Theorem '+g.TARGET+' :'))
            self.assertEqual(changed[start(changed):],original[start(original):])
            row = report()['checks']['negative-'+label]
            self.assertEqual(hashlib.sha256(changed.encode()).hexdigest(),row['sha256'])
            self.assertFalse(row['downstream_credit'])
            self.assertGreater(row['error_line'],row['target_proof_line'])

    def test_independent_queue_and_kind_semantic_rejections(self):
        p = (ROOT/driver().PROBE).read_text()
        drop = p.split('Theorem expected_queue_drop_rejected :',1)[1].split('Theorem expected_queue_kind_rejected',1)[0]
        self.assertIn('abssem Int.zero) nil',drop)
        self.assertIn('rewrite EcbMod.map_get_sig in Lookup. discriminate.',drop)
        kind = p.split('Theorem expected_queue_kind_rejected :',1)[1]
        self.assertIn('expected_wait_reason (absmbox Vnull)',kind)
        self.assertIn('exact Kind',kind)

    def test_source_provenance_and_open_physical_event_type_boundary(self):
        e = json.loads((LOG/'event-source-evidence.json').read_text())
        f = json.loads((ROOT/'csrc/repairs/FROZEN_SOURCE.json').read_text())
        self.assertEqual(e['source_hashes'],f['program']['source_sha256'])
        self.assertIn('OSEventType',e['snippets']['378'])
        self.assertIn('OS_EVENT_TYPE_SEM              3u',e['snippets']['133'])
        self.assertIn('physical OSEventType',report()['limits'])


if __name__ == '__main__':
    unittest.main()
