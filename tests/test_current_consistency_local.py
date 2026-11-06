"""Protocol checks; actual Coq and kernel logs carry semantic proof credit."""
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import unittest

ROOT=Path(__file__).resolve().parents[1]
LOG=ROOT/'audit/logs/stage26-current-consistency'


def driver():
    s=importlib.util.spec_from_file_location('current_gate',ROOT/'scripts/check-v293-current-consistency.py')
    m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def header(s,name):
    a=s.index('Theorem '+name+' :');return s[a:s.index('Proof.',a)]


class CurrentConsistencyTests(unittest.TestCase):
    def test_frozen_prefix_other_sources_and_prior_evidence(self):
        g=driver();b=json.loads((LOG/'baseline.json').read_text())
        self.assertEqual(len(b['active']),166);self.assertEqual(len(b['caches']),903)
        self.assertEqual(sha(ROOT/g.BEFORE),g.BEFORE_SHA)
        self.assertTrue((ROOT/g.SOURCE).read_bytes().startswith((ROOT/g.BEFORE).read_bytes()))
        for p,h in {**b['protected'],**b['historical'],**{p:h for p,h in b['active'].items() if p!=g.SOURCE}}.items():
            self.assertEqual(sha(ROOT/p),h,p)

    def test_all_old_entry_assumptions_and_outputs_retained(self):
        g=driver();old='V293_critical_event_queue_execution_event_frame_data'
        a=header((ROOT/g.BEFORE).read_text(),old);b=header((ROOT/g.SOURCE).read_text(),g.TARGET)
        self.assertEqual(a.replace(old,g.TARGET,1).split('  exists ',1)[0],b.split('  exists ',1)[0])
        self.assertIn(a.split('  exists ',1)[1].rstrip()[:-1]+' /\\',b)
        s=(ROOT/g.SOURCE).read_text();proof=s[s.index('Proof.',s.index('Theorem '+g.TARGET+' :')):]
        self.assertEqual(proof.count(old+' P'),1)
        self.assertIn("exists Mf. exists Os'. exists OO'.",proof)
        self.assertIn('apply V293_load_block_frame; intro i; apply Outside',proof)
        self.assertIn('V293_wait_rekey_preserves_ready_current',proof)
        self.assertNotIn('Admitted',s);self.assertNotIn('Axiom ',s)

    def test_literal_interface_and_new_simultaneous_entry(self):
        g=driver();s=(ROOT/g.SOURCE).read_text();p=(ROOT/g.PROBE).read_text()
        self.assertEqual(header(s,g.TARGET).replace(g.TARGET,'expected_current_contract',1),header(p,'expected_current_contract'))
        for x in ['set V293_complete_fixture_ge OSTCBCur',
                  '(encode_val (Tptr V293_tcb_type) (Vptr (60%positive,Int.zero)))',
                  '(51%positive,0%Z) 8','16 0 8 6 V293_prefix_fixture_entries',
                  'expected_current_contract V293_success_tail_fixture_program',
                  'Some (Int.repr 4,rdy,Vnull)',
                  'CurrentPreserved 80%positive V293_tcb_type (Int.repr 4) Vnull Binding']:
            self.assertIn(x,p)
        self.assertNotIn('destruct (EventDataProbeExecution ',p)

    def test_same_return_semantic_rejection_and_historical_mismatch(self):
        p=(ROOT/driver().PROBE).read_text()
        for name in ['CurrentProbeReturnRejectsWaitingPointer','CurrentProbeOldInputMismatch']:
            self.assertIn('Theorem '+name+' :',p)
        a=p.index('Theorem CurrentProbeReturnRejectsWaitingPointer :');b=p.index('Theorem CurrentProbeOldInputMismatch :')
        self.assertIn('CurrentProbeExecution sc now op ir enabled si ci',p[a:b])
        self.assertIn("get OO' curtid <> Some (oscurt (41%positive,Int.repr 8))",p[a:b])
        self.assertIn('load (Tptr V293_tcb_type) Mf (80%positive,0%Z) <> Some (Vptr (41%positive,Int.repr 8))',p[a:b])
        self.assertIn('load (Tptr V293_tcb_type) EventDataProbeMemory',p[b:])
        self.assertEqual(p.count('Print Assumptions '),7)

    def test_prospective_single_factor_controls_preserve_entire_proof(self):
        g=driver();positive,negative=g.controls((ROOT/g.SOURCE).read_text())
        suffix=lambda s:s[s.index('Proof.',s.index('Theorem '+g.TARGET+' :')):]
        for n,s in negative.items():self.assertEqual(suffix(s),suffix(positive),n)
        self.assertEqual(set(negative),{'WaitingPointer','WaitingAbstractCurrent'})
        self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.',positive)
        self.assertIn('Require Import CurrentConsistencyGate.FrozenPrefix.',positive)

    def test_eighteen_actual_checks_and_all_frozen_inputs(self):
        g=driver();r=json.loads((LOG/'gate01/result.json').read_text())
        self.assertTrue(r['passed']);self.assertTrue(r['inputs_unchanged']);self.assertTrue(r['temporary_tree_removed'])
        self.assertEqual(len(r['checks']),18)
        for p,h in r['inputs'].items():self.assertEqual(sha(ROOT/p),h,p)
        for name,row in r['checks'].items():
            self.assertEqual(row['exit_code'],1 if name.startswith('negative-') else 0,name)
            if name.startswith('negative-'):
                self.assertTrue(row['proof_suffix_unchanged']);self.assertFalse(row['downstream_credit'])
                self.assertGreater(row['error_line'],row['target_proof_line'])
        for name in ['Production-coqchk','Probe-coqchk','PositiveRoots-coqchk']:self.assertIn(name,r['checks'])

    def test_actual_assumptions_and_checked_source_snapshots(self):
        g=driver();r=json.loads((LOG/'gate01/result.json').read_text());m=g.module('check-v293-task-prio-rekey.py')
        for name,n,key in [('PositiveRoots',2,'positive_assumptions'),('V293CurrentConsistencyProbe',7,'probe_assumptions')]:
            self.assertEqual(m.checked_assumptions((LOG/f'gate01/{name}.log').read_text(),n),r[key])
        self.assertEqual((LOG/'gate01/Production.v.snapshot.txt').read_bytes(),(ROOT/g.SOURCE).read_bytes())
        self.assertEqual((LOG/'gate01/Probe.v.snapshot.txt').read_bytes(),(ROOT/g.PROBE).read_bytes())
        self.assertNotIn('Theorem '+g.TARGET+' :',(LOG/'gate01/FrozenPrefix.v.snapshot.txt').read_text())

    def test_configured_source_identity_and_all_prior_diagnostics_retained(self):
        c=json.loads((LOG/'configured-source/result.json').read_text())
        self.assertEqual(c['function']['preprocessed_definition_sha256'],'c29b633e71cf54c2d244eb87c7a5910a1f2973e6cd23d7a23769070b24bc2dbf')
        count=lambda s:Counter(re.findall(r'^(?:FAIL|ERROR): .*$',s,re.M))
        old=count((ROOT/'audit/logs/stage26-event-data/full-tests-post-docs.log').read_text())
        new=count((LOG/'full-tests-before-new-tests.log').read_text())
        self.assertFalse(old-new);self.assertEqual(sum((new-old).values()),2)
        self.assertIn('failures=305, errors=1',(LOG/'full-tests-before-new-tests.log').read_text())


if __name__=='__main__':unittest.main()
