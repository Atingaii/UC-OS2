"""Protocol/identity tests; semantic evidence comes from the actual Coq checks."""
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import unittest

ROOT=Path(__file__).resolve().parents[1]
LOG=ROOT/'audit/logs/stage26-event-return-frame'


def driver():
    s=importlib.util.spec_from_file_location('event_return_frame_gate',ROOT/'scripts/check-v293-event-return-frame.py')
    m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def theorem(s,n):
    a=s.index('Theorem '+n+' :');return s[a:s.index('Qed.',a)+4]


class EventReturnFrameTests(unittest.TestCase):
    def test_only_one_active_source_changed_no_frozen_evidence_rewritten(self):
        g=driver();b=json.loads((LOG/'baseline.json').read_text())
        self.assertEqual(len(b['active']),166)
        for p,h in {**b['protected'],**b['historical'],**{p:h for p,h in b['active'].items() if p!=g.SOURCE}}.items():
            self.assertEqual(sha(ROOT/p),h,p)
        self.assertNotEqual(sha(ROOT/g.SOURCE),b['active'][g.SOURCE])

    def test_original_public_contracts_and_entry_assumptions_exact(self):
        g=driver();s=(ROOT/g.SOURCE).read_text();old=(ROOT/g.BEFORE).read_text()
        self.assertEqual(sha(ROOT/g.BEFORE),g.BEFORE_SHA)
        for n in g.ORIGINALS:
            self.assertEqual(g.statement(s,n),g.statement(old,n),n)
            strong=g.statement(s,n+'_event_frame').replace(n+'_event_frame',n,1)
            self.assertEqual(strong.split('  exists ',1)[0],g.statement(old,n).split('  exists ',1)[0],n)
            wrapper=theorem(s,n).split('Proof.',1)[1]
            self.assertEqual(wrapper.count(n+'_event_frame '),1)
            self.assertNotIn('V293_local_steps',wrapper)

    def test_same_store_chain_and_same_full_return_witness(self):
        g=driver();s=(ROOT/g.SOURCE).read_text()
        lower=theorem(s,g.ORIGINALS[0]+'_event_frame')
        for t in ['V293_storebytes_outside _ _ _ _ _ _ _ S2',
                  'V293_storebytes_outside _ _ _ _ _ _ _ S1',
                  'V293_storebytes_outside _ _ _ _ _ _ _ Store',
                  'V293_event_rekey_byte_frame','rewrite TF','exact EventHeader']:
            self.assertIn(t,lower)
        full=theorem(s,'V293_critical_event_return_tcb_frame_event_frame')
        self.assertEqual(full.count('V293_critical_event_update_execution_writable_event_frame P'),1)
        self.assertEqual(full.count('V293_success_tail_return_execution P'),1)
        self.assertIn('rewrite FreeFrame by (apply HeapApart; simpl;tauto)',full)
        self.assertIn('apply EventHeader. exact Outside',full)
        queue=theorem(s,g.TARGET)
        self.assertEqual(queue.count('V293_critical_wait_payload_execution_event_frame P'),1)
        self.assertIn('reason data waiters',queue)
        self.assertIn('intro Kind. eapply V293_event_type_matches_frame',queue)
        self.assertIn('V293_event_type_matches M be ebase data ->',queue)

    def test_fixed_probe_constructs_new_input_and_full_semantic_counterexample(self):
        p=(ROOT/driver().PROBE).read_text()
        for t in ['V293_put_byte expected_payload_entry_mem (72%positive,5%Z) 3',
                  'expected_event_return_contract V293_success_tail_fixture_program',
                  'EventReturnProbeGetFrame','EventReturnProbeLoadFrame','EventReturnProbeKind',
                  'EventReturnProbeWrittenByteChanges','EventReturnProbeRejectsMailbox',
                  'EventReturnProbeExecution sc now op ir enabled si ci',
                  'get Mf (72%positive,17%Z) <> get EventReturnProbeMemory (72%positive,17%Z)']:
            self.assertIn(t,p)
        self.assertEqual(p.count('Print Assumptions '),5)
        self.assertNotIn('V293_event_rekey_changes_wait_byte',p)
        self.assertNotIn('expected_event_queue_nonvacuity sc',p)

    def test_single_factor_controls_preserve_entire_target_proof(self):
        g=driver();s=(ROOT/g.SOURCE).read_text();positive,controls=g.controls(s)
        proof=lambda x:x[x.index('Proof.',x.index('Theorem '+g.TARGET+' :')):]
        for name,negative in controls.items():
            self.assertEqual(proof(negative),proof(positive),name)
        self.assertIn('forall i, True -> get Mf',controls['WrittenByteFramed'])
        self.assertIn('Mf be ebase (absmbox Vnull)',controls['MailboxSubstituted'])

    def test_sixteen_actual_checks_and_frozen_inputs(self):
        g=driver();r=json.loads((LOG/'gate01/result.json').read_text())
        self.assertTrue(r['passed']);self.assertTrue(r['inputs_unchanged']);self.assertTrue(r['temporary_tree_removed'])
        self.assertTrue(r['old_public_statements_identical']);self.assertEqual(len(r['checks']),16)
        for p,h in r['inputs'].items():self.assertEqual(sha(ROOT/p),h,p)
        for n,row in r['checks'].items():
            self.assertEqual(row['exit_code'],1 if n.startswith('negative-') else 0,n)
            self.assertTrue((LOG/'gate01'/row['log']).exists())
            if n.startswith('negative-'):
                self.assertTrue(row['proof_suffix_unchanged']);self.assertFalse(row['downstream_credit'])
                self.assertGreater(row['error_line'],row['target_proof_line'])
        for n in ['Production-coqchk','Probe-coqchk','PositiveRoots-coqchk']:self.assertIn(n,r['checks'])

    def test_actual_assumptions_and_independent_pre_target_prefix(self):
        g=driver();r=json.loads((LOG/'gate01/result.json').read_text());checker=g.module('check-v293-task-prio-rekey.py')
        self.assertEqual(checker.checked_assumptions((LOG/'gate01/PositiveRoots.log').read_text(),8),r['positive_assumptions'])
        self.assertEqual(checker.checked_assumptions((LOG/'gate01/V293EventReturnFrameProbe.log').read_text(),5),r['probe_assumptions'])
        positive=(LOG/'gate01/PositiveRoots.v.snapshot.txt').read_text()
        prefix=(LOG/'gate01/FrozenPrefix.v.snapshot.txt').read_text()
        self.assertIn('Require Import EventReturnFrameGate.FrozenPrefix.',positive)
        self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.',positive)
        self.assertNotIn('Theorem '+g.TARGET+' :',prefix)
        self.assertEqual((LOG/'gate01/Production.v.snapshot.txt').read_bytes(),(ROOT/g.SOURCE).read_bytes())

    def test_old_failures_preserved_not_silently_rebased(self):
        old=(ROOT/'audit/logs/stage26-event-type/full-tests-post-docs.log').read_text()
        new=(LOG/'full-tests-before-new-tests.log').read_text()
        diagnostics=lambda s:Counter(re.findall(r'^(?:FAIL|ERROR): .*$',s,re.M))
        self.assertFalse(diagnostics(old)-diagnostics(new))
        self.assertEqual(sum((diagnostics(new)-diagnostics(old)).values()),26)
        self.assertIn('failures=301, errors=1',new)
        c=json.loads((LOG/'configured-source/result.json').read_text())
        self.assertEqual(c['function']['preprocessed_definition_sha256'],'c29b633e71cf54c2d244eb87c7a5910a1f2973e6cd23d7a23769070b24bc2dbf')


if __name__=='__main__':unittest.main()
