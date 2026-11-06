"""Identity/protocol regression tests; actual semantic evidence is Coq, not regex."""
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
LOG=ROOT/'audit/logs/stage26-event-type'


def driver():
    s=importlib.util.spec_from_file_location('event_type_gate',ROOT/'scripts/check-v293-event-type.py')
    m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class EventTypeTests(unittest.TestCase):
    def test_prefix_and_other_inputs_preserved(self):
        g=driver();raw=(ROOT/g.SOURCE).read_bytes()
        self.assertEqual(raw[:g.PREFIX_BYTES],(LOG/'Before.v.snapshot.txt').read_bytes())
        b=json.loads((LOG/'baseline.json').read_text())
        self.assertEqual(len(b['active']),166)
        for p,h in {**b['protected'],**{p:h for p,h in b['active'].items() if p!=g.SOURCE}}.items():
            self.assertEqual(sha(ROOT/p),h,p)

    def test_historical_evidence_not_rewritten(self):
        for p,h in json.loads((LOG/'baseline.json').read_text())['historical'].items():
            self.assertEqual(sha(ROOT/p),h,p)

    def test_physical_code_not_task_status_mask(self):
        suffix=driver().parts((ROOT/driver().SOURCE).read_text())[1]
        for code in ['abssem _ => 3','absmbox _ => 1','absmsgq _ _ => 2','absmutexsem _ _ => 4']:
            self.assertIn(code,suffix)
        evidence=json.loads((LOG/'source-evidence.json').read_text())
        text='\n'.join(row['text'] for row in evidence['header'])
        for symbol,value in [('MBOX',1),('Q',2),('SEM',3),('MUTEX',4)]:
            self.assertRegex(text,r'OS_EVENT_TYPE_'+symbol+r'\s+'+str(value)+r'u')
        self.assertEqual(evidence['hashes']['Source/ucos_ii.h'],'be144099fce9f05f578fcd359f40a922ad17290b8bb553bfd83ff9bb99b7113e')

    def test_single_real_witness_and_precise_frame(self):
        g=driver();s=g.parts((ROOT/g.SOURCE).read_text())[1]
        root=s.split('Theorem '+g.TARGET+' :',1)[1].split('Theorem V293_event_rekey_changes_wait_byte',1)[0]
        entry,post=root.split('  exists Me,',1)
        for oracle in ['cstepstar','get Mf','V293_event_type_matches Mf','store (']:
            self.assertNotIn(oracle,entry)
        self.assertIn('V293_event_type_matches M be base data ->',entry)
        self.assertEqual(post.count('V293_task_prio_event_nonnull_execution'),1)
        self.assertIn('eapply V293_storebytes_outside; [exact Store | left; congruence]',post)
        for term in ['exact Store','exact Exec','exact FinalLoads','exact FinalW','exact FinalLoc',
                     'exact FinalPtr','exact Frame','exact Header','V293_event_type_matches_frame']:
            self.assertIn(term,post)
        self.assertIn('(i < base+10)%Z \\/ (base+12 < i)%Z',post)
        self.assertNotIn('V293_critical_event_queue_execution',post)

    def test_nonvacuous_and_independent_semantic_controls(self):
        probe=(ROOT/driver().PROBE).read_text()
        for term in ['V293_event_body_fixture_entry','V293_event_nonnull_type_execution P ks',
                     'EventTypeProbeRejectsMailbox','EventTypeProbeWrittenByteIsNotFramed',
                     '(72%positive,5%Z) 3','exact High','Some (V293_byteval 0)']:
            self.assertIn(term,probe)
        self.assertEqual(probe.count('Print Assumptions '),4)
        self.assertNotIn('V293_event_nonnull_execution_witness',probe)

    def test_mutation_is_one_postcondition_and_proof_preserved(self):
        g=driver();changed,original=g.control((ROOT/g.SOURCE).read_text())
        start=lambda s:s.index('Proof.',s.index('Theorem '+g.TARGET+' :'))
        self.assertEqual(changed[start(changed):],original[start(original):])
        self.assertEqual(changed,original.replace('  V293_event_type_matches Mf be base data.',
                         '  V293_event_type_matches Mf be base (absmbox Vnull).',1))

    def test_real_gate_and_all_kernel_checks(self):
        r=json.loads((LOG/'gate01/result.json').read_text());self.assertTrue(r['passed'])
        self.assertTrue(r['inputs_unchanged']);self.assertTrue(r['temporary_tree_removed'])
        self.assertEqual(len(r['checks']),14)
        for p,h in r['inputs'].items():
            self.assertEqual(sha(ROOT/p),h,p)
        for n,row in r['checks'].items():
            self.assertEqual(row['exit_code'],1 if n=='negative-HeaderChanged' else 0,n)
            self.assertTrue((LOG/'gate01'/row['log']).exists())
        for n in ['Production-coqchk','Probe-coqchk','PositiveRoots-coqchk']:
            self.assertIn(n,r['checks'])
        neg=r['checks']['negative-HeaderChanged']
        self.assertFalse(neg['downstream_credit']);self.assertTrue(neg['proof_suffix_unchanged'])
        self.assertGreater(neg['error_line'],neg['target_proof_line'])
        self.assertIn('not prefix/coordinates/primitive update/return/free',r['limits'])

    def test_actual_assumptions_and_isolated_positive(self):
        g=driver();r=json.loads((LOG/'gate01/result.json').read_text())
        checker=g.module('check-v293-task-prio-rekey.py')
        self.assertEqual(checker.checked_assumptions((LOG/'gate01/PositiveRoots.log').read_text(),5),r['positive_assumptions'])
        self.assertEqual(checker.checked_assumptions((LOG/'gate01/V293EventTypeProbe.log').read_text(),4),r['probe_assumptions'])
        positive=(LOG/'gate01/PositiveRoots.v.snapshot.txt').read_text()
        self.assertIn('Require Import EventTypeGate.FrozenPrefix.',positive)
        self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.',positive)
        self.assertEqual((LOG/'gate01/Production.v.snapshot.txt').read_bytes(),(ROOT/g.SOURCE).read_bytes())


if __name__=='__main__':
    unittest.main()
