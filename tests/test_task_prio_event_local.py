"""Static companions; actual kernel gate checks all proof executions separately."""
import importlib.util
from pathlib import Path
import re
import json
import unittest
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('event_check',ROOT/'scripts/check-v293-task-prio-rekey.py')
CHECK=importlib.util.module_from_spec(spec);spec.loader.exec_module(CHECK)

class EventLocalTests(unittest.TestCase):
    def setUp(self):
        self.code=(ROOT/CHECK.CODE).read_text();self.proof=(ROOT/CHECK.PROOF).read_text()
        self.probe=(ROOT/'audit/probes/V293TaskPrioEventProbe.v').read_text()
    def header(self,name):
        return self.proof.split('Theorem '+name+' :',1)[1].split('Proof.',1)[0]
    def test_frozen_actual_source_and_field_order(self):
        d=ROOT/'audit/logs/stage26-task-prio-event'
        identity=json.loads((d/'source-identity.json').read_text())
        self.assertTrue(identity['function_record_matches_frozen'])
        record=json.loads((d/'configured-event-record.json').read_text())
        fields=[n['name'] for n in record['inner'] if n.get('kind')=='FieldDecl']
        self.assertEqual(fields,['OSEventType','OSEventPtr','OSEventCnt','OSEventGrp','OSEventTbl'])
        ast=json.loads((d/'configured-event-ast.json').read_text())
        self.assertEqual(ast['read_field']['name'],'OSTCBEventPtr')
        self.assertEqual(ast['independent_if']['inner'][0]['opcode'],'!=')
    def test_real_independent_if_and_field_lvalues(self):
        s=self.code.split('Definition V293_task_prio_event_then',1)[1]
        self.assertIn('efield (ederef (evar pevent)) 5%Z',s)
        self.assertIn('efield (ederef (evar pevent)) 4%Z',s)
        self.assertIn('sseq (V293_task_prio_event_read ptcb pevent)',s)
        self.assertIn('sifthen (V293_task_prio_event_test pevent)',s)
        self.assertNotIn('sifthenelse',s)
        self.assertIn('ecast enull (Tptr V293_event_type)',s)
    def test_actual_assignment_constructs_store_and_test(self):
        h=self.header('V293_task_prio_event_read_execution');entry,out=h.split('exists Me,',1)
        self.assertIn('V293_bytes_writable M be 0%Z 4',entry)
        self.assertIn('load (Tcom_ptr 411%Z) M',entry)
        for oracle in ['store ', 'cstepstar', 'evalval','Me']:
            self.assertNotIn(oracle,entry)
        self.assertIn('store (Tptr V293_event_type)',out)
        self.assertIn('V293_task_prio_event_test pevent',out)
        self.assertIn('apply eq_vcomptr',self.proof)
    def test_continuous_same_state_and_final_table(self):
        h=self.header('V293_task_prio_prefix_event_null_execution');entry,out=h.split('exists M1 M2 Me,',1)
        for oracle in ['store ', 'cstepstar', 'evalval','Mf','M1','M2']:
            self.assertNotIn(oracle,entry)
        self.assertIn('V293_task_prio_prefix_event table',out)
        self.assertIn('store (Tptr V293_event_type) Mf',out)
        self.assertIn('V293_table_loads V293_tcb_type Me',out)
        self.assertIn('V293_rekey_bitmap_loads Me',out)
        self.assertIn('get Me (c,i) = get M (c,i)',out)
        # Intermediate locals are not incorrectly promised after possible aliasing to be.
        self.assertIn('V293_rekey_locals ge le Mf',out)
    def test_concrete_witnesses_not_vacuous_and_not_nonnull_execution(self):
        h=self.header('V293_event_read_controls')
        self.assertIn('live Vnull false',h)
        self.assertIn('(Vptr (72%positive,Int.repr 5)) true',h)
        h=self.header('V293_prefix_event_controls')
        self.assertIn('true 80 Vnull',h);self.assertIn('false 16 Vnull',h)
        self.assertNotIn(' ->',h)
        self.assertNotIn('V293_event_nonnull_observes',h)
    def test_probe_has_static_literal_expectations_not_candidate_aliases(self):
        for alias in ['V293_event_type','V293_event_fields','V293_task_prio_event_read',
                      'V293_task_prio_event_test','V293_task_prio_event_then',
                      'V293_task_prio_prefix_event','V293_event_fixture_mem','V293_event_fixture_le',
                      'V293_prefix_event_observes','V293_event_read_observes']:
            self.assertNotRegex(self.probe,r'\b'+alias+r'\b')
        self.assertIn('Definition checked_event_fields',self.probe)
        self.assertIn('sseq (checked_prefix',self.probe)
        self.assertIn('(ge,le,Me)',self.probe)
    def test_four_single_header_controls_retain_complete_suffix(self):
        cases=CHECK.mutations(self.proof,event=True);self.assertEqual(len(cases),4)
        for label,(s,decl) in cases.items():
            start=self.proof.index(decl);a=self.proof.index('Proof.',start);b=s.index('Proof.',start)
            self.assertEqual(s[:start],self.proof[:start],label)
            self.assertEqual(s[b:],self.proof[a:],label)
            self.assertNotEqual(s[start:b],self.proof[start:a],label)
    def test_eight_assumption_prints_unknown_axioms_rejected(self):
        self.assertEqual(self.probe.count('Print Assumptions checked_'),8)
        self.assertEqual(CHECK.checked_assumptions('Closed under the global context\n'*8,8),[])
        for s in ['Closed under the global context\n'*7,'Axioms:\nInjected : False\n'*8]:
            with self.assertRaises(ValueError):CHECK.checked_assumptions(s,8)
if __name__=='__main__':unittest.main()
