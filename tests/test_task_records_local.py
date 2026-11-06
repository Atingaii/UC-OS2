"""Protocol regression tests; Coq/coqchk logs carry the semantic credit."""
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
LOG=ROOT/'audit/logs/stage26-task-records'


def driver():
    s=importlib.util.spec_from_file_location('records_gate',ROOT/'scripts/check-v293-task-records.py')
    m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def header(s,n):
    a=s.index('Theorem '+n+' :');return s[a:s.index('Proof.',a)]


class TaskRecordsTests(unittest.TestCase):
    def test_prefix_history_and_frozen_source_unchanged(self):
        g=driver();b=json.loads((LOG/'baseline.json').read_text())
        self.assertEqual(len(b['active']),166)
        self.assertEqual(sha(ROOT/g.BEFORE),g.BEFORE_SHA)
        self.assertTrue((ROOT/g.SOURCE).read_bytes().startswith((ROOT/g.BEFORE).read_bytes()))
        for p,h in {**b['protected'],**b['historical'],**{p:h for p,h in b['active'].items() if p!=g.SOURCE}}.items():
            self.assertEqual(sha(ROOT/p),h,p)

    def test_all_old_conditions_and_outputs_retained(self):
        g=driver();old='V293_critical_event_current_owned_execution'
        entry,post=header((ROOT/g.BEFORE).read_text(),old).split("  exists Mf Os' OO',",1)
        new=header((ROOT/g.SOURCE).read_text(),g.TARGET);ne,np=new.split("  exists Mf Os' OO',",1)
        self.assertTrue(ne.startswith(entry.replace(old,g.TARGET,1)))
        self.assertIn('V293_task_records M tasks ->',ne[len(entry):])
        self.assertIn('t <> (bt,Int.repr base)',ne[len(entry):])
        self.assertTrue(np.startswith(post.rstrip()[:-1]+' /\\'))
        self.assertEqual(new.replace(g.TARGET,'expected_task_records_contract',1),
                         header((ROOT/g.PROBE).read_text(),'expected_task_records_contract'))

    def test_universal_record_has_distinct_ready_time_and_ipc_fields(self):
        s=(ROOT/driver().SOURCE).read_text();s=s[s.index('Definition V293_task_record ('):]
        for f in ['forall t priority status message','get tasks t = Some (priority,status,message)',
                  '| rdy =>','| wait os_stat_time delay =>','| wait reason delay =>',
                  'V293_tcb_updated_loads M (fst t)', 'V293_wait_payload M (fst t)',
                  'load (Tcom_ptr 411%Z) M (fst t', 'V293_task_record_frame','map_get_set\'']:
            self.assertIn(f,s)
        self.assertNotIn('Admitted',s)
        for bad in ['Axiom ','Parameter ','Conjecture ']:self.assertNotIn(bad,s)

    def test_same_return_is_reused_once_with_actual_block_frame(self):
        g=driver();s=(ROOT/g.SOURCE).read_text();s=s[s.index('Theorem '+g.TARGET+' :'):]
        p=s[s.index('Proof.'):]
        self.assertEqual(p.count('V293_critical_event_current_owned_execution P'),1)
        for f in ['FinalEventPointer','FinalPayload','FinalRecord','RecordApart',
                  'V293_task_records_update_frame','apply Outside',"exists Mf. exists Os'. exists OO'."]:
            self.assertIn(f,p)

    def test_new_input_reconstructs_entry_and_rejects_stale_same_return(self):
        s=(ROOT/driver().PROBE).read_text()
        for f in ['Definition RecordProbeMemory','V293_tcb_update_memory CurrentProbeMemory 60%positive 0%Z 4',
                  'RecordProbeReadyRecord','RecordProbeWaitRecord','RecordProbeEntryRecords',
                  'RecordProbeEntryCore','expected_task_records_contract V293_success_tail_fixture_program',
                  'RecordProbeNoStaleTasks','RecordProbeOldInputMissingCurrent',
                  'RecordProbeExecution sc now op ir enabled si ci','~ V293_task_records Mf expected_payload_tasks']:
            self.assertIn(f,s)
        self.assertNotIn('destruct (OwnershipProbeExecution ',s)
        self.assertNotIn('Abort.',s)
        self.assertEqual(s.count('Print Assumptions '),9)

    def test_two_single_factor_controls_fix_entire_proof_suffix(self):
        g=driver();p,negative=g.controls((ROOT/g.SOURCE).read_text())
        self.assertEqual(set(negative),{'DroppedOtherFrame','StaleTaskRecord'})
        for name,s in negative.items():
            marker='Lemma V293_task_records_update_frame :' if name=='DroppedOtherFrame' else 'Theorem '+g.TARGET+' :'
            start=lambda t:t.index('Proof.',t.index(marker))
            self.assertEqual(s[start(s):],p[start(p):])
        self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.',p)
        self.assertIn('Require Import TaskRecordsGate.FrozenPrefix.',p)

    def test_twenty_actual_checks_and_frozen_inputs(self):
        r=json.loads((LOG/'gate01/result.json').read_text())
        for k in ['passed','inputs_unchanged','temporary_tree_removed']:self.assertTrue(r[k])
        self.assertEqual(len(r['checks']),20);self.assertEqual(len(r['inputs']),192)
        for p,h in r['inputs'].items():self.assertEqual(sha(ROOT/p),h,p)
        for n,c in r['checks'].items():
            self.assertEqual(c['exit_code'],1 if n.startswith('negative-') else 0,n)
            if n.startswith('negative-'):
                self.assertFalse(c['downstream_credit']);self.assertTrue(c['proof_suffix_unchanged'])
                self.assertGreater(c['error_line'],c['target_proof_line'])

    def test_assumptions_and_actual_snapshots_source_identity(self):
        g=driver();r=json.loads((LOG/'gate01/result.json').read_text());c=g.module('check-v293-task-prio-rekey.py')
        for n,count,k in [('PositiveRoots',3,'positive_assumptions'),('V293TaskRecordsProbe',9,'probe_assumptions')]:
            self.assertEqual(c.checked_assumptions((LOG/f'gate01/{n}.log').read_text(),count),r[k])
        for name,path in [('Production',g.SOURCE),('Probe',g.PROBE)]:
            self.assertEqual((LOG/f'gate01/{name}.v.snapshot.txt').read_bytes(),(ROOT/path).read_bytes())
        r=json.loads((LOG/'configured-source/result.json').read_text())
        self.assertEqual(r['function']['preprocessed_definition_sha256'],
                         'c29b633e71cf54c2d244eb87c7a5910a1f2973e6cd23d7a23769070b24bc2dbf')
