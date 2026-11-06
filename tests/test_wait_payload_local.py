"""Local provenance checks; semantic claims require the actual Coq gate."""
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT/'audit/logs/stage26-wait-payload'


def driver():
    spec = importlib.util.spec_from_file_location('payload_gate', ROOT/'scripts/check-v293-wait-payload.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def report():
    return json.loads((LOG/'gate01/result.json').read_text())


class WaitPayloadTests(unittest.TestCase):
    def test_prefix_and_fixed_source_preserved(self):
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
            if '/__pycache__/' not in p:
                self.assertEqual(hashlib.sha256((ROOT/p).read_bytes()).hexdigest(), h, p)

    def test_payload_exact_fields_and_four_unsuspended_reasons(self):
        s = driver().parts((ROOT/driver().SOURCE).read_text())[1]
        payload = s.split('Definition V293_wait_payload ',1)[1].split('Lemma V293_tcb_payload_load_frame',1)[0]
        for item in ['base+32','base+44','base+48','base+49', 'Some message', 'Some (Vint32 delay)',
                     'os_stat_sem _', 'os_stat_mbox _', 'os_stat_q _', 'os_stat_mutexsem _']:
            self.assertIn(item,payload)
        self.assertNotIn('os_stat_time => load',payload)
        self.assertIn('| _ => False',payload)

    def test_same_heap_not_completed_execution_oracle(self):
        s = (ROOT/driver().SOURCE).read_text().split('Theorem '+driver().TARGET+' :',1)[1]
        entry,post=s.split("  exists Mf Os' OO',",1)
        for bad in ['V293_local_steps','spec_step','get Mf','load Tint32 Mf']:
            self.assertNotIn(bad,entry)
        self.assertIn('V293_wait_payload M bt base reason delay message pend ->',entry)
        self.assertIn('V293_wait_payload Mf bt base reason delay message pend',post)
        proof=post.split('Proof.',1)[1]
        self.assertIn('V293_critical_event_return_tcb_frame',proof)
        self.assertIn('exact TcbFrame',proof)

    def test_actual_gate_and_assumptions(self):
        r=report()
        self.assertTrue(r['passed'])
        self.assertTrue(r['inputs_unchanged'])
        self.assertTrue(r['temporary_tree_removed'])
        self.assertEqual(len(r['checks']),13)
        for p,h in r['inputs'].items():
            self.assertEqual(hashlib.sha256((ROOT/p).read_bytes()).hexdigest(),h,p)
        for name,row in r['checks'].items():
            self.assertEqual(row['exit_code'],1 if name.startswith('negative-') else 0,name)
        for label in ['probe_assumptions','positive_assumptions']:
            self.assertEqual(set(r[label]),{'Classical_Prop.classic','FunctionalExtensionality.functional_extensionality_dep'})

    def test_negative_controls_only_change_postcondition_full_proof(self):
        g=driver();src=(ROOT/g.SOURCE).read_text();controls=g.controls(src)
        self.assertEqual([x[0] for x in controls],['TimeoutChanged','MessageErased'])
        for label,changed,original,_ in controls:
            start=lambda s:s.index('Proof.',s.index('Theorem '+g.TARGET+' :'))
            self.assertEqual(changed[start(changed):],original[start(original):])
            row=report()['checks']['negative-'+label]
            self.assertFalse(row['downstream_credit'])
            self.assertGreater(row['error_line'],row['target_proof_line'])

    def test_literal_nonnull_fixture_calls_new_contract(self):
        p=(ROOT/driver().PROBE).read_text()
        self.assertIn('Definition expected_payload_message : val := Vptr (120%positive,Int.repr 7)',p)
        w=p.split('Theorem expected_payload_nonvacuity :',1)[1].split('Print Assumptions expected_payload_nonvacuity',1)[0]
        self.assertIn('destruct (expected_payload_contract ',w)
        self.assertIn('exact expected_payload_fixture_bound',w)
        self.assertNotIn('exact expected_wait_event_nonvacuity',w)
        self.assertIn('Proof. exact V293_critical_wait_payload_execution. Qed.',p)

    def test_fine_frame_survives_real_free_not_assumed_final_loads(self):
        s=driver().parts((ROOT/driver().SOURCE).read_text())[1]
        fine=s.split('Theorem V293_critical_event_return_tcb_frame :',1)[1].split('Theorem V293_wait_payload_field_layout',1)[0]
        entry=fine.split('  exists Mf,',1)[0]
        self.assertNotIn('get Mf',entry)
        proof=fine.split('Proof.',1)[1]
        self.assertIn('V293_critical_event_update_execution_writable',proof)
        self.assertIn('V293_success_tail_return_execution',proof)
        self.assertIn('rewrite FreeFrame by (apply HeapApart; simpl;tauto)',proof)
        self.assertIn('apply Untouched. exact Outside.',proof)

    def test_source_hashes_match_fixed_repaired_program(self):
        e=json.loads((LOG/'source-layout-evidence.json').read_text())
        f=json.loads((ROOT/'csrc/repairs/FROZEN_SOURCE.json').read_text())
        for p,h in e['source_hashes'].items():
            self.assertEqual(h,f['program']['source_sha256'][p])
        self.assertIn('OS_STAT_SUSPEND',e['snippets']['Source/ucos_ii.h:100-124'])


if __name__=='__main__':
    unittest.main()
