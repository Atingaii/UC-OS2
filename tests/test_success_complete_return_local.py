"""Finite return refinement: structural checks plus separately recorded Coq gate."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT/'certiucos/v293/proofs/V293CriticalReturn.v'
FROZEN_LOG = ROOT/'audit/logs/stage26-success-complete-return'
LOG = ROOT/'audit/logs/stage26-ready-owned-transition/replayed-entry/complete-return-replay'


def gate():
    p = ROOT/'scripts/check-v293-success-complete-return.py'
    spec = importlib.util.spec_from_file_location('complete_return_gate', p)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def section(name):
    s = SOURCE.read_text()
    i = s.index(name+' :')
    return s[i:s.index('\nQed.',i)+6]


class CompleteReturn(unittest.TestCase):
    def test_frozen_2605_line_prefix(self):
        before = (FROZEN_LOG/'V293CriticalReturn.before.v.snapshot.txt').read_bytes()
        self.assertEqual(len(before),gate().PREFIX_BYTES)
        self.assertEqual(before.count(b'\n'),2605)
        self.assertEqual(hashlib.sha256(before).hexdigest(),gate().PREFIX_SHA)
        self.assertTrue(SOURCE.read_bytes().startswith(before))

    def test_no_added_oracle(self):
        bare = re.sub(r'\(\*.*?\*\)','',SOURCE.read_text(),flags=re.S)
        self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture)\b',bare))
        for name in [gate().NULL,gate().EVENT]:
            pre = section(name).split('Proof.',1)[0].split('  exists Mf,',1)[0]
            for oracle in ['cstepstar','V293_local_steps','storebytes','free Tint','V293_preserves_writable']:
                self.assertNotIn(oracle,pre)
            self.assertIn('V293_bytes_writable M c 0%Z (typelen t)',pre)
            self.assertNotIn('V293_bytes_writable Mh',pre)

    def test_writable_refinement_uses_actual_store_chain(self):
        for name in ['V293_task_prio_prefix_null_update_execution_writable',
                     'V293_task_prio_prefix_event_update_preserves_writable']:
            s = section(name).split('Proof.',1)[1]
            for item in ['V293_store_writable;exact S1','V293_store_writable;exact S2',
                         'V293_store_writable;exact Store','unfold Mr. V293_writable_pure',
                         'unfold Mf. V293_writable_pure']:
                self.assertIn(item,s)

    def test_original_memory_connects_to_tail_and_all_local_free(self):
        for branch,name in [('null',gate().NULL),('event',gate().EVENT)]:
            s = section(name)
            for item in ['V293_critical_'+branch+'_update_execution_writable',
                         'V293_success_tail_return_execution','InitialWritable c t I k K',
                         'eapply UpdateWritable;exact W0','(kseq (V293_task_prio_success_tail running sched) ks)',
                         '((ge,caller,Mf),ir,(enabled,si,ci))','get Mf (c,Z.of_nat k) = None']:
                self.assertIn(item,s)

    def test_heap_observations_are_after_free(self):
        for name in [gate().NULL,gate().EVENT]:
            s = section(name)
            for item in ['V293_tcb_updated_loads Mf','V293_rekey_bitmap_loads Mf',
                         'V293_table_loads V293_tcb_type Mf','apply FreeFrame. apply HeapApart',
                         'NoDup (map fst (getaddr le))']:
                self.assertIn(item,s)
        self.assertIn('V293_event_bitmap_loads Mf',section(gate().EVENT))

    def test_permission_ablation_is_one_boolean_factor(self):
        s = section('V293_success_load_free_permission_ablation')
        for item in ['forall (writable : bool)','(writable,Byte','Some (V293_byteval 7)',
                     'if writable then Some (del M','else None','permission:=writable']:
            self.assertIn(item,s)

    def test_prospective_controls_and_unchanged_statement_control_proofs(self):
        controls = gate().controls(SOURCE.read_text())
        self.assertEqual(len(controls),6)
        self.assertEqual({x[0] for x in controls},{'ReadableNotWritable','NoDupRemoved',
                         'HeapTableMayBeLocal','ReturnOne','CallerNotRestored','SecondTableStoreNeutralized'})
        for label,text,target,unchanged,original in controls:
            if unchanged:
                i = text.index('Proof.',text.index(target+' :'))
                j = original.index('Proof.',original.index(target+' :'))
                self.assertEqual(text[i:],original[j:])
            else:
                self.assertEqual(label,'SecondTableStoreNeutralized')
                self.assertEqual(text.replace('+ apply V293_writable_refl.',
                                              '+ eapply V293_store_writable;exact S2.'),original)

    def test_literal_probe_is_frozen_not_regenerated_by_gate(self):
        driver = (ROOT/'scripts/check-v293-success-complete-return.py').read_text()
        self.assertNotIn('write_text(head)',driver)
        probe = (ROOT/gate().PROBE).read_text()
        for item in ['Definition expected_success_program','Definition expected_tail',
                     'Definition expected_scheduler','Theorem expected_null_complete_root',
                     'Theorem expected_event_complete_root','Theorem expected_permission_ablation']:
            self.assertIn(item,probe)

    def test_recorded_gate_passed_all_17_checks(self):
        result = json.loads((LOG/'gate02/result.json').read_text())
        self.assertTrue(result['passed'])
        self.assertTrue(result['inputs_unchanged'])
        self.assertEqual(len(result['checks']),17)
        self.assertTrue(result['temporary_tree_removed'])

    def test_gate_inputs_match_current_identity(self):
        result = json.loads((LOG/'gate02/result.json').read_text())
        self.assertEqual(len(result['inputs']),173)
        for path,expected in result['inputs'].items():
            self.assertEqual(hashlib.sha256((ROOT/path).read_bytes()).hexdigest(),expected,path)

    def test_actual_new_assumptions_are_bounded(self):
        result = json.loads((LOG/'gate02/result.json').read_text())
        allowed = {'Classical_Prop.classic','FunctionalExtensionality.functional_extensionality_dep'}
        # The reused parser returns a list/set of names rather than a claim in prose.
        for entry in [result['probe_assumptions'],*result['positive_assumptions'].values()]:
            self.assertLessEqual(set(entry),allowed)

    def test_negative_rejection_is_inside_target_proof_only(self):
        result = json.loads((LOG/'gate02/result.json').read_text())
        rows = [v for k,v in result['checks'].items() if k.startswith('negative-')]
        self.assertEqual(len(rows),6)
        for row in rows:
            self.assertEqual(row['exit_code'],1)
            self.assertGreater(row['error_line'],row['target_proof_line'])
            self.assertFalse(row['downstream_credit'])


if __name__ == '__main__':
    unittest.main()
