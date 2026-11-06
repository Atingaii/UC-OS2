"""Resource protocol regressions; semantic credit comes from Coq/coqchk."""
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage26-task-ownership'


def driver():
    spec = importlib.util.spec_from_file_location('ownership_gate', ROOT / 'scripts/check-v293-task-ownership.py')
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class TaskOwnershipTests(unittest.TestCase):
    def test_existing_sources_and_eleven_protected_inputs_preserved(self):
        b = json.loads((LOG / 'baseline.json').read_text())
        self.assertEqual(len(b['active']), 166)
        protected = {p: h for p, h in b['protected'].items() if p != '_CoqProject'}
        self.assertEqual(len(protected), 11)
        for p, h in {**b['active'], **protected}.items():
            self.assertEqual(sha(ROOT / p), h, p)

    def test_default_build_registration_is_exact_append_not_rebinding(self):
        before = LOG / 'Before_CoqProject.snapshot.txt'
        b = json.loads((LOG / 'baseline.json').read_text())
        self.assertEqual(sha(before), b['protected']['_CoqProject'])
        self.assertEqual((ROOT / '_CoqProject').read_bytes(), before.read_bytes() +
                         b'\ncertiucos/v293/proofs/V293TaskRecordOwnership.v\n')
        self.assertNotEqual(sha(ROOT / '_CoqProject'), b['protected']['_CoqProject'])

    def test_full_physical_cells_and_canonical_task_enumeration(self):
        s = (ROOT / driver().SOURCE).read_text()
        for token in ['Amapsto a tp true v', 'V293_owned_task_list (TcbMod.lst tasks)',
                      'V293_record_layout', '| rdy =>', '| wait os_stat_time delay =>',
                      '| wait reason delay =>', 'V293_owned_record_cell_store',
                      'load_mem_mono', 'V293_shared_task_records_sound']:
            self.assertIn(token, s)
        for token in ['Admitted.', 'admit.', 'Axiom ', 'Parameter ', 'Conjecture ']:
            self.assertNotIn(token, s)

    def test_single_factor_controls_keep_all_lemma_statements_and_proofs(self):
        g = driver()
        s = (ROOT / g.SOURCE).read_text()
        negatives = g.controls(s)
        self.assertEqual(set(negatives), {'DroppedPhysicalCell', 'WrongPriorityOffset'})
        marker = 'Lemma V293_record_star_load_l'
        for n in negatives.values():
            self.assertEqual(n[n.index(marker):], s[s.index(marker):])
            self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.', n)

    def test_eight_actual_checks_and_unchanged_frozen_inputs(self):
        r = json.loads((LOG / 'gate02/result.json').read_text())
        for k in ['passed', 'inputs_unchanged', 'temporary_tree_removed']:
            self.assertTrue(r[k])
        self.assertEqual(len(r['checks']), 8)
        self.assertEqual(len({c['name'] for c in r['checks']}), 8)
        for c in r['checks']:
            self.assertEqual(c['exit_code'], c['expected_exit_code'])
            if c['name'] in {'DroppedPhysicalCell', 'WrongPriorityOffset'}:
                self.assertEqual(c['exit_code'], 1)
                self.assertFalse(c['downstream_credit'])
                self.assertTrue(c['all_lemma_statement_and_proof_suffix_unchanged'])
                self.assertGreater(c['error_line'], c['target_proof_line'])
        self.assertTrue(r['inputs'])
        for p, h in r['inputs'].items():
            self.assertEqual(sha(ROOT / p), h, p)

    def test_actual_assumptions_and_compiled_snapshots(self):
        g = driver()
        r = json.loads((LOG / 'gate02/result.json').read_text())
        check = g.helper('check-v293-task-prio-rekey.py').checked_assumptions
        self.assertEqual(check((LOG / 'gate02/Positive.log').read_text(), 4), r['positive_assumptions'])
        self.assertEqual(check((LOG / 'gate02/Probe.log').read_text(), 8), r['probe_assumptions'])
        for name, p in [('Production', g.SOURCE), ('Probe', g.PROBE)]:
            self.assertEqual((LOG / f'gate02/{name}.v.snapshot.txt').read_bytes(), (ROOT / p).read_bytes())

    def test_shared_fixture_uses_same_heap_and_abstract_task_map(self):
        s = (ROOT / driver().PROBE).read_text()
        for token in ['OwnershipLiteralSpatial', 'OwnershipSharedLiteralSpatial',
                      'OwnershipSharedLiteralRecords', 'OwnershipPointerTasksJoin',
                      'OwnershipSharedMemory OwnershipSharedAbs',
                      'V293_shared_task_records OwnershipReady OwnershipTasks',
                      'get OwnershipSharedAbs abstcblsid', 'V293_task_records OwnershipSharedMemory OwnershipTasks']:
            self.assertIn(token, s)
        self.assertEqual(s.count('Print Assumptions '), 8)
        self.assertNotIn('Abort.', s)

    def test_readable_half_permission_is_not_full_write_ownership(self):
        s = (ROOT / driver().PROBE).read_text()
        for token in ['OwnershipReadableNotWritable', 'false (encode_val Tint8 (V293_byteval 6))',
                      '~ exists Mf, store Tint8 OwnershipReadOnlyCell',
                      'Some (false,Byte (Byte.repr 6))', 'rewrite ReadPermission in Store',
                      'V293_owned_record_cell_store _ _ _ (V293_byteval 7)']:
            self.assertIn(token, s)
        # This is a protocol guard, not a substitute for the compiled theorem.
        self.assertIn('OwnershipReadableNotWritable', driver().PROBE_ROOTS)


if __name__ == '__main__':
    unittest.main()
