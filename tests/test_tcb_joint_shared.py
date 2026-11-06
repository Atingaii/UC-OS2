"""联合资源接口的结构回归；Coq/coqchk 才是语义检查。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TCBJointShared.v'
PROBE = 'audit/probes/V293TCBJointSharedProbe.v'
D = R / 'audit/logs/stage127-tcb-joint-shared'


class TCBJointSharedTests(unittest.TestCase):
    def setUp(self):
        self.source = (R / SOURCE).read_text()
        self.probe = (R / PROBE).read_text()

    def section(self, name, probe=False):
        text = self.probe if probe else self.source
        return text.split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_no_holes_or_audit_in_production(self):
        for text in [self.source, self.probe]:
            self.assertNotRegex(text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.', self.source)
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

    def test_any_priority_is_extracted_and_rejoined(self):
        self.assertIn('V293_priority_slots table reserved(seq 0 13)', self.source)
        select = self.section('V293_priority_table_select')
        for text in ['p<13', '<==>', 'V293_priority_rest table reserved p', 'seq_nth']:
            self.assertIn(text, select)
        self.assertIn('V293_priority_select_list', select)
        self.assertIn('p<13', self.section('JPAllPriorities', probe=True))

    def test_joint_core_is_nonempty_precise_and_isr_stable(self):
        core = self.source.split('Definition V293_tcb_joint_core', 1)[1].split('Lemma ', 1)[0]
        for text in ['V293_tcb_site_free_pool bt bf', 'V293_priority_table table reserved',
                     'V293_tcb_finite_shared bt bh bg br bn 0']:
            self.assertIn(text, core)
        for name in ['V293_tcb_joint_core_precise', 'V293_tcb_joint_core_good',
                     'V293_tcb_joint_core_isr', 'V293_tcb_joint_noisr_core']:
            self.assertIn(name, self.source)
        self.assertIn('V293_publication_envelope_precise', self.section('V293_tcb_finite_shared_precise'))
        self.assertIn('y<2', self.section('JPBothRows', probe=True))

    def test_complete_body_derives_all_six_borrows(self):
        whole = self.section('V293_OS_TCBInit_joint_shared')
        signature, proof = whole.split('Proof.', 1)
        for name in ['OpenFree', 'CloseFree', 'OpenPrio', 'ClosePrio', 'OpenPub', 'ClosePub',
                     'Kfree', 'Kprio', 'Kpub']:
            self.assertNotIn(name, signature)
        self.assertIn('(V293_TCBInit_function_body hi hc)', signature)
        self.assertIn('V293_OS_TCBInit_site_allocated_finite_published', proof)
        for name in ['free', 'priority', 'publication']:
            self.assertEqual(proof.count('V293_tcb_joint_borrow_' + name), 2)
        for text in ['(fun _=>false)', 'Spec hi=Some', 'Spec hc=Some', '(b,off)<>reserved']:
            self.assertIn(text, signature)

    def test_real_three_calls_same_returned_memory_not_circular(self):
        whole = self.section('V293_OSInit_three_calls_joint')
        pre, post = whole.split('exists (Mmisc Mrdy Mf:mem)', 1)
        self.assertNotIn('V293_tcb_joint_core', pre)
        self.assertNotIn('cstepstar', pre)
        self.assertIn('(ge,caller,Mf,ir,aux,O,op) |=', post)
        self.assertIn('V293_tcb_joint_core bt bf bp bl bg br bcount reserved', post)
        self.assertIn('V293_OSInit_three_calls slots oldtcbs', whole)
        fold = self.section('V293_init_three_result_joint')
        for text in ['In d slots', 'init_type d=Tint8', 'init_block d=bn', 'in_split',
                     'V293_raw_cells_permutation', 'V293_tcb_call_result_joint',
                     'V293_raw_cells_absorb']:
            self.assertIn(text, fold)

    def test_independent_literal_fixture_and_direct_stable_interface(self):
        actual = self.section('JPActualInitialization', probe=True)
        for text in ['ChainEntryMemory', 'V293_OSInit_three_calls_joint', 'ChainLiteralFullEntry',
                     'Build_V293_init_slot 1004%Z Tint8 184%positive', 'exact Final']:
            self.assertIn(text, actual)
        literal = R / 'audit/probes/V293InitChainProbe.v'
        base = json.loads((D / 'baseline.json').read_text())
        self.assertEqual(hashlib.sha256(literal.read_bytes()).hexdigest(),
                         base[str(literal.relative_to(R))]['sha256'])
        self.assertIn('JPActualInitialization ks', self.section('JPActualPriorityViews', probe=True))

    def test_physical_permission_only_ablation(self):
        for text in ['V293_encoded_memory 84%positive 16%Z perm', 'JPSlotState false',
                     'JPSlotState true', 'V293_reservation_publish', 'V293_reservation_pool_null']:
            self.assertIn(text, self.probe)
        control = self.section('JPPermissionOnlyControl', probe=True)
        for text in ['Some(true,Pointer', 'Some(false,Pointer', 'option_map snd',
                     '(20<=j)%Z', 'V293_encoded_memory_outside']:
            self.assertIn(text, control)
        rejected = self.section('JPFullPoolOverbookingRejected', probe=True)
        self.assertIn('V293_reservation_full_half_conflict', rejected)
        self.assertIn('-> False', rejected)

    def test_stable_compilation_and_explicit_limits(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('proof', SOURCE), ('probe', PROBE)]:
            label = stable[kind]
            record = json.loads((D / (label + '.json')).read_text())
            data = (R / path).read_bytes()
            self.assertEqual(record['exit'], 0)
            self.assertEqual(record['initial_source_sha256'], record['source_sha256'])
            self.assertEqual(hashlib.sha256(data).hexdigest(), record['source_sha256'])
            self.assertEqual(data, (D / (label + '.v.snapshot.txt')).read_bytes())
        doc = (R / 'audit/STAGE127_TCB_JOINT_SHARED.md').read_text()
        for text in ['不是生产全局Inv', '全false', 'token freshness', 'WFIFun', 'GOOD_OS', 'uCOS3',
                     '同一份', 'Atrue', '单因素']:
            self.assertIn(text, doc)
        rows = json.loads((R / 'audit/coverage.json').read_text())['rows']
        self.assertEqual([sum(bool(row[k]) for row in rows) for k in
                          ['located', 'modeled', 'specified', 'local_hoare', 'component_linked', 'full_target_linked']],
                         [94, 1, 1, 1, 1, 0])


if __name__ == '__main__':
    unittest.main()
