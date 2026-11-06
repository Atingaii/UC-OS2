"""创建路径共享接口的结构回归；不是 Coq 语义证明。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskCreateJointShared.v'
PROBE = 'audit/probes/V293TaskCreateJointSharedProbe.v'
D = R / 'audit/logs/stage128-create-joint-shared'


class TaskCreateJointSharedTests(unittest.TestCase):
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

    def test_only_needed_distinct_nesting_byte_added(self):
        core = self.source.split('Definition V293_create_joint_core', 1)[1].split('Lemma ', 1)[0]
        for text in ['V293_tcb_joint_core bt bf table bh bg rows tasks reserved',
                     'Amapsto(nesting,0%Z)Tint8 true(V293_byteval 0)']:
            self.assertIn(text, core)
        fold = self.section('V293_init_three_result_creator_joint')
        for text in ['In cd slots', 'init_block cd=tasks', 'In nd slots',
                     'init_block nd=nesting', 'tasks<>nesting', 'CountRest',
                     'V293_raw_cells_permutation', 'V293_init_three_result_joint']:
            self.assertIn(text, fold)
        self.assertIn('184%positive<>182%positive', self.section('CPActualNestingZero', True))

    def test_arbitrary_priority_and_full_tcb_body_share_inv(self):
        self.assertIn('p<13', self.section('V293_create_joint_borrow_priority'))
        whole = self.section('V293_OS_TCBInit_creator_joint')
        signature, proof = whole.split('Proof.', 1)
        self.assertIn('(V293_TCBInit_function_body hi hc)', signature)
        self.assertIn('V293_create_joint_inv', signature)
        for text in ['OpenFree', 'CloseFree', 'OpenPrio', 'ClosePrio', 'OpenPub', 'ClosePub']:
            self.assertNotIn(text, signature)
        for text in ['free', 'priority', 'publication']:
            self.assertEqual(proof.count('V293_create_joint_borrow_' + text), 2)
        for text in ['Spec hi=Some', 'Spec hc=Some', '(b,off)<>reserved', '(fun _=>false)']:
            self.assertIn(text, signature)

    def test_original_reservation_and_rollback_not_assumed(self):
        reserve = self.section('V293_OSTaskCreateExt_joint_reservation')
        for text in ['sassign(earrayelem', 'sprim excrit', 'V293_OSTaskCreateExt_owned_reservation',
                     'proj2(V293_create_joint_borrow_priority']:
            self.assertIn(text, reserve)
        rollback = self.section('V293_OSTaskCreateExt_joint_rollback')
        for text in ['V293_TaskCreateExt_rollback 92%Z 101%Z', 'V293_OSTaskCreateExt_owned_rollback',
                     'proj1(V293_create_joint_borrow_priority', 'proj2(V293_create_joint_borrow_priority']:
            self.assertIn(text, rollback)
        self.assertIn('(sprim encrit)', self.section('V293_create_joint_initial_enter'))

    def test_stack_fragment_performs_original_call(self):
        whole = self.section('V293_OSTaskCreateExt_joint_stack_fragment')
        for text in ['Spec hook=Some', 'V293_TaskCreateExt_stack_call 108%Z hook',
                     'V293_create_owned_share table(br,Int.zero)p',
                     'V293_OSTaskCreateExt_owned_stack_fragment', 'proj2(V293_create_joint_borrow_priority']:
            self.assertIn(text, whole)

    def test_actual_three_calls_same_memory_and_literal_fixture(self):
        whole = self.section('V293_OSInit_three_calls_creator_joint')
        pre, post = whole.split('exists (Mmisc Mrdy Mf:mem)', 1)
        self.assertNotIn('V293_create_joint_core', pre)
        self.assertNotIn('cstepstar', pre)
        for text in ['(ge,caller,Mf,ir,aux,O,op) |=', 'bcount<>nesting',
                     'V293_OSInit_three_calls slots oldtcbs']:
            self.assertIn(text, whole)
        actual = self.section('CPActualInitialization', True)
        for text in ['ChainLiteralFullEntry', 'ChainEntryMemory', 'V293_OSInit_three_calls_creator_joint',
                     'Build_V293_init_slot 1004%Z Tint8 184%positive',
                     'Build_V293_init_slot 1002%Z Tint8 182%positive']:
            self.assertIn(text, actual)
        base = json.loads((D / 'baseline.json').read_text())
        for name in ['V293InitChainProbe', 'V293TCBJointSharedProbe']:
            path = 'audit/probes/' + name + '.v'
            self.assertEqual(hashlib.sha256((R / path).read_bytes()).hexdigest(), base[path]['sha256'])

    def test_actual_store_omission_and_half_permission_controls(self):
        for text in ['V293_reservation_reacquire', 'JPReservedShareCompatible',
                     'V293_owned_record_cell_update', 'V293_storebytes_outside']:
            self.assertIn(text, self.probe)
        for name, text in [('CPWrittenRollbackRead', 'CPObserve true=Some Vnull'),
                           ('CPOmittedRollbackRead', 'CPObserve false=Some(Vptr JPToken)'),
                           ('CPOmittedRollbackNotNull', 'CPObserve false<>Some Vnull'),
                           ('CPHalfAloneCannotRollback', 'Vnull=None')]:
            self.assertIn(text, self.section(name, True))
        self.assertIn('if write then store', self.probe)
        self.assertIn('get Mf(b,j)=get(JPSlotMemory true)(b,j)', self.probe)

    def test_stable_compilation_and_limits(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('proof', SOURCE), ('probe', PROBE)]:
            label = stable[kind]
            row = json.loads((D / (label + '.json')).read_text())
            data = (R / path).read_bytes()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(hashlib.sha256(data).hexdigest(), row['source_sha256'])
            self.assertEqual(data, (D / (label + '.v.snapshot.txt')).read_bytes())
        doc = (R / 'audit/STAGE128_CREATE_JOINT_SHARED.md').read_text()
        for text in ['不是生产全局Inv', '全false', 'token freshness', 'WFIFun', 'GOOD_OS',
                     'uCOS3', 'Atrue', '单因素', 'fpre', 'fpost', '尚未']:
            self.assertIn(text, doc)


if __name__ == '__main__':
    unittest.main()
