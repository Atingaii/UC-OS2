"""启动边界的结构与证据回归；语义结论由 Coq 检查。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage132-boot-running-boundary'
SOURCE = 'certiucos/v293/proofs/V293BootRunningBoundary.v'
PROBE = 'audit/probes/V293BootRunningBoundaryProbe.v'


class BootRunningBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.source = (R / SOURCE).read_text()
        self.probe = (R / PROBE).read_text()

    def section(self, name, probe=False):
        text = self.probe if probe else self.source
        return text.split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_registered_and_hole_free(self):
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(SOURCE), 1)
        self.assertNotIn('CertiOS.audit.', self.source)
        for text in [self.source, self.probe]:
            self.assertNotRegex(text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')

    def test_generic_null_obstruction_is_not_empty_li_only(self):
        for name in ['V293_null_current_no_CurLINV', 'V293_null_current_no_initst']:
            body = self.section(name)
            self.assertIn('Some Vnull', body)
            self.assertIn('li', body.split('Proof.', 1)[0])
            self.assertNotIn('V293_witness_li', body)
        self.assertIn('V293_shared_current_read', self.source)

    def test_all_initst_constructors_preserve_full_memory_read(self):
        body = self.section('V293_initst_current_read')
        for text in ['induction Init', 'destruct IH', 'load_mono', 'map_join_comm',
                     'get O curtid=Some(oscurt t)', 'Some(Vptr t)']:
            self.assertIn(text, body)

    def test_actual_initializer_has_real_binding_and_same_memory(self):
        self.assertIn('set ChainGE OSTCBCur(166%positive,Tptr V293_tcb_type)', self.probe)
        body = self.section('BRActualInitialization', True)
        for text in ['V293_OSInit_three_calls', 'ChainEntryMemory', 'BRReadyEnvironment',
                     'BRTCBEnvironment', 'BRLiteralEntry', 'BRState Mf |= BRCore',
                     'Mf(166%positive,0%Z)=Some Vnull', 'Mf(185%positive,0%Z)']:
            self.assertIn(text, body)

    def test_single_store_control_reaches_actual_return(self):
        body = self.section('BRCurrentStoreControl', True)
        for text in ['V293_owned_record_cell_update', 'Some Mf',
                     'CurTid BRTarget ** CurTid BRTarget', 'GV_separate_rw_frm',
                     'forall li t', 'Some Vnull', 'V293_witness_li']:
            self.assertIn(text, body)
        linked = self.section('BRReachableCurrentStoreControl', True)
        self.assertIn('BRActualInitialization', linked)
        self.assertIn('BRCurrentStoreControl M Raw', linked)

    def test_ghost_ownership_is_built_independently_and_still_no_current(self):
        direct = self.section('BRAbstractSpatial', True)
        self.assertIn('BRAbsApart', direct)
        self.assertNotIn('V293_fields_no_abstract_frame', direct)
        body = self.section('BRBootAbstractOwnership', True)
        for text in ['BRActualInitialization', 'BRAbstractSpatial',
                     'V293_fields_no_abstract_frame', 'V293_null_current_no_CurLINV']:
            self.assertIn(text, body)

    def test_no_extension_root_does_not_assume_physical_current(self):
        body = self.section('V293_fields_no_abstract_frame')
        self.assertNotIn('CurTid', body)
        for text in ['curtid', 'abstcblsid', 'absecblsid', 'ostmid', 'Of=emp']:
            self.assertIn(text, body)

    def test_stable_compiles_and_bounded_claims(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('proof', SOURCE), ('probe', PROBE)]:
            label = stable[kind]
            row = json.loads((D / (label + '.json')).read_text())
            data = (R / path).read_bytes()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256(data).hexdigest())
            self.assertEqual(data, (D / (label + '.v.snapshot.txt')).read_bytes())
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertEqual(len(protocol['prospective_checks']), 5)
        doc = (R / 'audit/STAGE132_BOOT_RUNNING_BOUNDARY.md').read_text()
        for text in ['单因素', '同一份返回内存', 'placeholder', '不是生产语义Inv',
                     '不证明目标是已创建的任务', 'WFIFun', 'GOOD_OS', 'uCOS3', '423']:
            self.assertIn(text, doc)
