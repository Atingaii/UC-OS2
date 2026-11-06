"""首TCB启动连接的结构／证据回归，不替代Coq语义检查。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage133-boot-tcb-entry'
SOURCE = 'certiucos/v293/proofs/V293BootTCBEntry.v'
PROBE = 'audit/probes/V293BootTCBEntryProbe.v'


class BootTCBEntryTests(unittest.TestCase):
    def setUp(self):
        self.source = (R / SOURCE).read_text()
        self.probe = (R / PROBE).read_text()

    def section(self, name, probe=False):
        text = self.probe if probe else self.source
        return text.split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_registered_hole_free_production_has_no_audit_dependency(self):
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(SOURCE), 1)
        self.assertNotIn('CertiOS.audit.', self.source)
        for text in [self.source, self.probe]:
            self.assertNotRegex(text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')

    def test_exact_zero_bytes_supply_typed_fields_and_four_spares(self):
        for text in ['[0;4;8;28;32;36]', 'base+24', 'base+40', 'base+42', 'base+43']:
            self.assertIn(text, self.source)
        body = self.section('V293_boot_zero_payload_fields')
        for text in ['repeat(Vint32 Int.zero)20', 'repeat(Vint32 Int.zero)32',
                     'V293_init_zero_run_fold', 'V293_boot_tcb_old', 'V293_boot_tcb_spares']:
            self.assertIn(text, body)
        self.assertNotIn('exists old', body)

    def test_remaining_twelve_records_priority_table_and_frame_preserved(self):
        for text in ['tl(V293_tcb_linked_next bt)', 'V293_tcb_untouched_cells bt 56 12',
                     'V293_null_pointer_cells bp 0 13++frame']:
            self.assertIn(text, self.source)
        body = self.section('V293_boot_first_tcb_entry')
        self.assertIn('V293_boot_zero_payload_fields', body)
        self.assertIn('V293_raw_cells_swap', body)

    def test_actual_initialization_returns_same_memory_and_checked_bindings(self):
        self.assertIn('set BRGE 91%Z(95%positive,Tptr V293_tcb_type)', self.probe)
        body = self.section('BTActualInitialization', True)
        for text in ['V293_OSInit_three_calls', 'ChainEntryMemory', 'BTLiteralEntry',
                     'BTReadyEnvironment', 'BTTCBEnvironment',
                     'BTState Mf |= V293_rdy_raw_cells ChainFinalCells Atrue',
                     'BTState Mf |= V293_rdy_raw_cells BTBefore Atrue',
                     'V293_boot_first_tcb_entry']:
            self.assertIn(text, body)

    def test_actual_call_reaches_genuine_missing_hook_with_current_still_null(self):
        self.assertIn('Some(V293_TCBInit_function 206%Z 207%Z)else BRProgram f', self.probe)
        body = self.section('BTEntryToFirstHook', True)
        for text in ['V293_OS_TCBInit_call_to_first_hook', 'exact Exec', 'exact Final',
                     'apply Missing;reflexivity']:
            self.assertIn(text, body)
        observable = self.probe.split('Definition BTAtHook', 1)[1].split('Ltac BTLoad', 1)[0]
        for text in ['V293_tcb_init_final_fields', 'V293_local_steps BTProgram',
                     'sfexec 206%Z', '166%positive,0%Z)=Some Vnull',
                     '185%positive,0%Z)=Some(Vint32 Int.zero)', '~exists C\' state\'']:
            self.assertIn(text, observable)
        self.assertNotIn('CurLINV', body)
        self.assertNotIn('HookReturn', body)

    def test_single_store_empty_call_returns_66_and_preserves_node(self):
        body = self.section('BTNullHeadControl', True)
        for text in ['V293_owned_record_cell_update', 'V293_tcb_fresh_nine_avoiding',
                     'V293_OS_TCBInit_empty_call_return', 'exact Store', 'exact Exec', 'exact Final']:
            self.assertIn(text, body)
        observable = self.probe.split('Definition BTEmptyControl', 1)[1].split('Lemma BTNullHeadControl', 1)[0]
        for text in ['store(Tptr V293_tcb_type)M(95%positive,0%Z)Vnull=Some Mn',
                     'sfexec 205%Z BTArguments', 'Int.repr 66',
                     '82%positive,50%Z)=Some(Vint32 Int.zero)', '::BTFreeTail']:
            self.assertIn(text, observable)

    def test_positive_and_control_use_same_initialized_memory(self):
        body = self.section('BTSameMemoryControl', True)
        for text in ['BTAtHook ks M /\\ BTEmptyControl ks M', 'BTActualInitialization',
                     'apply BTEntryToFirstHook;exact Entry', 'apply BTNullHeadControl;exact Entry']:
            self.assertIn(text, body)
        self.assertIn('not a determinism or all-runs theorem', self.probe)

    def test_stable_compiles_and_explicit_bounded_claims(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('proof', SOURCE), ('probe', PROBE)]:
            label = stable[kind]
            row = json.loads((D / (label + '.json')).read_text())
            data = (R / path).read_bytes()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256(data).hexdigest())
            self.assertEqual(data, (D / (label + '.v.snapshot.txt')).read_bytes())
        self.assertEqual(len(json.loads((D / 'protocol.json').read_text())['prospective_checks']), 5)
        doc = (R / 'audit/STAGE133_BOOT_TCB_ENTRY.md').read_text()
        for text in ['单因素', '同一份返回内存', '不是完整 OSTaskCreateExt', '没有用空函数代替Hook',
                     '存在性轨迹', 'GoodI', 'WFIFun', 'GOOD_OS', 'uCOS3', '423']:
            self.assertIn(text, doc)
