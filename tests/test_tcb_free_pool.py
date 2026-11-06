"""TCB 动态取池的结构回归；不替代 Coq 的语义检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TCBFreePool.v'
PROBE = 'audit/probes/V293TCBFreePoolProbe.v'
D = ROOT / 'audit/logs/stage115-tcb-free-pool'


class TCBFreePoolTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / SOURCE).read_text()
        self.probe = (ROOT / PROBE).read_text()

    def test_no_holes_axioms_or_production_audit_dependencies(self):
        for content in [self.source, self.probe]:
            self.assertNotRegex(content, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
            self.assertNotIn('CertiOS.audit.', content)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

    def test_node_full_layout_has_every_byte_once(self):
        layout = self.source.split('Definition V293_tcb_free_payload_cells ')[1].split('Definition ')[0]
        rows = re.findall(r'\(\(b,\(base\+(\d+)\)%Z\),(Tptr \w+|Tcom_ptr \d+%Z|Tint\d+)\)', layout)
        self.assertEqual(len(rows), 22)
        covered = list(range(20, 24))
        for off, tp in rows:
            width = {'Tint8': 1, 'Tint16': 2, 'Tint32': 4}.get(tp, 4)
            covered.extend(range(int(off), int(off) + width))
        self.assertEqual(sorted(covered), list(range(56)))

    def test_dynamic_chain_not_frozen_head_or_successor_snapshot(self):
        chain = self.source.split('Fixpoint V293_tcb_free_chain ')[1].split('Lemma ')[0]
        for token in ['Vnull=>Aemp', 'O=>Afalse', 'EX next:val', 'true next',
                      'V293_tcb_free_chain n next', 'V293_tcb_free_chain 13 head',
                      'Int.unsigned offset+55<=Int.max_unsigned']:
            self.assertIn(token, chain)
        for name in ['chain_precise', 'pool_precise', 'chain_weaken', 'pool_good', 'pool_isr']:
            self.assertIn('Lemma V293_tcb_free_' + name + ' :', self.source)

    def test_closed_pop_interface_has_no_suffix_or_load_oracle(self):
        public = self.source.split('Theorem V293_OS_TCBInit_free_pop_transfer :')[1].split('Proof.')[0]
        self.assertEqual(public.count('InfRules '), 1)
        self.assertNotRegex(public, r'\b(?:evalval|evaladdr|load|loststep|sfexec|WFIFun)\b')
        for token in ['V293_TCBInit_pop 91%Z 108%Z', '(sprim excrit)',
                      'V293_tcb_free_node b off next ** R', 'EX next:val']:
            self.assertIn(token, public)
        self.assertNotIn('success_suffix', public)

    def test_whole_body_remains_explicitly_conditional_on_success(self):
        public = self.source.split('Theorem V293_OS_TCBInit_free_body_with_success :')[1].split('Proof.')[0]
        self.assertEqual(public.count('InfRules '), 2)
        for token in ['V293_TCBInit_function_body hi hc', 'forall b off next',
                      'V293_TCBInit_fields 108%Z 101%Z', 'V293_TCBInit_success_suffix hi hc',
                      'r(Some(Vint32(Int.repr 66)))']:
            self.assertIn(token, public)
        body = self.source.split('Theorem V293_OS_TCBInit_free_body_with_success :')[1]
        for token in ['V293_tcb_enabled_cpu', 'V293_tcb_free_enter', 'V293_tcb_free_pointer',
                      'V293_tcb_free_guard_eval', 'V293_tcb_free_return_pool', 'apply rete_rule']:
            self.assertIn(token, body)

    def test_same_inv_empty_two_changed_tail_with_actual_input(self):
        self.assertEqual(len(re.findall(r'^Definition \w+ : Inv :=', self.probe, re.M)), 1)
        for name in ['FPSameInvariantEmptyTwo', 'FPSameInvariantChangedTail', 'FPWholeEnabledLiteral',
                     'FPActualPopInput', 'FPPopTransferChecked', 'FPTailNoPoppedBytes']:
            self.assertRegex(self.probe, r'(?:Lemma|Theorem) ' + name + r' :')
        self.assertIn('apply V293_OS_TCBInit_free_pop_transfer', self.probe)
        self.assertIn('apply FPOnePool', self.probe)

    def test_enabled_caller_does_not_hold_shared_bytes(self):
        caller = self.probe.split('Definition FPCaller ')[1].split('Lemma ')[0]
        self.assertNotRegex(caller, r'FP(?:HeadMemory|NodeMemory|Shared|ChainMemory)')
        for token in ['Lemma FPCallerNoShared :', 'b=401%positive \/ b=501%positive \/ b=502%positive',
                      'Vundef(Vint32(Int.repr 99))', 'FPWholePartition']:
            self.assertIn(token, self.probe)

    def test_physical_write_and_omission_are_distinguished(self):
        for name in ['FPActualHeadRead', 'FPActualNextRead', 'FPWrittenHeadRead', 'FPOmittedWriteDiffers']:
            self.assertRegex(self.probe, r'(?:Lemma|Theorem) ' + name + r' :')
        self.assertIn('store(Tptr V293_tcb_type)FPPopInput(401%positive,0%Z)FPNext', self.probe)
        omitted = self.probe.split('Theorem FPOmittedWriteDiffers :')[1].split('Qed.')[0]
        self.assertIn('<>Some FPNext', omitted)
        self.assertIn('rewrite FPActualHeadRead. discriminate.', omitted)

    def test_stable_compiles_and_prospective_protocol(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('proof', SOURCE), ('probe', PROBE)]:
            label = stable[kind]
            row = json.loads((D / (label + '.json')).read_text())
            content = (ROOT / path).read_bytes()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(hashlib.sha256(content).hexdigest(), row['source_sha256'])
            self.assertEqual(content, (D / (label + '.v.snapshot.txt')).read_bytes())
        self.assertLessEqual((D / 'protocol.json').stat().st_mtime_ns,
                             (D / 'proof01.v.snapshot.txt').stat().st_mtime_ns)
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertIn('gates94/1/1/1/1/0', protocol['unchanged'])
        self.assertIn('not WFIFun/GOOD_OS/K1K4/uCOS3', protocol['limitations'])


if __name__ == '__main__':
    unittest.main()
