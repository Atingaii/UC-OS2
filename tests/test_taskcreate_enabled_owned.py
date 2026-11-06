"""开启中断的任务创建受限整函数契约：结构回归，语义由 Coq 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskCreateEnabledOwned.v'
PROBE = 'audit/probes/V293TaskCreateEnabledOwnedProbe.v'
D = ROOT / 'audit/logs/stage114-enabled-owned-taskcreate'


class TaskCreateEnabledOwnedTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / SOURCE).read_text()
        self.probe = (ROOT / PROBE).read_text()

    def test_no_holes_new_axioms_or_audit_dependency(self):
        for content in [self.source, self.probe]:
            self.assertNotRegex(content, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
            self.assertNotIn('CertiOS.audit.', content)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

    def test_public_contract_uses_standard_builders_not_execution_oracle(self):
        public = self.source.split('Theorem V293_OSTaskCreateExt_enabled_owned_contract :')[1].split('Proof.')[0]
        self.assertEqual(public.count('InfRules '), 1)
        self.assertNotRegex(public, r'\b(?:evalval|evaladdr|load|loststep|sfexec|WFIFun)\b')
        for token in ['BuildPreI P creator vl lg', 'BuildRetI P creator vl lg',
                      'V293_CreateExt_function 92%Z 99%Z 97%Z', 'Spec hook=Some', 'Spec f=Some',
                      'p<13 -> Aisr ir ** invlth_isr I', 'V293_create_owned_pool']:
            self.assertIn(token, public)
        self.assertNotIn('Amapsto(bf', public)

    def test_original_body_is_connected_from_cpu_and_real_guards(self):
        body = self.source.split('Theorem V293_OSTaskCreateExt_enabled_owned_body :')[1]
        for token in ['rewrite V293_create_owned_empty_tail_source', 'apply V293_create_enabled_cpu',
                      'V293_create_enabled_priority', 'V293_create_owned_initial_enter',
                      'V293_create_owned_acquired_guards', 'V293_create_owned_initial_exit',
                      'V293_OSTaskCreateExt_owned_empty_critical_tail', 'destruct v;try discriminate',
                      'apply pfalse_rule']:
            self.assertIn(token, body)
        self.assertIn('V293_create_bad_priority', body)
        self.assertIn('V293_create_occupied_priority', body)

    def test_comparison_reads_reserved_half_or_other_full_without_upgrade(self):
        guard = self.source.split('Lemma V293_create_owned_acquired_guards :')[1].split('Qed.')[0]
        for token in ['rule_type_val_match(Tptr V293_tcb_type)v=true', 'val_eq v Vnull',
                      'V293_reservation_permission(br,Int.zero)v', 'mapstoval_load', 'SlotRead']:
            self.assertIn(token, guard)
        self.assertNotIn('V293_reservation_join_owner', guard)
        self.assertIn('V293_create_owned_acquired bp bc table bn br p cpu v K F', self.source)

    def test_post_exposes_42_40_before_and_66_after_with_all_locals(self):
        post = self.source.split('Definition V293_create_owned_post ')[1].split('Definition ')[0]
        self.assertIn('result=Some(Vint32(Int.repr 42)) \/ result=Some(Vint32(Int.repr 40))', post)
        self.assertIn('result=Some(Vint32(Int.repr 66))', post)
        self.assertIn('Rbefore', post)
        self.assertIn('Rafter', post)
        for token in ['V293_create_internal_post_cells', 'V293_create_internal_domain',
                      'V293_create_slot_global_views', 'V293_create_slot_drop_views']:
            self.assertIn(token, self.source)

    def test_single_inv_and_finite_spec_check_full_callee_and_caller(self):
        self.assertEqual(len(re.findall(r'^Definition \w+ : Inv :=', self.probe, re.M)), 1)
        self.assertEqual(self.probe.count('InfRules(EOSpec cs)sd V293_witness_li EOInv'), 2)
        for name in ['EOBuilders', 'EOCalleeCheckedSameSpec', 'EOEnabledBuilders', 'EOEnabledCheckedSameSpec']:
            self.assertRegex(self.probe, r'(?:Lemma|Theorem) ' + name + r' :')
        self.assertIn('Z.eq_dec f 500%Z', self.probe)
        self.assertIn('Z.eq_dec f 600%Z', self.probe)
        self.assertIn('Z.eq_dec f 700%Z', self.probe)
        self.assertIn('V293_OSTaskCreateExt_enabled_owned_contract', self.probe)

    def test_literal_enabled_caller_has_no_shared_bytes_and_compatible_pool(self):
        self.assertIn('(true,nil,cs)', self.probe)
        self.assertIn('Theorem EOEnabledEntryLiteral : EOState EOLE EOEntryMemory nil |= EOEnabledPre nil.', self.probe)
        memory = self.probe.split('Definition EOEntryMemory :=')[1].split('Lemma ')[0]
        for name in ['101', '109', '108', '205', '206', '207', '208', '204', '209', '201', '202', '203']:
            self.assertIn('EOEntryLocal' + name, memory)
        for token in ['EOFree', 'EOSlot', 'EOCounter']:
            self.assertNotIn(token, memory)
        for name in ['EOExactDomain', 'EOCallerHasNoSharedBytes', 'EOEnabledSharedCompatible',
                     'EOSameInvariantFreeReservedOther', 'EOComparisonReadNeedsBytes']:
            self.assertRegex(self.probe, r'(?:Lemma|Theorem) ' + name + r' :')

    def test_stable_compiles_hashes_and_prospective_protocol(self):
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
        self.assertIn('not production global Inv/WFIFun/init/GOOD_OS/uCOS3', protocol['limitations'])


if __name__ == '__main__':
    unittest.main()
