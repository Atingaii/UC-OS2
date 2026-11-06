"""结构／证据身份检查；实际执行性质由独立 Coq 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage142-ready-full-call'
PROOF = 'certiucos/v293/proofs/V293ReadyFullCall.v'
PROBE = 'audit/probes/V293ReadyFullCallProbe.v'


class ReadyFullCallTests(unittest.TestCase):
    def setUp(self):
        self.proof, self.probe = [(R / p).read_text() for p in (PROOF, PROBE)]

    def section(self, name, text):
        return text.split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_registered_hole_free_sources(self):
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(PROOF), 1)
        self.assertNotIn('CertiOS.audit.', self.proof)
        for s in (self.proof, self.probe):
            self.assertNotRegex(s, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertEqual(sum(len(re.findall(r'^(?:Lemma|Theorem) \w+\s*:', s, re.M))
                             for s in (self.proof, self.probe)), 18)

    def test_real_allocation_and_original_initialization(self):
        body = self.section('V293_sched_call_enter', self.proof)
        for s in ('fresh M b', 'sfexec f nil nil', 'sfexec_step', 'salloclv_step',
                  'sallocend_step', 'V293_success_assign_zero', 'V293_sched_control_exact'):
            self.assertIn(s, body)
        caller = self.section('FCcaller', self.probe)
        for s in ('V293_cpu_release', 'fresh Mbase 98%positive', 'FCcpu_outside', 'V293_cpu_recreate'):
            self.assertIn(s, caller)
        self.assertIn('snpcall_step', self.section('FCenter', self.probe))

    def test_return_releases_four_bytes_and_restores_caller(self):
        body = self.section('V293_sched_call_return', self.proof)
        for s in ('sret_step', 'sfree_step', 'sfreeend_step', '((ge,caller,Mf),ir,aux)'):
            self.assertIn(s, body)
        for s in ('(0<=i<4)%Z', 'V293_freeb_removed', 'V293_freeb_outside'):
            self.assertIn(s, self.section('V293_cpu_release', self.proof))
        for s in ('CGlocal_ready false enabled ci', 'V293_sched_control_exit',
                  'V293_sched_call_return', 'Some (Vint32 Int.mone)', 'Some (V293_byteval 4)'):
            self.assertIn(s, self.section('FCno_switch_return', self.probe))
        self.assertIn('CGmemory ct different ni nl', self.section('FCblocked_return', self.probe))

    def test_actual_switch_preserves_pending_real_call_frame(self):
        for s in ('FCenter OwnershipWaiting true', 'CGlocal_ready true enabled ci', 'FCpending'):
            self.assertIn(s, self.section('FCready_to_switch', self.probe))
        body = self.section('FCswitch_after_call', self.probe)
        for s in ('FCready_to_switch', 'V293_ready_switch_step', 'Mtail', 'lpstep',
                  'Amapsto (98%positive,0%Z)', 'Some (false,nil,enabled::ci)', 'Some (false,nil,nil)'):
            self.assertIn(s, body)
        self.assertNotIn('V293_global_steps', body)

    def test_free_only_ablation_reaches_both_returns(self):
        body = self.section('FCfree_ablation', self.probe)
        for s in ('FCenter OwnershipReady false', 'sfree ((98%positive,Tint32)::nil)',
                  'sfree nil None', 'sret_step', 'sfree_step', 'sfreeend_step',
                  'get Mf (98%positive,i)=None', 'load Tint32 Mtail (98%positive,0%Z)',
                  'b<>98%positive -> get Mf (b,i)=get Mtail (b,i)'):
            self.assertIn(s, body)

    def test_stable_source_identity_and_prospective_protocol(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('proof', PROOF), ('probe', PROBE)]:
            label = stable[kind]
            row = json.loads((D / (label + '.json')).read_text())
            data = (R / path).read_bytes()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256(data).hexdigest())
            self.assertEqual(data, (D / (label + '.v.snapshot.txt')).read_bytes())
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertEqual(len(protocol['checks']), 5)
        self.assertEqual(len(protocol['limits']), 4)

    def test_claims_do_not_upgrade_to_kernel_or_full_global_proof(self):
        doc = (R / 'audit/STAGE142_READY_FULL_CALL.md').read_text()
        for s in ('不是完整全局闭包', '存在性、无交错', '初始化可达性', '行政性局部释放',
                  'OSPrioCur', '生产全局语义 Inv', 'GOOD_OS', 'K1–K4', 'uCOS3 未开始',
                  '失败 ID 集合', '94/1/1/1/1/0'):
            self.assertIn(s, doc)


if __name__ == '__main__':
    unittest.main()
