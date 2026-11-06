"""接口与证据身份回归；运行语义由 Coq 根定理而非字符串检查证明。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage143-ready-call-global'
PROOF = 'certiucos/v293/proofs/V293ReadyCallGlobal.v'
PROBE = 'audit/probes/V293ReadyCallGlobalProbe.v'


class ReadyCallGlobalTests(unittest.TestCase):
    def setUp(self):
        self.proof, self.probe = [(R / p).read_text() for p in (PROOF, PROBE)]

    def section(self, name, text):
        return text.split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_registered_original_rules_no_holes(self):
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(PROOF), 1)
        self.assertNotIn('CertiOS.audit.', self.proof)
        for s in (self.proof, self.probe):
            self.assertNotRegex(s, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
            self.assertNotRegex(s, re.compile(r'^Inductive ', re.M))
        self.assertEqual(sum(len(re.findall(r'^(?:Lemma|Theorem) \w+\s*:', s, re.M))
                             for s in (self.proof, self.probe)), 13)
        for s in ('V293_global_steps', 'pt_step', 'inapi_step', 'exact Step'):
            self.assertIn(s, self.section('V293_loststep_global_single', self.proof))

    def test_actual_global_entry_allocation_initialization(self):
        body = self.section('V293_sched_global_enter', self.proof)
        for s in ('sfexec f nil nil', 'fresh M b', 'store Tint32 (allocb M b 0%Z 4)',
                  'sfexec_step', 'salloclv_step', 'sallocend_step',
                  'V293_success_assign_zero', 'V293_local_steps_global'):
            self.assertIn(s, body)
        probe = self.section('FGenter', self.probe)
        for s in ('FCcaller', 'sfexec 113%Z nil nil', 'RTle Mbase', '(kenil,kstop)',
                  'fresh Mbase 98%positive', 'V293_sched_global_enter'):
            self.assertIn(s, probe)
        self.assertNotIn('kcall 112', self.probe)

    def test_classification_from_actual_call_binding(self):
        body = self.section('V293_bound_call_inos', self.proof)
        for s in ('po f=Some (tau,d1,d2,body)', 'kcall f body caller ks', 'InOS', 'rewrite H'):
            self.assertIn(s, body)
        for name in ('V293_sched_global_free', 'V293_sched_global_restore'):
            self.assertIn('V293_bound_call_inos', self.section(name, self.proof))
        body = self.section('V293_sched_global_enter', self.proof)
        for s in ('goodks', 'Program', 'Bind', 'kcall f body caller ks'):
            self.assertIn(s, body)

    def test_complete_no_switch_return_and_guard_blocked_return(self):
        for s in ('V293_global_steps', 'sfexec 113%Z nil nil', 'SKIP,(kenil,kstop)',
                  'RTle Mf', '(0<=i<4)%Z', 'Some (Vint32 Int.mone)',
                  'Some (V293_byteval 4)', 'V293_sched_global_restore'):
            self.assertIn(s, self.section('FGno_switch', self.probe))
        for s in ('(Nat.eqb ni 0 && Nat.eqb nl 0)=false', 'RTle Mbase', 'CGlocal_blocked',
                  'V293_local_steps_global', 'V293_sched_global_return'):
            self.assertIn(s, self.section('FGblocked', self.probe))

    def test_actual_global_switch_same_intermediate_memory(self):
        body = self.section('FGswitch', self.probe)
        for s in ('V293_global_steps', 'FGenter OwnershipWaiting true',
                  'CGlocal_ready true enabled ci', 'V293_ready_switch_step',
                  'store (Tptr V293_tcb_type) Mtail', 'FCpending',
                  'Some (V293_byteval 6)', 'Amapsto (98%positive,0%Z)',
                  'Some (false,nil,enabled::ci)', 'Some (false,nil,nil)'):
            self.assertIn(s, body)
        self.assertNotIn('FGno_switch', body)

    def test_restore_only_ablation_both_suffixes_return(self):
        body = self.section('FGrestore_ablation', self.probe)
        self.assertEqual(body.count('V293_global_steps'), 3)
        self.assertEqual(body.count('V293_sched_global_restore'), 2)
        for s in ('FGno_switch_free', 'sfree nil None', 'kcall 113%Z CGbody CGle kstop',
                  'RTle Mf (enabled,nil,ci)', 'CGle Mf (enabled,nil,ci)',
                  'get Mf (98%positive,i)=None', 'get RTle 104%Z=Some',
                  'get CGle 104%Z=None', 'RTle<>CGle'):
            self.assertIn(s, body)

    def test_stable_compile_identity_and_prospective_protocol(self):
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

    def test_claims_are_bounded(self):
        doc = (R / 'audit/STAGE143_READY_CALL_GLOBAL.md').read_text()
        for s in ('sfexec', '不是 client 侧 scall', '存在性、无交错',
                  '初始化可达性', '行政性调用帧', 'OSPrioCur', '生产全局语义 Inv',
                  'GOOD_OS', 'K1–K4', 'uCOS3 未开始', '失败 ID 集合', '94/1/1/1/1/0'):
            self.assertIn(s, doc)


if __name__ == '__main__':
    unittest.main()
