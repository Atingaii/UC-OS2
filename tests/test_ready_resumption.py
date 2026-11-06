"""结构和身份回归；实际语义由独立编译与 coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage145-ready-resumption'
PROOF = 'certiucos/v293/proofs/V293ReadyResumption.v'
PROBE = 'audit/probes/V293ReadyResumptionProbe.v'


class ReadyResumptionTests(unittest.TestCase):
    def setUp(self):
        self.proof, self.probe = [(R / p).read_text() for p in (PROOF, PROBE)]

    def section(self, name, text):
        return text.split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_registration_and_no_new_rules_or_holes(self):
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(PROOF), 1)
        self.assertNotIn('CertiOS.audit.', self.proof)
        self.assertNotIn('OwnershipReady', self.proof)
        for s in (self.proof, self.probe):
            self.assertNotRegex(s, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
            self.assertNotRegex(s, re.compile(r'^Inductive ', re.M))
        self.assertEqual(sum(len(re.findall(r'^(?:Lemma|Theorem) \w+\s*:', s, re.M))
                             for s in (self.proof, self.probe)), 9)

    def test_bound_continuation_classification(self):
        body = self.section('V293_bound_continuation_inos', self.proof)
        for s in ('po f=Some', 'callcont', 'InOS', 'pumerge'):
            self.assertIn(s, body)
        statement = body.split('Proof.', 1)[0]
        self.assertEqual(statement.count('InOS'), 1)

    def test_exit_constructs_free_and_restores_caller(self):
        body = self.section('V293_sched_resume_return', self.proof)
        statement = body.split('Proof.', 1)[0]
        self.assertEqual(statement.count('free Tint32'), 1)
        for s in ('exists Mf', 'V293_global_steps', 'V293_sched_global_return',
                  'set les t caller', 'set aus t (enabled,si,ci)', 'get Mf (b,i)=None'):
            self.assertIn(s, body)

    def test_actual_switch_back_then_exit(self):
        body = self.section('V293_sched_switch_resume_return', self.proof)
        for s in ('runner<>victim', 'get T victim=', 'get les victim=', 'get aus victim=',
                  'V293_owned_record_cell_update', 'pswitch_step',
                  'V293_sched_resume_return', 'exact Step|exact Resume', 'V293_storebytes_outside'):
            self.assertIn(s, body)
        self.assertNotIn('OwnershipWaiting', body)

    def test_nonempty_source_roundtrip_same_heap(self):
        body = self.section('RProundtrip', self.probe)
        for s in ('RPentry enabled ci ip cst', 'RPprepare enabled ci ip cst Mfirst After',
                  'sfexec 113%Z nil nil', 'exact Prefix', 'exact Prepare|exact Resume',
                  'store (Tptr V293_tcb_type) Mb', 'free Tint32 98%positive Ms=Some Mf',
                  'get Mf (98%positive,i)=None', 'Some (V293_byteval 6)'):
            self.assertIn(s, body)
        self.assertIn('sig OwnershipReady (curs RPcontext,(kenil,FCouter))', self.probe)
        self.assertIn('V293_priority_repr_injective', self.section('RPtable_waiting', self.probe))

    def test_delete_top_both_sides_actually_return(self):
        body = self.section('V293_sched_resume_stack_ablation', self.proof)
        self.assertEqual(body.count('V293_sched_resume_return'), 2)
        self.assertEqual(body.count('V293_global_steps'), 2)
        for s in ('enabled::negb enabled::ci', 'set aus t (active,si,negb enabled::ci)',
                  'set aus t (enabled,si,negb enabled::ci)',
                  'set aus t (negb enabled,si,ci)', 'assert (Mn=Mf) by congruence',
                  'destruct enabled;discriminate'):
            self.assertIn(s, body)

    def test_stable_identity_and_prospective_protocol(self):
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
        self.assertIn('删除恢复栈顶', protocol['checks'][3])

    def test_bounded_claims(self):
        doc = (R / 'audit/STAGE145_READY_RESUMPTION.md').read_text()
        for s in ('环境 fixture', '仍然 blocked', '条件资源契约', '同一实际物理内存',
                  '不是生产调度器选择或唤醒', 'production Inv', '初始化可达性',
                  'GOOD_OS', 'K1–K4', 'uCOS3 未开始', '失败 ID 集合', '94/1/1/1/1/0'):
            self.assertIn(s, doc)


if __name__ == '__main__':
    unittest.main()
