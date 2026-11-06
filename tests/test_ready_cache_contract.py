"""结构/身份回归；语义有效性由编译与 coqchk 验证。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage144-ready-cache-contract'
PROOF = 'certiucos/v293/proofs/V293ReadyCacheContract.v'
PROBE = 'audit/probes/V293ReadyCacheContractProbe.v'


class ReadyCacheContractTests(unittest.TestCase):
    def setUp(self):
        self.proof, self.probe = [(R / p).read_text() for p in (PROOF, PROBE)]

    def section(self, name, text):
        return text.split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_registered_no_new_rules_or_holes(self):
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(PROOF), 1)
        self.assertNotIn('CertiOS.audit.', self.proof)
        for s in (self.proof, self.probe):
            self.assertNotRegex(s, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
            self.assertNotRegex(s, re.compile(r'^Inductive ', re.M))
        self.assertEqual(sum(len(re.findall(r'^(?:Lemma|Theorem) \w+\s*:', s, re.M))
                             for s in (self.proof, self.probe)), 7)

    def test_generic_priority_characterization(self):
        body = self.section('V293_cache_current_iff', self.proof)
        for s in ('forall tasks current M cache cached selected', 'cached<13',
                  '<-> cached=selected', 'V293_priority_repr_injective'):
            self.assertIn(s, body)
        self.assertNotIn('OwnershipReady', self.proof)
        self.assertIn('~V293_cache_current', self.section('V293_cache_current_mismatch', self.proof))

    def test_cache_store_constructed_not_assumed(self):
        body = self.section('V293_ready_cache_write', self.proof)
        statement = body.split('Proof.', 1)[0]
        self.assertEqual(statement.count('store Tint8'), 1)
        self.assertIn('exists Mw, store Tint8', statement)
        for s in ('V293_owned_record_cell_update', 'V293_byte_type',
                  'V293_storebytes_outside', 'c<>cache \/ i<>0%Z'):
            self.assertIn(s, body)

    def test_original_switch_and_actual_task_map(self):
        body = self.section('V293_ready_switch_cache', self.proof)
        for s in ('V293_ready_switch_step', 'lpstep', 'store (Tptr tp)',
                  'get O abstcblsid=Some (abstcblist tasks)',
                  'get (set O curtid (oscurt next)) abstcblsid',
                  'Some (V293_byteval cached)', '<-> cached=selected'):
            self.assertIn(s, body)
        self.assertNotIn('cache<>bc', body)

    def test_old_complete_call_reaches_gap(self):
        body = self.section('SCcall_gap', self.probe)
        for s in ('FGswitch enabled ci ip cst', 'sfexec 113%Z nil nil', 'V293_global_steps',
                  'Some (Vptr OwnershipReady)', 'Some (V293_byteval 6)',
                  'V293_cache_current_mismatch'):
            self.assertIn(s, body)

    def test_ablation_both_switch_and_only_one_byte_differs(self):
        body = self.section('SCwrite_switch_ablation', self.probe)
        self.assertEqual(body.count('lpstep'), 2)
        self.assertEqual(body.count('V293_ready_switch_cache'), 2)
        for s in ('CGlocal_ready true enabled ci', 'V293_ready_cache_write',
                  'store Tint8 Mtail', 'SameCurrent', 'V293_storebytes_nth',
                  'get Mpositive (c,i)=get Mnegative (c,i)', 'i<>0%Z',
                  'apply (proj2 PIff)', 'apply (proj1 NIff)'):
            self.assertIn(s, body)

    def test_stable_identity_prospective_protocol(self):
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

    def test_claims_bounded(self):
        doc = (R / 'audit/STAGE144_READY_CACHE_CONTRACT.md').read_text()
        for s in ('端口声明', '不是端口实现已修复', '不是新生产 Inv', '初始化可达性',
                  '存在性、无交错', '没有正例完整调用轨迹', 'GOOD_OS', 'K1–K4',
                  'uCOS3 未开始', '失败 ID 集合', '94/1/1/1/1/0'):
            self.assertIn(s, doc)


if __name__ == '__main__':
    unittest.main()
