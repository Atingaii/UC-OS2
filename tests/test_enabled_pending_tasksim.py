"""IE=true pending 的结构与证据回归；语义结论由原 Coq 内核核查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage274-enabled-pending-tasksim'
PROD = 'certiucos/v293/proofs/V293EnabledPendingTaskSim.v'
PROBE = 'audit/probes/V293EnabledPendingTaskSimProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class EnabledPendingTaskSimTests(unittest.TestCase):
    def test_old_inputs_and_single_registration(self):
        for p, h in read('baseline.json')['files'].items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d']:
                self.assertEqual(sha(R / p), h, p)
        project = (R / '_CoqProject').read_text().splitlines()
        self.assertEqual(project.count(PROD), 1)
        self.assertNotIn(PROBE, project)
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h, p)

    def test_quantified_shared_and_external_frames(self):
        s = (R / PROD).read_text()
        self.assertNotIn('CertiOS.audit', s)
        self.assertNotRegex(s, r'(?m)^Definition ')
        body = theorem(s, 'V293_enabled_cstep_TaskSim')
        for term in ['forall Mf Mall,join M Mf Mall', 'join M\' Mf Mall\'',
                     'map_join_assoc JS JF', 'inv_ncare_le', 'exists Ms;exists O;exists Os',
                     'V293_pending_cstep_successor', 'inversion Bad']:
            self.assertIn(term, body)
        self.assertNotIn('V293_pending_shared_empty', body)
        self.assertEqual(len(re.findall(r'^ - ', body, re.M)), 7)
        bridge = theorem(s, 'V293_enabled_excrit_TaskSim')
        for term in ['join Mt Ms M', 'join Ot Os O', '(false,nil,true::ci)', '(true,nil,ci)',
                     'V293_pending_shared_empty', 'exists Ms;exists Ot;exists Os', 'exact AbsPartition', 'exact Shared']:
            self.assertIn(term, bridge)
        self.assertEqual(len(re.findall(r'^ - ', bridge, re.M)), 7)

    def test_public_interface_and_owned_suffix(self):
        s = (R / PROD).read_text()
        self.assertEqual(re.findall(r'^Theorem (\w+)\s*:', s, re.M), ['V293_enabled_pending_TaskSim'])
        public = theorem(s, 'V293_enabled_pending_TaskSim')
        stmt = public.split('Proof.', 1)[0]
        for term in ['(false,nil,true::ci)', 'Amapsto(b,0%Z)Tint32 true v **(Core **CurTid t)',
                     '(RDYINV G t **LINV V293_shared_li t nil)']:
            self.assertIn(term, stmt)
        pre = stmt.split(' TaskSim', 1)[0]
        for term in ['InitTaskSt', 'TaskSim', 'ProgSim', 'free Tint32', 'V293_global_steps']:
            self.assertNotIn(term, pre)
        for term in ['V293_enabled_excrit_TaskSim', 'V293_enabled_return_suffix', 'V293_return_enabled_INV']:
            self.assertIn(term, public)
        suffix = theorem(s, 'V293_enabled_return_suffix')
        self.assertNotIn('Core', suffix)
        for term in ['free_mono', 'join_free', 'V293_tick_free_owned', 'V293_return_client_coinduction']:
            self.assertIn(term, suffix)

    def test_snapshot_is_not_enabled_entry_reachability(self):
        s = (R / PROBE).read_text()
        self.assertIn('PTnonvacuous', theorem(s, 'EPnonvacuous'))
        toggle = theorem(s, 'EPtoggle')
        self.assertIn('good_inv_prop', toggle)
        self.assertIn('V293_enabled_pending_TaskSim', toggle)
        self.assertNotIn('exact OldSim', toggle)
        for term in ['join Mt\' Ms Mt', 'join Ot\' Os Ot', 'V293_return_enabled_INV', 'V293_enabled_return_suffix']:
            self.assertIn(term, theorem(s, 'EPtransfer'))
        for term in ['free Tint32 98%positive(emp:mem)=None', 'forall R:asrt,~', 'free_mono', 'discriminate Impossible']:
            self.assertIn(term, theorem(s, 'EPowned_free_boundary'))
        self.assertIn('PTsaved_stack_boundary', theorem(s, 'EPsaved_stack_boundary'))
        doc = (R / 'audit/STAGE274_ENABLED_PENDING_TASKSIM.md').read_text()
        for term in ['Core 不复制', '任意兼容共享 INV', '没有证明 true 快照从原完整入口可达',
                     '所有权分区边界', '这不是整核证明', 'uCOS3 未开始', 'ADR-0010']:
            self.assertIn(term, doc)

    def test_stable_compiles_and_recursive_trust(self):
        roots = []
        for p in [PROD, PROBE]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', s, re.M)]
        self.assertEqual(len(roots), 11)
        for p, labels in read('stable-compiles.json').items():
            self.assertEqual(len(labels), 2)
            for n in labels:
                row = read(n + '.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
                self.assertEqual(row['source_sha256'], sha(R / p))
        t = read('trust.json')
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 11)
        self.assertEqual(list(read('assumptions-by-root.json')), roots)
        self.assertTrue(all(row['exit'] == 0 for row in t['commands']))
        self.assertLessEqual(set(t['assumptions']), {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
