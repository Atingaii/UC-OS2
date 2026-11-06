"""共享资源重封装回归；文本断言不替代 Coq 内核检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage269-exit-shared-reclose'
PROD = 'certiucos/v293/proofs/V293OSIntExitSharedReclose.v'
PROBE = 'audit/probes/V293ExitSharedRecloseProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class ExitSharedRecloseTests(unittest.TestCase):
    def test_old_inputs_and_registration_delta(self):
        base = read('baseline.json')['files']
        for p, h in base.items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d']:
                self.assertEqual(sha(R / p), h, p)
        project = (R / '_CoqProject').read_bytes()
        line = (PROD + '\n').encode()
        self.assertEqual(project.count(line), 1)
        self.assertEqual(hashlib.sha256(project.replace(line, b'')).hexdigest(), base['_CoqProject'])
        self.assertNotIn(PROBE, project.decode())
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- exit-shared-reclose-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), base[p])
        identity = read('source-identity.json')
        for p, h in identity['files'].items():
            self.assertEqual(sha(R / p), h, p)
        lines = (R / 'csrc/upstream/v2.93.01/checkout/Source/os_core.c').read_text().splitlines()
        for n, anchor in identity['line_anchors'].items():
            self.assertEqual(lines[int(n) - 1].strip(), anchor)

    def test_production_actual_path_shared_private_boundary(self):
        src = (R / PROD).read_text()
        self.assertNotIn('CertiOS.audit', src)
        self.assertEqual(re.findall(r'^Theorem (\w+)\s*:', src, re.M), ['V293_exit_boundary_shared_reclose'])
        body = theorem(src, 'V293_exit_boundary_shared_reclose')
        statement = body.split('Proof.', 1)[0]
        premises = statement.split(' exists bs next nh Me Ms Mf,', 1)[0]
        self.assertNotIn('ProgSim', statement)
        self.assertNotIn('V293_global_steps', premises)
        for term in ['V293_storage rest **R', 'GoodInvAsrt R',
                     'V293_ready_current_inv br bg bp target V293_tcb_type',
                     'Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **R',
                     'V293_cache_current tasks next Mf bc <-> sync=true']:
            self.assertIn(term, statement)
        for term in ['V293_OSIntExit_boundary_switch sync', 'V293_exit_shared_reclose',
                     'conj(V293_storage_good rest)Good', 'clear Held;sep auto']:
            self.assertIn(term, body)
        helper = theorem(src, 'V293_exit_shared_reclose')
        for term in ['V293_ready_storage_switch_resources', 'V293_current_switch_highest',
                     'V293_shared_no_abstract_frame']:
            self.assertIn(term, helper)

    def test_nonempty_storage_and_same_heap_actual_control(self):
        src = (R / PROBE).read_text()
        self.assertIn('Definition SRrest : list(addr*type) := [((99%positive,0%Z),Tint8)].', src)
        independent = theorem(src, 'SRcomplete_switch')
        statement = independent.split('Proof.', 1)[0]
        self.assertNotIn('->', statement.split(' exists ', 1)[0])
        self.assertNotIn('ProgSim', statement)
        self.assertIn('V293_exit_boundary_shared_reclose sync', independent)
        self.assertIn('(SRentry ci)', independent)
        control = theorem(src, 'SRcopy_ablation')
        statement = control.split('Proof.', 1)[0]
        self.assertEqual(statement.count('V293_global_steps'), 2)
        self.assertEqual(statement.count('SXmemory 1 6'), 2)
        self.assertEqual(statement.count('|=SRpost'), 2)
        self.assertNotIn('->', statement.split(' exists ', 1)[0])
        self.assertIn('~V293_cache_current OwnershipTasks OwnershipReady M1 96%positive', statement)
        self.assertEqual(control.count('destruct(SRcomplete_switch'), 2)
        self.assertIn('unfold SRpost,SRprivate in Held', theorem(src, 'SRprivate_canary'))

    def test_stable_compile_recursive_trust_and_frozen_protocol(self):
        roots = []
        for p in [PROD, PROBE]:
            src = (R / p).read_text()
            self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        for p, labels in read('stable-compiles.json').items():
            for label in labels:
                row = read(label + '.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
                self.assertEqual(row['source_sha256'], sha(R / p))
        t = read('trust.json')
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], len(roots))
        self.assertEqual(list(read('assumptions-by-root.json')), roots)
        self.assertTrue(all(c['exit'] == 0 for c in t['commands']))
        self.assertLessEqual(set(t['assumptions']),
                             {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])

    def test_claim_boundaries_disclosed(self):
        text = (R / 'audit/STAGE269_EXIT_SHARED_RECLOSE.md').read_text()
        for term in ['不是同一个完整全局 Inv', '不等于完整 Inv', '不是原外部 CPU-port',
                     '重封装通过不等于缓存正确', '初始化可达', 'K1–K4', 'uCOS3 尚未开始',
                     '不声称分配地址相同', '端点停在 switch 后']:
            self.assertIn(term, text)
        protocol = read('protocol.json')
        self.assertEqual(protocol['goal_status'], 'active')
        self.assertEqual(len(protocol['prospective_tests']), 3)
