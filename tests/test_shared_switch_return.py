"""共享切换返回回归；结构检查不替代 Coq 内核验证。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage270-shared-switch-return'
PROD = 'certiucos/v293/proofs/V293OSIntExitSharedReturn.v'
PROBE = 'audit/probes/V293SharedSwitchReturnProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class SharedSwitchReturnTests(unittest.TestCase):
    def test_old_inputs_and_registration_delta(self):
        base = read('baseline.json')['files']
        for p, h in base.items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d']:
                self.assertEqual(sha(R / p), h, p)
        line = (PROD + '\n').encode()
        project = (R / '_CoqProject').read_bytes()
        self.assertEqual(project.count(line), 1)
        self.assertEqual(hashlib.sha256(project.replace(line, b'')).hexdigest(), base['_CoqProject'])
        self.assertNotIn(PROBE, project.decode())
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- shared-switch-return-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), base[p])
        identity = read('source-identity.json')
        for p, h in identity['files'].items():
            self.assertEqual(sha(R / p), h, p)
        lines = (R / 'csrc/upstream/v2.93.01/checkout/Source/os_core.c').read_text().splitlines()
        for n, anchor in identity['line_anchors'].items():
            self.assertEqual(lines[int(n) - 1].strip(), anchor)

    def test_production_real_execution_and_resources(self):
        src = (R / PROD).read_text()
        self.assertNotIn('CertiOS.audit', src)
        self.assertEqual(re.findall(r'^Theorem (\w+)\s*:', src, re.M), ['V293_int_exit_shared_switch_return'])
        body = theorem(src, 'V293_int_exit_shared_switch_return')
        statement = body.split('Proof.', 1)[0]
        premises = statement.split(' exists Ms Mf,', 1)[0]
        for term in ['lpstep', 'V293_global_steps', 'ProgSim', 'free Tint32', 'store(Tptr']:
            self.assertNotIn(term, premises)
        for term in ['V293_scheduler O victim', 'GoodInvAsrt R',
                     'get aus victim=Some(false,si,enabled::vci)',
                     'SWINVt(V293_ready_storage_inv',
                     'V293_ready_current_core br bg bp target tp cells cache **(CurTid victim **R)']:
            self.assertIn(term, statement)
        for term in ['V293_ready_storage_switch_step', 'V293_current_handoff_switch_highest_frame',
                     'V293_int_exit_pending_return', 'good_inv_prop', 'V293_shared_current_read']:
            self.assertIn(term, body)
        self.assertIn('CurTid t', theorem(src, 'V293_current_shared_open'))

    def test_independent_full_call_and_actual_stack_control(self):
        src = (R / PROBE).read_text()
        body = theorem(src, 'STfull_call_shared_return')
        premises = body.split('Proof.', 1)[0].split(' exists Mc Ms Mf,', 1)[0]
        self.assertEqual(premises.count('fresh('), 2)
        self.assertNotIn('V293_global_steps', premises)
        self.assertIn('FTto_switch', body)
        self.assertIn('STselected_return', body)
        control = theorem(src, 'STsaved_top_actual_ablation')
        statement = control.split('Proof.', 1)[0]
        self.assertEqual(statement.count('V293_global_steps'), 3)
        self.assertEqual(statement.count('|=STpost'), 2)
        self.assertIn('(true,nil,vci)', statement)
        self.assertIn('(false,nil,true::vci)', statement)
        self.assertEqual(control.count('destruct(STselected_return'), 2)
        for term in ['assert(Ms2=Ms)by congruence', 'assert(Mf2=Mf)by congruence',
                     't<>OwnershipReady', 'STaux_without_top']:
            self.assertIn(term, control)
        self.assertIn('SXnot_highest', theorem(src, 'STblocked_old_not_selected'))
        self.assertIn('memory_has_fresh_block', theorem(src, 'STnonvacuous'))
        self.assertIn('90%positive', theorem(src, 'STsaved_retained'))
        self.assertIn('V293_int_exit_shared_switch_return', theorem(src, 'STselected_return'))

    def test_stable_compiles_recursive_trust_and_protocol(self):
        roots = []
        for p in [PROD, PROBE]:
            src = (R / p).read_text()
            self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        for p, labels in read('stable-compiles.json').items():
            self.assertEqual(len(labels), 2)
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

    def test_claim_boundaries(self):
        text = (R / 'audit/STAGE270_SHARED_SWITCH_RETURN.md').read_text()
        for term in ['不是旧任务切出后再调度切回的完整共享循环', '共同 si', '目标 pending 已存在',
                     '不是初始化可达证明', '不是原外部 CPU-port', 'K1–K4', 'uCOS3 尚未开始',
                     '不是任务私有 LINV', '不是 ProgSim', '变体从共同到达的 switch 快照开始']:
            self.assertIn(term, text)
        self.assertEqual(read('protocol.json')['goal_status'], 'active')
        self.assertEqual(len(read('protocol.json')['prospective_tests']), 4)
