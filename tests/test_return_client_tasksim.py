"""实际返回 client TaskSim 的结构和证据回归；不替代 Coq 内核检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage272-return-client-tasksim'
PROD = 'certiucos/v293/proofs/V293ReturnClientTaskSim.v'
PROBE = 'audit/probes/V293ReturnClientTaskSimProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class ReturnClientTaskSimTests(unittest.TestCase):
    def test_original_inputs_and_registration(self):
        for p, h in read('baseline.json')['files'].items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d']:
                self.assertEqual(sha(R / p), h, p)
        project = (R / '_CoqProject').read_text().splitlines()
        self.assertEqual(project.count(PROD), 1)
        self.assertNotIn(PROBE, project)
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h, p)
        lines = (R / 'csrc/upstream/v2.93.01/checkout/Source/os_core.c').read_text().splitlines()
        for n, s in read('source-identity.json')['line_anchors'].items():
            self.assertEqual(lines[int(n) - 1].strip(), s)

    def test_original_constructor_and_exact_partition(self):
        src = (R / PROD).read_text()
        self.assertNotIn('CertiOS.audit', src)
        self.assertNotRegex(src, r'(?m)^Definition ')
        self.assertEqual(re.findall(r'^Theorem (\w+)\s*:', src, re.M), ['V293_return_client_TaskSim'])
        cofix = theorem(src, 'V293_return_client_coinduction')
        premise = cofix.split('Proof.', 1)[0].rsplit(' TaskSim', 1)[0]
        self.assertNotIn('InitTaskSt', premise)
        self.assertNotIn('TaskSim', premise)
        self.assertIn('CurLINV li t', premise)
        self.assertIn('P(o,O)', premise)
        self.assertIn('cofix CIH', cofix)
        self.assertIn('apply task_sim', cofix)
        self.assertEqual(len(re.findall(r'^ - ', cofix, re.M)), 7)
        self.assertIn('V293_skip_client_match_abort', cofix)
        body = theorem(src, 'V293_return_client_TaskSim')
        stmt = body.split('Proof.', 1)[0]
        for term in ['(forall i,ir i=false)', '(enabled=false ->gettopis si<=INUM)',
                     'LINV li t lg **R', 'join Mt Mf Mtail', 'join Ms Mtail M',
                     'join Ot Of Otail', 'join Os Otail O', 'Of,op)|=R',
                     '(fun s=>satp(fst s)(snd s)(RDYINV G t **LINV li t lg))t']:
            self.assertIn(term, stmt)
        for term in ['InitTaskSt', 'Atrue', 'ProgSim', 'V293_global_steps']:
            self.assertNotIn(term, stmt)
        self.assertEqual(stmt.count('TaskSim'), 1)
        self.assertIn('V293_current_return_invariants', body)
        self.assertIn('exact Frame', body)

    def test_actual_execution_and_boundaries(self):
        src = (R / PROBE).read_text()
        full = theorem(src, 'RTfull_call')
        premise = full.split(' exists Mc Ms Mf,', 1)[0]
        self.assertEqual(premise.count('fresh('), 2)
        for term in ['TaskSim', 'V293_global_steps', 'RTpacket', 'ProgSim']:
            self.assertNotIn(term, premise)
        for term in ['STfull_call_shared_return', 'STsaved_retained', 'SKIP,(kenil,kstop)', 'apply RTclose']:
            self.assertIn(term, full)
        control = theorem(src, 'RTsaved_top_actual_ablation')
        stmt = control.split('Proof.', 1)[0]
        self.assertEqual(stmt.count('V293_global_steps'), 3)
        self.assertEqual(stmt.count('RTpacket br bs'), 2)
        for term in ['STsaved_top_actual_ablation', 'exact Positive', 'exact Negative', 'exact Off', 'exact On']:
            self.assertIn(term, control)
        self.assertIn('enabled=false \/ ci<>nil', theorem(src, 'RTnot_initial'))
        for term in ['~IsEnd', 'cstep RCprogram', 'V293_skip_client_code']:
            self.assertIn(term, theorem(src, 'RTnonterminal_resume'))
        self.assertIn('STnonvacuous', theorem(src, 'RTnonvacuous'))
        close = theorem(src, 'RTclose')
        self.assertIn('STframe bs ==> LINV V293_shared_li OwnershipReady nil **STframe bs', close)
        self.assertIn('V293_switch_local_empty', close)

    def test_stable_compiles_recursive_trust_and_protocol(self):
        roots = []
        for p in [PROD, PROBE]:
            src = (R / p).read_text()
            self.assertNotRegex(src, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        self.assertEqual(len(roots), 10)
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
        self.assertEqual(t['roots_printed'], 10)
        self.assertEqual(list(read('assumptions-by-root.json')), roots)
        self.assertTrue(all(row['exit'] == 0 for row in t['commands']))
        self.assertLessEqual(set(t['assumptions']), {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])

    def test_scope_boundaries(self):
        doc = (R / 'audit/STAGE272_RETURN_CLIENT_TASKSIM.md').read_text()
        for s in ['不是整核', '不复制', '原任务仍 blocked', '不是目标任务私有 LINV',
                  '不是另一项实际执行消融', 'uCOS3 未开始', 'GOOD_OS', 'ADR-0010',
                  '不是把完整调用的实际终止 caller 改成非终止程序', 'pending 返回之前', '空局部候选']:
            self.assertIn(s, doc)
