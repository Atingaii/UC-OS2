"""原 INV/RDYINV 的结构及证据回归；不替代内核检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage271-return-invariant-split'
PROD = 'certiucos/v293/proofs/V293CurrentReturnInvariant.v'
PROBE = 'audit/probes/V293ReturnInvariantSplitProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class ReturnInvariantSplitTests(unittest.TestCase):
    def test_original_inputs_and_registration(self):
        base = read('baseline.json')['files']
        for p, h in base.items():
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

    def test_exact_existing_partition(self):
        src = (R / PROD).read_text()
        self.assertNotIn('CertiOS.audit', src)
        self.assertNotRegex(src, r'(?m)^Definition ')
        self.assertEqual(re.findall(r'^Theorem (\w+)\s*:', src, re.M), ['V293_current_return_invariants'])
        body = theorem(src, 'V293_current_return_invariants')
        stmt = body.split('Proof.', 1)[0]
        for term in ['(forall i,ir i=false)', '(enabled=false ->gettopis si<=INUM)',
                     '|=C **(CurTid t **R)', '|=(INV G **RDYINV G t) **R']:
            self.assertIn(term, stmt)
        for term in ['Atrue', 'GoodInvAsrt R', 'TaskSim', 'ProgSim', 'V293_global_steps']:
            self.assertNotIn(term, stmt)
        for term in ['destruct enabled', 'V293_return_enabled_INV',
                     'V293_return_disabled_INV_empty', 'V293_return_disabled_SWINV', 'exact Frame']:
            self.assertIn(term, body)
        enabled = theorem(src, 'V293_return_enabled_INV').split('Proof.', 1)[0]
        self.assertNotIn('gettopis', enabled)

    def test_full_execution_and_single_factor(self):
        src = (R / PROBE).read_text()
        full = theorem(src, 'IPfull_call')
        stmt = full.split('Proof.', 1)[0]
        premise = stmt.split(' exists Mc Ms Mf,', 1)[0]
        self.assertEqual(premise.count('fresh('), 2)
        self.assertNotIn('V293_global_steps', premise)
        self.assertNotIn('ProgSim', premise)
        for term in ['STfull_call_shared_return', 'STsaved_retained', 'apply IPclose']:
            self.assertIn(term, full)
        control = theorem(src, 'IPsaved_top_actual_ablation')
        stmt = control.split('Proof.', 1)[0]
        self.assertEqual(stmt.count('V293_global_steps'), 3)
        self.assertEqual(stmt.count('|=IPpost br bs'), 2)
        for term in ['STsaved_top_actual_ablation', 'exact Positive', 'exact Negative',
                     'apply IPclose;exact Off', 'apply IPclose;exact On']:
            self.assertIn(term, control)
        self.assertIn('STnonvacuous', theorem(src, 'IPnonvacuous'))
        self.assertIn('INV I ->gettopis si<=INUM', theorem(src, 'IPdisabled_top_bound'))
        self.assertIn('false,3::si,ci', theorem(src, 'IPout_of_range_rejected'))

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
        doc = (R / 'audit/STAGE271_RETURN_INVARIANT_SPLIT.md').read_text()
        for s in ['不是整核', '不复制', '原任务仍 blocked', '不是任务私有 LINV',
                  '不是第二项实际执行消融', 'uCOS3 未开始', 'GOOD_OS', 'ADR-0010', 'TaskSim']:
            self.assertIn(s, doc)
