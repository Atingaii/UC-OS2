"""嵌套退出中断的连续执行回归；结构检查不代替 Coq 语义证明。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage194-interrupt-nested-execution'
PROD = 'certiucos/v293/proofs/V293OSIntExitExecution.v'
PROBE = 'audit/probes/V293OSIntExitExecutionProbe.v'


def read(name):
    return json.loads((D / name).read_text())


class InterruptNestedExecutionTests(unittest.TestCase):
    def test_exact_source_and_protocol(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        for p, h in source['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
            self.assertEqual(h, read('baseline.json')['files'][p])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(), read('protocol-identity.json')['protocol.json'])
        old = R / 'audit/logs/stage193-interrupt-uniform-internal/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])
        self.assertTrue(read('protocol-clarification.json')['frozen_protocol_unchanged'])

    def test_actual_full_body_trace_without_callee_oracle(self):
        src = (R / PROD).read_text()
        stmt = src.split('Theorem V293_OSIntExit_nested_execution :', 1)[1].split('Proof.', 1)[0]
        for token in ('V293_local_steps P', '2<=n', 'n<256', 'store Tint32', 'store Tint8',
                      'callcont ks', 'V293_bytes_writable', 'get Mf(b,Z.of_nat k)=None'):
            self.assertIn(token, stmt)
        for token in ('InfRules', 'Spec', 'cstepstar', 'V293_local_steps'):
            self.assertNotIn(token, stmt.split('exists Mf,', 1)[0])
        for token in ('V293_OSIntExit_abstract_normalization', 'V293_port_normalize',
                      'V293_OSIntExit_nested_middle_execution', 'V293_void_return_execution',
                      'apply encrit_step', 'apply excrit_step', 'V293_success_assign_zero'):
            self.assertIn(token, src)
        self.assertNotIn('CertiOS.audit.', src)

    def test_nonempty_memory_return_frame_and_both_boundaries(self):
        src = (R / PROBE).read_text()
        for token in ('Theorem NEnested_witness :', 'Lemma NEentry_loads :',
                      'Corollary NEnest2 :', 'Corollary NEnest255 :',
                      'Definition NEprogram : progunit := fun _=>None.', 'Int.repr 23',
                      'V293_storebytes_exists', 'load Tint8 Mf', 'get Mf(61%positive,Z.of_nat k)=None',
                      'b<>61%positive -> b<>52%positive'):
            self.assertIn(token, src)
        stmt = src.split('Theorem NEnested_witness :', 1)[1].split('Proof.', 1)[0]
        self.assertNotIn('store ', stmt)
        self.assertIn('forall n ir enabled si ci,2<=n -> n<256', stmt)

    def test_paired_actual_critical_segment_ablation_and_physical_readback(self):
        src = (R / PROBE).read_text()
        stmt = src.split('Theorem NEcritical_pair_witness :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(stmt.count('V293_local_steps NEprogram'), 2)
        self.assertEqual(stmt.count('((NEge,NEle,NEmem 2),ir,(enabled,si,ci))'), 2)
        self.assertIn('NEcritical true', stmt)
        self.assertIn('NEcritical false', stmt)
        self.assertIn('(false,si,enabled::ci)<>(enabled,si,ci)', stmt)
        self.assertIn('Theorem NEnest_changed :', src)
        self.assertIn('if restore then sprim excrit else sskip None', src)

    def test_stable_compiles_recursive_trust_and_no_holes(self):
        stable = read('stable-compiles.json')
        for kind, p in (('body', PROD), ('probe', PROBE)):
            row = read(stable[kind] + '.json')
            h = hashlib.sha256((R / p).read_bytes()).hexdigest()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(h, row['initial_source_sha256'])
            self.assertEqual(h, row['source_sha256'])
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
        trust = read('trust.json')
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(trust['roots_printed'], len(trust['roots']))
        self.assertEqual(trust['roots_printed'], 14)
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))
