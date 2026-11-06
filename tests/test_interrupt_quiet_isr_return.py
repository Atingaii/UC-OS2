"""quiet 中断的局部 ISR 返回；文本回归不能替代 Coq 根检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage298-quiet-isr-return'
P = 'certiucos/v293/proofs/V293InterruptQuietISRReturn.v'
Q = 'audit/probes/V293InterruptQuietISRReturnProbe.v'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read(name):
    return json.loads((D / name).read_text())


class QuietISRReturnTests(unittest.TestCase):
    def test_actual_builder_public_contract(self):
        s = (R / P).read_text()
        statement = s.split('Theorem V293_interrupt_quiet_builder_general :', 1)[1].split('Proof.', 1)[0]
        for word in ['BuildintPre', 'BuildintRet', 'intspec i=Some(spec_done None)',
                     'Spec enter=Some(efp,efq', 'Spec exit=Some(xfp,xfq',
                     r'pre //\\ filter', 'V293_irq_source_wrapper']:
            self.assertIn(word, statement)
        self.assertNotRegex(statement, r'\b(?:snapshot|cstep|TaskSim|forall j|Top|Lower)\b')
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertIn('V293_irq_builder_lower_clear with', s)
        self.assertIn('V293_irq_quiet_builder_open', s)

    def test_interval_resource_conversion_not_global_clear(self):
        s = (R / P).read_text()
        for word in ['isr_inv', 'j<i ->ir j=false', 'low<=j<=low+n',
                     'starinv_noisr I low n', 'starinv_isr I low n',
                     'Aisr(isrupd ir i false) **Core ==>invlth_isr G 0 i',
                     'eoi_ieoff_rule', 'V293_OSIntEnter_bound_call',
                     'V293_interrupt_bound_quiet_exit_depth', 'apply iret_rule']:
            self.assertIn(word, s)
        self.assertNotIn('SWINV', s)
        self.assertNotIn('forall j,ir j=false', s)

    def test_same_heap_single_bit_and_satisfiable_resources(self):
        s = (R / Q).read_text()
        for name in ['QKsame_heap_active_input', 'QKactual_wrapper',
                     'QKactive_return_resources', 'QKonly_other_ISR_bit',
                     'QKother_bit_preserved_and_old_gate_rejected',
                     'QKlower_active_builder_rejected', 'QKactive_entry_and_return_bit']:
            self.assertIn('Theorem ' + name + ' :', s)
        self.assertIn('destruct(QJfiltered_nonempty nest Positive Bound)', s)
        self.assertIn('QCstate M O|=QJpre /\\QKstate(isrupd QKother 0 true)M O|=QKpre QKother', s)
        self.assertIn('getmem(QCstate M O)=getmem(QKstate(isrupd QKother 0 true)M O)', s)
        self.assertIn('~st|=ipreasrt\' 1(isrupd(fun _:hid=>false)0 true)', s)
        self.assertIn('st|=QKret QKother ->getisr(gettaskst st)1=true', s)
        self.assertNotRegex(s, re.compile(r'^Definition \w*(?:memory|heap)\w*', re.M))

    def test_finite_interval_and_unrelated_bit_control(self):
        # 独立布尔算术检查；不是中断可达性或两次完整 C 执行。
        accepted = rejected = retained = 0
        for mask in range(32):
            ir = [(mask >> j) & 1 for j in range(5)]
            for i in range(5):
                updated = ir[:]
                updated[i] = 0
                if any(ir[j] for j in range(i)):
                    rejected += 1
                    continue
                accepted += 1
                self.assertFalse(any(updated[:i + 1]))
                self.assertEqual(updated[i + 1:], ir[i + 1:])
                retained += any(updated[i + 1:])
        self.assertEqual((accepted, rejected, retained), (62, 98, sum(2 * (2**k - 1) for k in range(5))))
        ir = [0, 1, 0, 0, 0]
        self.assertFalse(all(x == 0 for x in ir))
        self.assertTrue(all(ir[j] == 0 for j in range(0)))

    def test_protocol_identity_and_append_only_project(self):
        b = read('baseline.json')['files']
        ident = read('source-identity.json')
        for p, h in ident['files'].items():
            self.assertEqual(sha(R / p), h, p)
            self.assertEqual(b[p], h, p)
        self.assertEqual((R / '_CoqProject').read_bytes(),
                         (D / '_CoqProject.baseline').read_bytes() + ('\n' + P + '\n').encode())
        self.assertNotIn(Q, (R / '_CoqProject').read_text())
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])

    def test_stable_compiles_all_roots_and_recursive_kernel_check(self):
        stable = read('stable-compiles.json')
        roots = []
        for p, prefix in [(P, 'production'), (Q, 'probe')]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            for i in [1, 2]:
                row = stable[prefix + '-stable-' + str(i)]
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / p))
                self.assertEqual(row['source_sha256'], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
        t = read('trust.json')
        self.assertEqual(len(roots), 18)
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], len(roots))
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in t['commands']))
        self.assertLessEqual(set(t['assumptions']),
                             {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})


if __name__ == '__main__':
    unittest.main()
