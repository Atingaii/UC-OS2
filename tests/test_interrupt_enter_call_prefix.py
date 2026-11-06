"""完整 Enter 调用与实际中断前缀的边界检查；不充当整核证明。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage303-enter-call-prefix'
P = 'certiucos/v293/proofs/V293InterruptEnterCallPrefix.v'
Q = 'audit/probes/V293InterruptEnterCallPrefixProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class EnterCallPrefixTests(unittest.TestCase):
    def test_full_call_constructed_from_real_rules(self):
        s = (R / P).read_text()
        for rule in ['snpcall_step', 'sfexec_step', 'sallocend_step',
                     'V293_control_enter_execution', 'sret_step', 'sfreeend_step']:
            self.assertIn(rule, s)
        contract = s.split('Theorem V293_control_enter_full_call :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(contract.count('cstepstar'), 1)
        self.assertNotRegex(contract, r'->\s*cstepstar.*->|store Tint8|TaskSim')
        self.assertIn('(ge,caller,V293_control_enter_memory bn c M)', contract)
        self.assertNotIn('get caller running=None', contract)
        self.assertNotIn('Require Import CertiOS.audit.', s)

    def test_global_entry_created_not_assumed(self):
        s = (R / P).read_text()
        contract = s.split('Theorem V293_control_enter_irq_global :', 1)[1].split('Proof.', 1)[0]
        pre, post = contract.split('exists Mf,', 1)
        self.assertNotRegex(pre, r'V293_global_steps|cstepstar|store Tint8|TaskSim')
        self.assertIn('get T t=Some(interrupted,(ike,ks))', pre)
        self.assertIn('get aus t=Some((true,si,nil):localst)', pre)
        self.assertIn('V293_interrupt_source_enter', s)
        self.assertIn('V293_interrupt_local_steps_global', s)
        self.assertIn('V293_interrupt_eoi_restores_ir', s)
        self.assertIn('kseq(sprim exint)(kint interrupted ike caller ks)', post)
        self.assertIn('set aus t(false,i::si,nil)', post)

    def test_bridge_same_post_memory_and_precise_cutpoint(self):
        s = (R / P).read_text()
        for root in ['V293_control_enter_call_bridge', 'V293_control_enter_irq_global']:
            contract = s.split('Theorem ' + root + ' :', 1)[1].split('Proof.', 1)[0]
            self.assertIn('V293_control_read br bn bl Mf=Some(V293_control_enter c)', contract)
            self.assertIn('V293_control_step sd V293_control_Enter(O,c)', contract)
            self.assertIn('get Mf a=get M a', contract)
            self.assertIn('exists v,get M(bn,0%Z)=Some(true,v)', contract)
        self.assertIn('(curs(scall exit nil),(kenil,kseq(sprim exint)kstop))', s)
        self.assertNotIn('apply exint_step', s)
        self.assertNotIn('apply V293_control_exit', s)

    def test_nonempty_actual_calls_and_global_fixture(self):
        s = (R / Q).read_text()
        for text in ['ECcaller:env:=set(set emp', 'ECir:isr:=fun i=>Nat.eqb i 1',
                     'keop1 negation Tint32 kenil', '((true,[1],nil):localst)',
                     '((false,[0;1],nil):localst)', 'Theorem ECglobal_case',
                     'Corollary ECboundary_calls', 'CEmemory 0 254 7',
                     'CEmemory 1 254 7', 'CEmemory 1 255 7',
                     'Lemma ECshadow_discriminator', 'Lemma ECcaller_discriminator']:
            self.assertIn(text, s)
        boundary = s.split('Corollary ECboundary_calls :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(boundary.count('cstepstar ECprogram'), 3)
        self.assertIn('(904%positive,7%Z)77', (R / 'audit/probes/V293InterruptControlExecutionProbe.v').read_text())

    def test_independent_environment_discriminators(self):
        protocol = read('ablation-protocol.json')
        result = read('ablation-results.json')
        self.assertTrue(result['passed'] and result['production_unchanged'])
        self.assertEqual(protocol['production_sha256'], sha(R / P))
        self.assertEqual(protocol['probe_sha256'], sha(R / Q))
        self.assertIn('不是完整执行模拟消融', protocol['scope'])
        self.assertEqual(len(protocol['cases']), 2)
        for case in protocol['cases']:
            label = 'ablation-' + case['name']
            baseline = (D / (label + '-baseline.v.snapshot.txt')).read_text()
            mutant = (D / (label + '-mutant.v.snapshot.txt')).read_text()
            self.assertEqual(baseline.count(case['old']), 1)
            self.assertEqual(baseline.replace(case['old'], case['new'], 1), mutant)
            self.assertEqual(read(label + '-baseline.json')['exit'], 0)
            self.assertEqual(read(label + '-mutant.json')['exit'], 1)

    def test_all_roots_checked_without_new_assumptions(self):
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots.extend(Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M))
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], 10)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']), {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertEqual(len(read('stable-compiles.json')), 4)
        for label, row in read('stable-compiles.json').items():
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['source_sha256'], sha(R / (P if label.startswith('production') else Q)))
            self.assertEqual(row['source_sha256'], row['initial_source_sha256'])

    def test_registration_and_locked_source_identity(self):
        before = (D / '_CoqProject.baseline').read_bytes()
        current = (R / '_CoqProject').read_bytes()
        self.assertTrue(current.startswith(before + b'\n' + P.encode() + b'\n'))
        self.assertEqual(current.splitlines().count(P.encode()), 1)
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h, p)
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])

    def test_old_materials_and_bytecode_preserved(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        for p, h in read('baseline.json')['files'].items():
            if p not in mutable:
                self.assertTrue((R / p).is_file(), p)
                self.assertEqual(sha(R / p), h, p)
        current = {str(p.relative_to(R)): sha(p) for p in R.rglob('*.pyc')}
        self.assertEqual(current, read('bytecode-baseline.json'))
        self.assertEqual(len(current), 306)
