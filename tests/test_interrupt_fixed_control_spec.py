"""固定控制前端回归；算术影子和文本检查不代替旧 WFInt 健全性迁移。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage301-fixed-control-spec'
P = 'certiucos/v293/proofs/V293InterruptFixedControlSpec.v'
Q = 'audit/probes/V293InterruptFixedControlSpecProbe.v'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read(name):
    return json.loads((D / name).read_text())


class FixedControlSpecTests(unittest.TestCase):
    def test_fixed_operators_read_state_and_retain_update(self):
        s = (R / P).read_text()
        rules = s.split('Inductive V293_control_step', 1)[1].split('Inductive V293_control_steps', 1)[0]
        for text in ['sd V293_control_Enter(O,c)', 'sd V293_control_Exit(O,c)',
                     '(V293_control_Core(V293_control_exit_code c))(O,V293_control_exit c)',
                     '(V293_control_Core(spec_done None))(O,V293_control_enter c)',
                     'spec_step sd a O b O\'']:
            self.assertIn(text, rules)
        self.assertIn('if Nat.ltb i INUM then Some V293_fixed_control_handler else None', s)
        self.assertNotRegex(rules, r'spec_choice|absinfer_choice|spec_assume')
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertIn('not an instance of the old osintspec', s)

    def test_legacy_reflection_covers_finite_traces(self):
        s = (R / P).read_text()
        for root in ['V293_control_core_exact', 'V293_control_core_trace_exact']:
            contract = s.split('Theorem ' + root + ' :', 1)[1].split('Proof.', 1)[0]
            self.assertIn('<->', contract)
            self.assertIn("s'=(O',c)", contract)
            self.assertIn('spec_step', contract)
        q = (R / Q).read_text()
        self.assertIn('Theorem FCenabled_not_self', q)
        self.assertIn('DCwaiting_no_self_sched', q)
        self.assertIn('Global switching has not been ported', q)

    def test_source_updates_and_unfiltered_builder(self):
        s = (R / P).read_text()
        for text in ['V293_OSIntEnter_updates_hoare', 'V293_OSIntExit_decrement_hoare',
                     'V293_control_cells_capture', 'V293_control_enter c)R',
                     'V293_control_exit(V293_control 1 n l))R', 'V293_control_capture_owned']:
            self.assertIn(text, s)
        c = s.split('Theorem V293_fixed_control_builder_prefix :', 1)[1].split('Proof.', 1)[0]
        for text in ['BuildintPre', 'st|=pre', 'V293_fixed_control_intspec i',
                     'V293_control_capture brun bn bl st', 'V293_control_steps sd V293_fixed_control_handler']:
            self.assertIn(text, c)
        self.assertNotRegex(c, r'quiet_filter|highest|sched_self|TaskSim')
        self.assertIn('Only the running=1 decrement prefix', s)

    def test_same_frontend_actual_lock_only_pair(self):
        s = (R / Q).read_text()
        c = s.split('Theorem FCexit_lock_pair :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(c.count('V293_control_step V293_scheduler V293_control_Exit'), 2)
        for text in ['store Tint8(ACmemory n)(151%positive,0%Z)(V293_byteval 1)',
                     '(b,off)<>(151%positive,0%Z)', 'Some(V293_control 1 n 0)',
                     'Some(V293_control 1 n 1)', '(RIabstract OwnershipWaiting,V293_control 1 0 0)',
                     '(RIabstract OwnershipWaiting,V293_control 1 0 1)',
                     'CRcall(ACmemory n)CCspec', 'CRcall Ml QCspec']:
            self.assertIn(text, c)
        self.assertIn('CRlock_only_pair n', s)
        self.assertIn('distinct CCspec/QCspec', s)
        self.assertIn('FCpair_boundaries', s)
        self.assertIn('V293_control 1 254 0', s)

    def test_independent_source_guard_oracle_and_single_factors(self):
        mismatches = dict(lock=0, double_depth=0, retained_update=0)
        checked = 0
        # 逐步 C 控制条件，不是内存执行或调度器模拟。
        for running in [0, 1, 2, 255]:
            for depth in range(256):
                for locked in range(256):
                    post = depth
                    scheduled = False
                    if running == 1:
                        if post > 0:
                            post -= 1
                        if post == 0 and locked == 0:
                            scheduled = True
                    select = running == 1 and depth <= 1 and locked == 0
                    retained = max(depth - 1, 0) if running == 1 else depth
                    self.assertEqual((scheduled, post), (select, retained))
                    entered = depth + 1 if running == 1 and depth < 255 else depth
                    pair_select = running == 1 and entered <= 1 and locked == 0
                    self.assertEqual(pair_select, running == 1 and depth == 0 and locked == 0)
                    mismatches['lock'] += select != (running == 1 and depth <= 1)
                    mismatches['double_depth'] += select != (running == 1 and retained <= 1 and locked == 0)
                    mismatches['retained_update'] += retained != depth
                    checked += 1
        self.assertEqual(checked, 262144)
        self.assertEqual(mismatches, dict(lock=510, double_depth=1, retained_update=65280))

    def test_actual_coq_single_factor_pairs(self):
        protocol = read('ablation-protocol.json')
        report = read('ablation-results.json')
        self.assertTrue(report['passed'] and report['production_unchanged'])
        self.assertEqual(protocol['production_sha256'], sha(R / P))
        self.assertEqual((D / 'ablation-protocol.sha256').read_text().split(),
                         [sha(D / 'ablation-protocol.json'), 'ablation-protocol.json'])
        prefix = (R / P).read_text().split('Theorem V293_fixed_control_lookup', 1)[0]
        self.assertEqual(hashlib.sha256(prefix.encode()).hexdigest(), protocol['prefix_sha256'])
        self.assertEqual(len(report['results']), 6)
        for case in protocol['cases']:
            name = 'ablation-' + case['name']
            old = (D / (name + '-baseline.v.snapshot.txt')).read_text()
            new = (D / (name + '-mutant.v.snapshot.txt')).read_text()
            self.assertEqual(old.replace(case['old'], case['new'], 1), new)
            self.assertEqual(read(name + '-baseline.json')['exit'], 0)
            self.assertNotEqual(read(name + '-mutant.json')['exit'], 0)
            self.assertIn('Theorem discriminate_case', old)

    def test_source_identity_protocol_and_project_append(self):
        base = (D / '_CoqProject.baseline').read_bytes()
        current = (R / '_CoqProject').read_bytes()
        self.assertTrue(current.startswith(base))
        self.assertEqual(current[len(base):].splitlines().count(P.encode()), 1)
        self.assertNotIn(Q.encode(), current)
        self.assertEqual((D / 'protocol.sha256').read_text().split(),
                         [sha(D / 'protocol.json'), 'protocol.json'])
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h, p)
            self.assertEqual(read('baseline.json')['files'][p], h, p)

    def test_all_roots_stable_and_recursive_trust(self):
        roots = []
        for p, prefix in [(P, 'production'), (Q, 'probe')]:
            source = (R / p).read_text()
            self.assertNotRegex(source, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            for i in [1, 2]:
                row = read('stable-compiles.json')[prefix + '-stable-' + str(i)]
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / p))
                self.assertEqual(row['source_sha256'], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(
                r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', source, re.M)]
        self.assertEqual(len(roots), 18)
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']),
                             {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})


if __name__ == '__main__':
    unittest.main()
