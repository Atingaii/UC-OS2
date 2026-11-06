"""结构回归只约束本步证据；实际 Hoare 证明由 Coq 核验。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage207-interrupt-exit-same-priority'
PROD = 'certiucos/v293/proofs/V293OSIntExitSamePriority.v'
PROBE = 'audit/probes/V293OSIntExitSamePriorityProbe.v'

def read(n):
    return json.loads((D / n).read_text())

def statement(src, name):
    return src.split(name + ' :', 1)[1].split('Proof.', 1)[0]

class InterruptExitSamePriorityTests(unittest.TestCase):
    def test_source_identity_and_prospective_protocol(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        self.assertEqual([x['function']['name'] for x in source['functions']],
                         ['OSIntEnter', 'OSIntExit', 'OS_SchedNew'])
        for x in source['functions']:
            self.assertTrue(x['reconstructed_repaired_source_matches'])
            self.assertTrue(x['temporary_source_removed_on_context_exit'])
            self.assertEqual(hashlib.sha256((D / (x['function']['name'] + '.configured.c.txt')).read_bytes()).hexdigest(),
                             x['function']['preprocessed_definition_sha256'])
        for p, h in source['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
            self.assertEqual(h, read('baseline.json')['files'][p])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])
        old = R / 'audit/logs/stage206-scheduler-isr-context/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_complete_body_no_assumed_middle(self):
        src = (R / PROD).read_text()
        stmt = statement(src, 'V293_OSIntExit_same_priority_body')
        self.assertEqual(stmt.count('InfRules'), 1)
        for token in ('nest<=1', 'V293_ready_select lo hi(V293_ready_group lo hi)=nc',
                      'V293_exit_boundary_body', 'V293_ISR_sched_fpre',
                      'result=None', 'OS[ir,enabled,si,ci]', 'Vint32 Int.zero'):
            self.assertIn(token, stmt)
        for token in ('apply V293_OSIntExit_context_same_dispatch', 'apply encrit1_rule',
                      'apply encrit2_rule', 'apply excrit1_rule', 'apply excrit2_rule',
                      'V293_time_zero Spec sd li I', 'apply ret_rule'):
            self.assertIn(token, src)
        self.assertNotIn('BuildPreI', stmt)
        self.assertNotIn('WFFunEnv', stmt)
        self.assertNotIn('CertiOS.audit.', src)

    def test_ordinary_data_is_a_frame_not_OS_context(self):
        src = (R / PROD).read_text()
        data = src.split('Definition V293_exit_same_core', 1)[1].split('Lemma V293_exit_same_data_good', 1)[0]
        for token in ('V293_sched_globals', 'V293_sched_inputs', 'CurLINV li tid',
                      'V293_prefix_frame', 'V293_counter_cell', 'V293_time_cell', 'V293_highest_ready'):
            self.assertIn(token, data)
        for token in ('Aie', 'Aisr', 'Ais ', 'Acs ', 'invlth_isr', '<||aop||>'):
            self.assertNotIn(token, data)
        self.assertIn('GoodFrm(V293_exit_same_data nest hv out c value)', src)
        self.assertIn('V293_sched_ISR_context I true ir si (true::ci)', src)
        self.assertIn('V293_sched_ISR_context I false ir si (false::ci)', src)

    def test_nonempty_and_bounded_assignment_control(self):
        src = (R / PROBE).read_text()
        for name in ('QPpre_nonempty', 'QPbody', 'QPboth_ie_and_nonempty_stacks',
                     'QPzero', 'QPwithout_zero'):
            self.assertRegex(src, r'Theorem ' + name + ' :')
        self.assertIn('pose proof(RCbig_owned 12 nest c 1 old)', src)
        self.assertIn('QPstate true (cons 0 nil)(cons false nil)', src)
        self.assertIn('QPstate false (cons 0 nil)(cons false nil)', src)
        self.assertIn('Vint32 Int.one', statement(src, 'QPwithout_zero'))
        self.assertIn('Vint32 Int.zero', statement(src, 'QPwithout_zero'))
        self.assertIn('rewrite Actual in Wrong;discriminate.', src)
        self.assertIn('not two full executions', src)
        self.assertNotIn('cstepstar', src)
        self.assertNotIn('loststep', src)

    def test_stable_compiles_recursive_trust_and_no_new_holes(self):
        roots = []
        for kind, p in (('body', PROD), ('probe', PROBE)):
            src = (R / p).read_text()
            label = read('stable-compiles.json')[kind]
            row = read(label + '.json')
            h = hashlib.sha256((R / p).read_bytes()).hexdigest()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(h, row['initial_source_sha256'])
            self.assertEqual(h, row['source_sha256'])
            self.assertEqual(h, hashlib.sha256((D / (label + '.v.snapshot.txt')).read_bytes()).hexdigest())
            self.assertNotRegex(src, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', src, re.M)]
        trust = read('trust.json')
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertEqual(list(read('assumptions-by-root.json')), roots)
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
        self.assertTrue(all(x['exit'] == 0 for x in trust['commands']))
