"""局部延时阻塞的真实 Coq 证据；不把位图选择升级为整核证明。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage316-time-delay-block'
C = 'certiucos/v293/code/V293OSTimeDly.v'
P = 'certiucos/v293/proofs/V293TimeDlyBlocking.v'
Q = 'audit/probes/V293TimeDlyBlockingProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class TimeDelayBlockTests(unittest.TestCase):
    def test_exact_configured_source_and_bounded_translation(self):
        identity = read('source-identity.json')
        inventory = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        self.assertEqual(identity, next(x for x in inventory['functions'] if x['name'] == 'OSTimeDly'))
        self.assertEqual(sha(D / 'OSTimeDly.source.c.snapshot.txt'), identity['source_lines_sha256'])
        configured = (D / 'OSTimeDly.configured.c.snapshot.txt').read_bytes()
        self.assertEqual(hashlib.sha256(configured[:-1]).hexdigest(), identity['preprocessed_definition_sha256'])
        self.assertIn(b'OSTCBCur->OSTCBDly = ticks;', configured)
        ast = (R / C).read_text()
        for token in ['cpu_sr=0 local initializer', 'encrit/excrit', 'V293_dly_before_delay',
                      'current 18%Z', 'current 19%Z', 'current 20%Z', 'current 13%Z']:
            self.assertIn(token, ast)

    def test_execution_and_physical_record_share_the_same_heap(self):
        s = (R / P).read_text()
        pre, body = s.split('Theorem V293_OSTimeDly_blocking_bridge :', 1)[1].split('Proof.', 1)
        inputs, outputs = pre.split('exists Mf,', 1)
        self.assertNotIn('cstepstar', inputs)
        self.assertNotIn('store ', inputs)
        self.assertNotIn('V293_highest_ready', inputs)
        for token in ['cstepstar P', '(ge,le,Mf)', 'V293_task_record Mf', 'V293_owned_record_cells',
                      'V293_bitmap_tasks', 'V293_priority_table', '~V293_highest_ready']:
            self.assertIn(token, outputs)
        for token in ['V293_OSTimeDly_updates_execution', 'V293_dly_blocked_record',
                      'V293_dly_bitmap_tasks', 'V293_tick_priority_table']:
            self.assertIn(token, body)
        self.assertIn('V293_tick_cells_store_at', s)
        self.assertIn('forall tail,cstepstar', s)
        self.assertNotIn('Require Import CertiOS.audit.', s)

    def test_nonempty_fixture_and_priority_rule_are_not_wakeup_reachability(self):
        s = (R / Q).read_text()
        for token in ['OwnershipCellsSpatial', 'DLspatial', 'DLtable', 'DLbitmap',
                      'DLhigher_still_runs', 'DLactual_block', 'V293_task_record Mf OwnershipReady',
                      'V293_highest_ready', 'OwnershipWaiting', 'not proof of the preceding wakeup']:
            self.assertIn(token, s)
        self.assertIn('80 0 1', s)
        self.assertIn('V293_byteval 64', s)
        coverage = read('function-boundary.json')
        self.assertTrue(coverage['stages']['located'])
        self.assertFalse(coverage['stages']['full_target_linked'])
        self.assertFalse(coverage['full_api_proved'])

    def test_only_delay_write_changes_and_rejection_is_after_actual_execution(self):
        protocol, result = read('ablation-protocol.json'), read('ablation.json')
        base = (D / 'gate-base.v.snapshot.txt').read_text()
        mutant = (D / 'gate-mutant.v.snapshot.txt').read_text()
        self.assertTrue(protocol['prospective'])
        self.assertEqual(base.count(protocol['old']), 1)
        self.assertEqual(base.replace(protocol['old'], protocol['new']), mutant)
        self.assertEqual(result['protocol_sha256'], sha(D / 'ablation-protocol.json'))
        self.assertEqual(read('gate-base.json')['exit'], 0)
        self.assertEqual(read('gate-mutant.json')['exit'], 1)
        self.assertTrue(result['actual_mutant_body_executed'])
        log = (D / 'gate-mutant.log').read_text()
        for token in ['Executed : cstepstar', 'ActualDelay : load Tint32',
                      'ClearedRow : load Tint8', 'while it is expected']:
            self.assertIn(token, log)
        self.assertEqual((result['delay_after_baseline'], result['delay_after_mutant']), (3, 0))

    def test_recursive_trust_and_two_stable_compilations(self):
        trust = read('trust.json')
        roots = []
        for p in [C, P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
            if p != C:
                roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], 16)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']), {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        for stem, p in [('code', C), ('production', P), ('probe', Q)]:
            for i in [1, 2]:
                row = read(f'stable-{stem}-{i}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / p))
                self.assertEqual(row['source_sha256'], sha(R / p))

    def test_frozen_history_registration_and_bytecode_preserved(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in read('baseline.json')['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        for name in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / name).read_bytes().endswith((D / (name + '.baseline')).read_bytes()))
        project = (R / '_CoqProject').read_bytes()
        self.assertTrue(project.startswith((D / '_CoqProject.baseline').read_bytes()))
        for p in [C, P]:
            self.assertEqual(project.splitlines().count(p.encode()), 1)
        self.assertEqual({str(p.relative_to(R)): sha(p) for p in R.rglob('*.pyc')}, read('bytecode-baseline.json'))
        for name in ['protocol', 'ablation-protocol']:
            self.assertEqual((D / (name + '.sha256')).read_text().split(),
                             [sha(D / (name + '.json')), name + '.json'])


if __name__ == '__main__':
    unittest.main()
