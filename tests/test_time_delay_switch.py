"""延时阻塞到比较、计数器及原切换步的局部回归，不是整核验收。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage320-time-delay-switch'
OLD = R / 'audit/logs/stage319-time-delay-sched-call'
P = 'certiucos/v293/proofs/V293TimeDlySwitch.v'
Q = 'audit/probes/V293TimeDlySwitchProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class TimeDelaySwitchTests(unittest.TestCase):
    def test_source_replay_and_function_boundary(self):
        inventory = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        identities = read('source-identities.json')
        self.assertEqual(identities, json.loads((OLD / 'source-identities.json').read_text()))
        self.assertEqual([r['name'] for r in identities], ['OSTimeDly', 'OS_Sched', 'OS_SchedNew'])
        for row in identities:
            self.assertEqual(row, next(r for r in inventory['functions'] if r['name'] == row['name']))
            self.assertEqual(sha(D / (row['name'] + '.source.c.snapshot.txt')), row['source_lines_sha256'])
            self.assertEqual(hashlib.sha256((D / (row['name'] + '.configured.c.snapshot.txt')).read_bytes()[:-1]).hexdigest(),
                             row['preprocessed_definition_sha256'])
        self.assertEqual(read('source-replay.json')['exit'], 0)
        boundary = read('function-boundary.json')
        self.assertFalse(boundary['full_api_proved'])
        self.assertTrue(all(s['located'] and not s['full_target_linked'] for s in boundary['stages'].values()))
        self.assertIn('after cpu_sr initializer', boundary['entry'])
        self.assertIn('original lpstep', boundary['positive_endpoint'])
        self.assertFalse(boundary['priority_cache_synchronized'])

    def test_call_to_switch_has_no_execution_or_store_oracle(self):
        source = (R / P).read_text()
        statement, proof = source.split('Theorem V293_sched_call_to_switch :', 1)[1].split('Proof.', 1)
        inputs, outputs = statement.split('exists bs byblock Mf,', 1)
        for token in ['cstepstar', 'V293_local_steps', 'ProgSim', 'store ', 'rdy', 'V293_task_record']:
            self.assertNotIn(token, inputs)
        for token in ['V293_sched_read_memory M', 'V293_bytes_writable M bk', 'nc<256', '<>nc']:
            self.assertIn(token, inputs)
        for token in ['curs(scall f nil)', 'curs(sprim(switch target))', 'Int.add c Int.one',
                      'V293_bytes_writable Mf bs', 'get Mf(byblock,0%Z)=None']:
            self.assertIn(token, outputs)
        for token in ['V293_sched_call_to_change', 'V293_sched_change_raw', 'exact Prefix', 'exact Tail']:
            self.assertIn(token, proof)
        raw = source.split('Lemma V293_sched_change_raw :', 1)[1].split('Theorem V293_sched_call_to_switch', 1)[0]
        for token in ['V293_storebytes_exists', 'V293_ready_counter_eval', 'V293_tick_assign32_execution',
                      'V293_OSSched_byte_comparison_eval', 'V293_storebytes_nth']:
            self.assertIn(token, raw)
        self.assertNotIn('Require Import CertiOS.audit.', source)

    def test_physical_switch_constructs_store_from_permissions(self):
        source = (R / P).read_text().split('Theorem V293_sched_switch_commit :', 1)[1]
        inputs, outputs = source.split('exists Mf,', 1)
        for token in ['lpstep', 'store(', 'ProgSim', 'SWINV']:
            self.assertNotIn(token, inputs)
        self.assertIn('V293_bytes_writable M bc', inputs)
        for token in ['V293_storebytes_exists', 'eapply pswitch_step', 'V293_store_readback',
                      'set T old(SKIP,(kenil,ks))', 'get ge OSTCBCur']:
            self.assertIn(token, source)
        self.assertIn('lpstep', outputs)

    def test_nonempty_block_switch_high_rule_both_ie_and_wrap(self):
        source = (R / Q).read_text()
        statement = source.split('Theorem DWblocked_run :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(statement.split('exists bs byblock Mf,', 1)[0].strip(), 'forall c enabled,')
        for token in ['V293_OSTimeDly_body_to_sched_refines', 'V293_sched_call_to_switch',
                      'exact Blocked|exact Scheduled', 'Theorem DWblocked_switch', 'V293_sched_switch_commit',
                      'V293_task_record_frame', 'get(DWenvs bs)OwnershipWaiting', 'get(DWaux enabled)OwnershipWaiting',
                      'Lemma DWselected', 'Theorem DWhigh_switch', 'eapply hswi_step',
                      'Theorem DWboth_IE', 'DWrun Int.zero true', 'DWrun Int.zero false',
                      'Lemma DWcounter_wrap', 'Int.repr Int.max_unsigned', 'Theorem DWwrap_run',
                      'V293_byteval 4', 'Vint32(Int.repr 99)', 'get Mf(byblock,0%Z)=None']:
            self.assertIn(token, source)
        self.assertIn('spec_step', statement)
        self.assertIn('V293_bitmap_tasks 64 0', statement)

    def test_counter_only_ablation_reaches_late_gate(self):
        protocol = read('ablation-protocol.json')
        self.assertTrue(protocol['prospective'])
        self.assertIn('fragment-level', protocol['scope'])
        for suffix in ['-03', '-final']:
            base, mutant = [(D / (stem + suffix + '.v.snapshot.txt')).read_text()
                            for stem in ['gate-base', 'gate-mutant']]
            self.assertEqual(base.count(protocol['old']), 1)
            self.assertEqual(base.replace(protocol['old'], protocol['new']), mutant)
            self.assertEqual(read('gate-base' + suffix + '.json')['exit'], 0)
            self.assertEqual(read('gate-mutant' + suffix + '.json')['exit'], 1)
            log = (D / ('gate-mutant' + suffix + '.log')).read_text()
            for token in ['Prefix : DWprefix', 'Tail : cstepstar', 'Switch : lpstep',
                          'Records : V293_task_records', 'Current : load', 'Canary : load Tint32',
                          'CPU : V293_bytes_writable', 'HelperReleased : get Mf',
                          'The term "Counter" has type', 'Some (Vint32 Int.one)', 'exact~Counter.']:
                self.assertIn(token, log)
            self.assertNotIn('not found in the current environment', log)
        source = (R / Q).read_text()
        self.assertIn('DWablation_run : exists bs byblock Mr,', source)
        self.assertIn('DWprefix Int.zero true bs Mr /\\forall count,exists Mcut Mf,', source)
        result = read('ablation-final.json')
        for token in ['single_factor', 'same_incoming_heap_and_prefix', 'actual_switch_records_canary_cpu_helper_before_gate']:
            self.assertTrue(result[token])
        self.assertFalse(result['mutated_full_function_call_claimed'])
        self.assertEqual(result['protocol_sha256'], sha(D / 'ablation-protocol.json'))
        self.assertEqual(result['production_sha256'], sha(R / P))
        self.assertEqual(result['probe_sha256'], sha(R / Q))
        for i, missing in [(1, 'V293_cpu_lenv'), (2, 'V293_task_records')]:
            self.assertEqual(read(f'gate-base-{i:02d}.json')['exit'], 1)
            self.assertIn(missing + ' was not found', (D / f'gate-base-{i:02d}.log').read_text())

    def test_recursive_trust_and_source_stable_repeated_compiles(self):
        roots = []
        for p in [P, Q]:
            source = (R / p).read_text()
            self.assertNotRegex(source, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', source, re.M)]
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(r['exit'] == 0 for r in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']), {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        for stem, p in [('production', P), ('probe', Q)]:
            for i in [1, 2]:
                row = read(f'stable-{stem}-{i}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / p))
                self.assertEqual(row['source_sha256'], sha(R / p))

    def test_frozen_history_append_only_registration_and_bytecode(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in read('baseline.json')['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        project = (R / '_CoqProject').read_bytes()
        self.assertTrue(project.startswith((D / '_CoqProject.baseline').read_bytes() + (P + '\n').encode()))
        self.assertEqual(project.splitlines().count(P.encode()), 1)
        self.assertEqual({str(p.relative_to(R)): sha(p) for p in R.rglob('*.pyc')}, read('bytecode-baseline.json'))
        for name in ['protocol', 'ablation-protocol']:
            self.assertEqual((D / (name + '.sha256')).read_text().split(), [sha(D / (name + '.json')), name + '.json'])

    def test_documented_scope_is_not_full_kernel(self):
        doc = (R / 'audit/STAGE320_TIME_DELAY_SWITCH.md').read_text()
        for token in ['不是完整 API', '不是全局记录不变量', '不是 raw port', '优先级缓存',
                      'spec_step', '全局 ProgSim', 'GOOD_OS', 'uCOS3', '同一输入堆', '片段级消融']:
            self.assertIn(token, doc)
        for name in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / name).read_bytes().endswith((D / (name + '.baseline')).read_bytes()))
        self.assertFalse(read('function-boundary.json')['full_api_proved'])


if __name__ == '__main__':
    unittest.main()
