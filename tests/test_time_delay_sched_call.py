"""延时阻塞到真实调度调用／目标写回的局部回归，不是整核验收。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage319-time-delay-sched-call'
OLD = R / 'audit/logs/stage318-time-delay-entry'
P = 'certiucos/v293/proofs/V293TimeDlySchedCall.v'
Q = 'audit/probes/V293TimeDlySchedCallProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda name: json.loads((D / name).read_text())


class TimeDelaySchedCallTests(unittest.TestCase):
    def test_source_replay_and_bounded_function_coverage(self):
        inventory = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        identities = read('source-identities.json')
        self.assertEqual([x['name'] for x in identities], ['OSTimeDly', 'OS_Sched', 'OS_SchedNew'])
        for row in identities:
            self.assertEqual(row, next(x for x in inventory['functions'] if x['name'] == row['name']))
            self.assertEqual(sha(D / (row['name'] + '.source.c.snapshot.txt')), row['source_lines_sha256'])
            self.assertEqual(hashlib.sha256((D / (row['name'] + '.configured.c.snapshot.txt')).read_bytes()[:-1]).hexdigest(),
                             row['preprocessed_definition_sha256'])
        self.assertEqual(identities[0], json.loads((OLD / 'source-identity.json').read_text()))
        self.assertEqual(read('source-replay.json')['exit'], 0)
        boundary = read('function-boundary.json')
        self.assertFalse(boundary['full_api_proved'])
        for stages in boundary['stages'].values():
            self.assertTrue(stages['located'])
            self.assertFalse(stages['full_target_linked'])
        self.assertIn('after cpu_sr initializer', boundary['entry'])
        self.assertIn('BEFORE comparison and physical switch', boundary['positive_endpoint'])

    def test_stable_interface_has_no_callee_execution_or_current_ready_oracle(self):
        source = (R / P).read_text()
        statement, proof = source.split('Theorem V293_sched_call_to_change :', 1)[1].split('Proof.', 1)
        inputs, outputs = statement.split('exists bs byblock Mi Mf,', 1)
        for forbidden in ['cstepstar', 'V293_local_steps', 'spec_step', 'ProgSim', 'store ', 'rdy', 'V293_task_record']:
            self.assertNotIn(forbidden, inputs)
        for token in ['P helper=Some(V293_OSSchedNew_function', 'V293_sched_read_memory M',
                      'V293_bytes_writable M bd', 'Some(Vptr next)']:
            self.assertIn(token, inputs)
        for token in ['V293_local_steps P', 'curs(scall f nil)', 'V293_OSSched_change high current counter',
                      '(false,si,enabled::ci)', 'Some(Vptr next)', 'V293_bytes_writable Mf bs',
                      'get Mf(byblock,0%Z)=None', 'get Mf(c,i)=get M(c,i)']:
            self.assertIn(token, outputs)
        for token in ['V293_sched_call_enter', 'V293_sched_control_enter', 'V293_schednew_raw_call',
                      'V293_assign_pointer_execution', 'exact NewCall', 'exact Assigned']:
            self.assertIn(token, proof)
        self.assertNotIn('Require Import CertiOS.audit.', source)

    def test_helper_allocates_frees_and_has_exact_net_update(self):
        source = (R / P).read_text()
        helper = source.split('Theorem V293_schednew_raw_call :', 1)[1].split('Theorem V293_sched_call_to_change', 1)[0]
        inputs, body = helper.split('exists byblock Ms,', 1)
        self.assertNotIn('cstepstar', inputs)
        for token in ['V293_ready_fresh_avoiding', 'allocb M byblock', 'V293_OSSchedNew_updates_execution',
                      'apply snpcall_step', 'sfexec_step', 'salloclv_step', 'sallocend_step',
                      'sret_step', 'sfree_step', 'sfreeend_step', 'V293_sched_byte_release_exact',
                      'free Tint8 byblock Ms=Some(V293_write_byte M bh', 'byblock<>bh']:
            self.assertIn(token, body)
        self.assertIn('HalfPermMap.extensionality', source)

    def test_nonempty_body_composition_and_same_program_both_ie(self):
        source = (R / Q).read_text()
        statement, proof = source.split('Theorem DSblocked_run :', 1)[1].split('Proof.', 1)
        inputs, outputs = statement.split('exists bs byblock Mf,', 1)
        self.assertEqual(inputs.strip(), 'forall wrong enabled,')
        for token in ['DSrun wrong enabled bs Mf', 'spec_step', 'V293_task_records Mf',
                      'V293_bitmap_tasks 64 0', 'V293_byteval 6', 'Vptr(DStarget wrong)',
                      'Vint32(Int.repr 99)', 'V293_bytes_writable Mf bs', 'get Mf(byblock,0%Z)=None']:
            self.assertIn(token, outputs)
        for token in ['V293_OSTimeDly_body_to_sched_refines', 'V293_sched_call_to_change',
                      'exact Blocked|exact Scheduled', 'V293_task_record_frame', 'V293_load_block_frame',
                      'OwnershipCellsSpatial', 'DSseparated_sound', 'DSaddr_dec', 'Defined.',
                      'V293_read_bytes_witness', 'DTlow_owned', 'Theorem DSboth_IE',
                      'DSrun false true', 'DSrun false false', 'Lemma DSblocked_current']:
            self.assertIn(token, source)
        self.assertNotIn('set DEabs curtid', proof)

    def test_pointer_ablation_reaches_only_late_identity_gate(self):
        protocol = read('ablation-protocol.json')
        self.assertTrue(protocol['prospective'])
        for suffix in ['-02', '-final']:
            base = (D / ('gate-base' + suffix + '.v.snapshot.txt')).read_text()
            mutant = (D / ('gate-mutant' + suffix + '.v.snapshot.txt')).read_text()
            self.assertEqual(base.count(protocol['old']), 1)
            self.assertEqual(base.replace(protocol['old'], protocol['new']), mutant)
            self.assertEqual(read('gate-base' + suffix + '.json')['exit'], 0)
            self.assertEqual(read('gate-mutant' + suffix + '.json')['exit'], 1)
            log = (D / ('gate-mutant' + suffix + '.log')).read_text()
            for token in ['Executed : DSrun', 'Step : hmstep', 'Records : V293_task_records',
                          'Bitmap : V293_bitmap_tasks', 'High : load Tint8', 'Canary : load Tint32',
                          'CPU : V293_bytes_writable', 'HelperReleased : get Mf',
                          'The term "Target" has type', 'Some (Vptr OwnershipWaiting)']:
                self.assertIn(token, log)
            self.assertIn('exact~Target.', log)
            self.assertNotIn('not found in the current environment', log)
        result = read('ablation-final.json')
        self.assertEqual(result['protocol_sha256'], sha(D / 'ablation-protocol.json'))
        for name in ['single_factor', 'same_program', 'same_numeric_priority', 'records_canary_cpu_helper_before_gate']:
            self.assertTrue(result[name])
        self.assertEqual(result['production_sha256'], sha(R / P))
        self.assertEqual(result['probe_sha256'], sha(R / Q))
        source = (R / Q).read_text()
        for token in ['DSbaseline_entries', 'Lemma DSonly_slot', 'p<>6', 'Lemma DSmutant_outside_table']:
            self.assertIn(token, source)
        self.assertEqual(read('gate-base-01.json')['exit'], 1)
        self.assertIn('V293_tcb_type was not found', (D / 'gate-base-01.log').read_text())

    def test_recursive_trust_and_repeated_source_stable_compiles(self):
        roots = []
        for path in [P, Q]:
            source = (R / path).read_text()
            self.assertNotRegex(source, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            self.assertEqual(read('trust-inputs.json')[path], sha(R / path))
            roots += [Path(path).stem + '.' + n for n in re.findall(
                r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', source, re.M)]
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']), {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        for stem, path in [('production', P), ('probe', Q)]:
            for i in [1, 2]:
                row = read(f'stable-{stem}-{i}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / path))
                self.assertEqual(row['source_sha256'], sha(R / path))

    def test_frozen_history_and_append_only_project_registration(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in read('baseline.json')['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        project = (R / '_CoqProject').read_bytes()
        self.assertTrue(project.startswith((D / '_CoqProject.baseline').read_bytes() + (P + '\n').encode()))
        self.assertEqual(project.splitlines().count(P.encode()), 1)
        self.assertEqual({str(p.relative_to(R)): sha(p) for p in R.rglob('*.pyc')}, read('bytecode-baseline.json'))
        for name in ['protocol', 'ablation-protocol']:
            self.assertEqual((D / (name + '.sha256')).read_text().split(),
                             [sha(D / (name + '.json')), name + '.json'])

    def test_documented_scope_and_rejected_invariant_mutant(self):
        doc = (R / 'audit/STAGE319_TIME_DELAY_SCHED_CALL.md').read_text()
        for token in ['不是完整回切', '不是全局记录不变量', '不是从之前真实 Waiting 状态唤醒',
                      '不是 raw port', '全局优先级表不变量保持证明', 'spec_step', '全局 ProgSim', 'GOOD_OS', 'uCOS3']:
            self.assertIn(token, doc)
        for name in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / name).read_bytes().endswith((D / (name + '.baseline')).read_bytes()))
        self.assertFalse(read('function-boundary.json')['full_api_proved'])


if __name__ == '__main__':
    unittest.main()
