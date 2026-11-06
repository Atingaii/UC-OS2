"""真实分配调用接通调度/切换的局部验收，不替代整核目标。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage324-time-delay-allocated-sched'
OLD = R / 'audit/logs/stage323-time-delay-call-block'
P = 'certiucos/v293/proofs/V293TimeDlyAllocated.v'
Q = 'audit/probes/V293TimeDlyAllocatedProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda name: json.loads((D / name).read_text())


class TimeDelayAllocatedSchedTests(unittest.TestCase):
    def test_exact_source_identity_and_replay(self):
        identities = read('source-identities.json')
        inventory = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        self.assertEqual(identities, json.loads((OLD / 'source-identities.json').read_text()))
        self.assertEqual({row['name'] for row in identities}, {'OSTimeDly', 'OS_Sched', 'OS_SchedNew'})
        for row in identities:
            self.assertIn(row, inventory['functions'])
            self.assertEqual(sha(D / (row['name'] + '.source.c.snapshot.txt')), row['source_lines_sha256'])
            self.assertEqual(hashlib.sha256((D / (row['name'] + '.configured.c.snapshot.txt')).read_bytes()[:-1]).hexdigest(),
                             row['preprocessed_definition_sha256'])
        self.assertEqual(read('source-replay.json')['exit'], 0)

    def test_stable_contract_allocates_without_execution_or_store_oracle(self):
        source = (R / P).read_text()
        statement, proof = source.split('Theorem V293_dly_allocated_to_sched_refines:', 1)[1].split('Proof.', 1)
        inputs, outputs = statement.split('exists Mf,', 1)
        for token in ['V293_local_steps', 'cstepstar', 'store ', 'spec_step ', 'V293_task_records M']:
            self.assertNotIn(token, inputs)
        for token in ['fresh M ba', 'fresh M byloc', 'fresh M bs', 'V293_dly_call_cells',
                      'V293_dly_call_lenv ticks y saved ba byloc bs']:
            self.assertIn(token, inputs)
        for token in ['(ge,caller,M)', 'scall f[econst32 duration]', 'scall sched nil',
                      'spec_step sd', 'V293_task_records Mf blocked',
                      'V293_bitmap_tasks(fst cleared)(snd cleared)blocked']:
            self.assertIn(token, outputs)
        for token in ['V293_dly_call_entry', 'V293_dly_body_first_y',
                      'V293_dly_after_y_to_sched_refines', 'V293_local_trans']:
            self.assertIn(token, proof)
        self.assertNotIn('Require Import CertiOS.audit.', source)
        self.assertNotIn('V293_OSTimeDly_body_to_sched_refines', source)

    def test_nonempty_initial_heap_excludes_all_three_locals(self):
        source = (R / Q).read_text()
        cells = source.split('Definition DAinput:=', 1)[1].split('Definition DAsmall', 1)[0]
        for token in ['11%positive', '12%positive', '13%positive']:
            self.assertNotIn(token, cells)
        self.assertIn('Lemma DAfresh:', source)
        self.assertIn('b=11%positive \\/b=12%positive \\/b=13%positive', source)
        self.assertIn('DLextra++(DLlow++DAframe wrong c)', source)
        for token in ['OwnershipCellsSpatial', 'apply DAjoin', 'V293_shared_fixture_fields', 'apply DTlow_owned']:
            self.assertIn(token, source)

    def test_one_program_and_actual_call_to_scheduler_composition(self):
        source = (R / Q).read_text()
        program = source.split('Definition DAprogram:', 1)[1].split('Definition DAframe', 1)[0]
        self.assertIn('DSprogram f', program)
        self.assertIn('Some DCfunction', program)
        run = source.split('Definition DArun', 1)[1].split('Theorem DAallocated_run:', 1)[0]
        for token in ['DAprogram', 'scall 1200%Z[econst32(Int.repr 3)]', '(DWge,emp,DAmem wrong c)',
                      'sprim(switch 116%Z)', 'DAcontinuation']:
            self.assertIn(token, run)
        statement, proof = source.split('Theorem DAallocated_run:', 1)[1].split('Proof.', 1)
        self.assertEqual(statement.split('exists bs byblock Mf,')[0].strip(), 'forall wrong c enabled,')
        for token in ['V293_dly_allocated_to_sched_refines DAprogram', 'V293_sched_call_to_switch DAprogram',
                      'exact Blocked|exact Scheduled', 'DAentry wrong c enabled']:
            self.assertIn(token, proof)
        for token in ['DWblocked_run', 'DWblocked_prefix', 'DSbody_to_change', 'DCcall_first_y enabled']:
            self.assertNotIn(token, source)

    def test_terminal_original_switch_high_step_and_resources(self):
        source = (R / Q).read_text()
        for token in ['Theorem DAallocated_switch:', 'V293_sched_switch_commit', 'Theorem DAhigh_switch:',
                      'eapply hswi_step', 'exact DWselected', 'Theorem DAboth_IE:', 'Theorem DAwrap_run:',
                      'rewrite DWcounter_wrap in Count', 'DAfacts_frame', 'V293_tick_raw_owned_writable']:
            self.assertIn(token, source)
        observed = source.split('Definition DAobserved:', 1)[1].split('Definition DArun', 1)[0]
        for token in ['60%positive,44%Z', '11%positive,0%Z', '12%positive,0%Z', '13%positive,0%Z',
                      '30%positive,0%Z', '30%positive,1%Z', '31%positive,0%Z',
                      'V293_bytes_writable M 13%positive 0%Z 4']:
            self.assertIn(token, observed)
        switch = source.split('Theorem DAallocated_switch:', 1)[1].split('Proof.', 1)[0]
        for token in ['V293_task_records Mf', 'V293_bitmap_tasks 64 0', 'DAfacts Mf',
                      'Some(Vptr OwnershipWaiting)', 'Some(V293_byteval 4)', 'Int.repr 99',
                      'SKIP,(kenil,DAcontinuation)', 'OwnershipWaiting=Some DWready']:
            self.assertIn(token, switch)

    def test_prospective_single_slot_ablation_is_late_and_bounded(self):
        protocol = read('protocol.json')
        self.assertTrue(protocol['prospective'])
        self.assertEqual(sha(D / 'protocol.json'), '819c8640e090f05e57459f0cdb1148bd88bfb1074d372f7bb5a00e3b0608553a')
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
        self.assertIn('change only pointer-table slot 6', protocol['ablation']['factor'])
        self.assertIn('negative local prefix only', protocol['ablation']['scope'])
        source = (R / Q).read_text()
        for token in ['Lemma DAonly_slot:', 'firstn 9(DAframe false c)', 'skipn 10(DAframe false c)',
                      '83%positive,24%Z', 'DAallocated_run true c enabled', 'rewrite Target;discriminate',
                      'exact DSmutant_outside_table']:
            self.assertIn(token, source)
        statement = source.split('Theorem DAwrong_target:', 1)[1].split('Proof.', 1)[0]
        for token in ['DArun true c enabled', 'V293_task_records Mf', 'V293_bitmap_tasks 64 0',
                      'Int.add c Int.one', 'DAfacts Mf', '<>Some(Vptr OwnershipWaiting)',
                      '~V293_priority_table']:
            self.assertIn(token, statement)
        self.assertNotIn('lpstep', statement)
        self.assertNotIn('hpstep', statement)

    def test_recursive_trust_and_stable_compiles(self):
        roots = []
        for p in [P, Q]:
            source = (R / p).read_text()
            self.assertNotRegex(source, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', source, re.M)]
        self.assertEqual(len(roots), 14)
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(x['exit'] == 0 for x in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']), {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        for name, p in [('production', P), ('probe', Q)]:
            for i in [1, 2]:
                result = read(f'stable-{name}-{i}.json')
                self.assertEqual(result['exit'], 0)
                self.assertEqual(result['initial_source_sha256'], sha(R / p))
                self.assertEqual(result['source_sha256'], sha(R / p))

    def test_history_and_honest_boundary(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in read('baseline.json')['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        project = (R / '_CoqProject').read_bytes()
        self.assertTrue(project.startswith((D / '_CoqProject.baseline').read_bytes() + (P + '\n').encode()))
        self.assertEqual(project.splitlines().count(P.encode()), 1)
        self.assertEqual({str(p.relative_to(R)): sha(p) for p in R.rglob('*.pyc')}, read('bytecode-baseline.json'))
        boundary = read('function-boundary.json')
        for name in ['raw_entry_connected_to_blocking', 'raw_entry_connected_to_blocking_switch',
                     'scheduler_execution_from_this_call']:
            self.assertTrue(boundary[name])
        for name in ['full_api_proved', 'whole_call_global_reachability_proved', 'priority_cache_synchronized']:
            self.assertFalse(boundary[name])
        self.assertTrue(all(row['located'] and not any(v for k, v in row.items() if k != 'located')
                            for row in boundary['stages'].values()))
        doc = (R / 'audit/STAGE324_TIME_DELAY_ALLOCATED_SCHED.md').read_text()
        for token in ['不是完整 API', '不是全局记录不变量', '不是全局 ProgSim', '客户端堆',
                      '优先级缓存', '负例仅局部前缀', 'GOOD_OS', 'uCOS3']:
            self.assertIn(token, doc)
        for name in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / name).read_bytes().endswith((D / (name + '.baseline')).read_bytes()))


if __name__ == '__main__':
    unittest.main()
