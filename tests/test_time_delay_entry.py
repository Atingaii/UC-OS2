"""延时函数体入口到调度调用前／真实提前返回；不是整核验收。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage318-time-delay-entry'
OLD = R / 'audit/logs/stage317-time-delay-task-bridge'
P = 'certiucos/v293/proofs/V293TimeDlyEntry.v'
Q = 'audit/probes/V293TimeDlyEntryProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class TimeDelayEntryTests(unittest.TestCase):
    def test_source_identity_and_bounded_function_coverage(self):
        identity = read('source-identity.json')
        inventory = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        self.assertEqual(identity, next(x for x in inventory['functions'] if x['name'] == 'OSTimeDly'))
        self.assertEqual(identity, json.loads((OLD / 'source-identity.json').read_text()))
        self.assertEqual(sha(D / 'OSTimeDly.source.c.snapshot.txt'), identity['source_lines_sha256'])
        self.assertEqual(hashlib.sha256((D / 'OSTimeDly.configured.c.snapshot.txt').read_bytes()[:-1]).hexdigest(),
                         identity['preprocessed_definition_sha256'])
        self.assertEqual(read('source-replay.json')['exit'], 0)
        boundary = read('function-boundary.json')
        self.assertTrue(boundary['stages']['located'])
        self.assertFalse(boundary['full_api_proved'])
        self.assertFalse(boundary['stages']['full_target_linked'])
        self.assertIn('after cpu_sr initializer', boundary['entry'])
        self.assertIn('BEFORE OS_Sched call', boundary['positive_endpoint'])

    def test_positive_interface_derives_actual_execution_and_restores_aux(self):
        source = (R / P).read_text()
        statement, proof = source.split('Theorem V293_OSTimeDly_body_to_sched_refines :', 1)[1].split('Proof.', 1)
        inputs, outputs = statement.split('exists Mf,', 1)
        for forbidden in ['cstepstar', 'V293_local_steps', 'spec_step', 'store ', 'ProgSim']:
            self.assertNotIn(forbidden, inputs)
        for token in ['V293_local_steps P', 'curs(scall sched nil)', '(enabled,si,ci)',
                      'spec_step sd', 'V293_task_records Mf blocked', 'V293_bitmap_tasks',
                      'V293_shared_fields(bt,Int.repr base)blocked events now **R']:
            self.assertIn(token, outputs)
        for token in ['V293_OSTimeDly_updates_refines', 'V293_dly_body_enters_positive',
                      'apply encrit_step', 'apply excrit_step', 'exact Updates']:
            self.assertIn(token, proof)
        self.assertNotIn('Require Import CertiOS.audit.', source)
        self.assertNotIn('set O curtid', source)

    def test_unsigned_guard_and_short_circuit_requirements(self):
        source = (R / P).read_text()
        self.assertIn('Lemma V293_dly_unsigned_positive', source)
        self.assertIn('Int.ltu Int.zero n=if Int.eq n Int.zero then false else true', source)
        reject = source.split('Definition V293_dly_rejects', 1)[1].split('Lemma', 1)[0]
        for token in ['ni<>0 \\/ (ni=0 /\\exists bl nl', 'nl<>0 \\/ (nl=0 /\\exists bd',
                      'load Tint32 M(bd,0%Z)=Some(Vint32 Int.zero)']:
            self.assertIn(token, reject)
        self.assertIn('DEnesting_shortcircuit', (R / Q).read_text())
        self.assertIn('(sig 110%Z(70%positive,Tint8),(emp:env),DEmem Int.zero 255 0)', (R / Q).read_text())

    def test_early_return_executes_frees_and_restores_caller(self):
        source = (R / P).read_text()
        theorem = source.split('Theorem V293_OSTimeDly_early_return :', 1)[1]
        for token in ['NoDup(map fst(getaddr le))', 'V293_bytes_writable M b',
                      '((ge,caller,Mf),ir,aux)', 'get Mf(b,i)=get M(b,i)',
                      'get Mf(b,Z.of_nat k)=None', 'V293_void_return_execution', 'exact Prefix|exact Return']:
            self.assertIn(token, theorem)
        probe = (R / Q).read_text()
        for token in ['Lemma DEwritable', 'Theorem DEearly', 'V293_tick_raw_owned_writable',
                      'DErejection duration ni nl Ni Nl Choice', 'kcall 900%Z(sseq(sskip None)(sskip None))']:
            self.assertIn(token, probe)

    def test_nonempty_heap_and_high_unsigned_literal(self):
        probe = (R / Q).read_text()
        for token in ['DEcells duration++(DLextra++(DLlow++DEframe ni nl))',
                      'OwnershipCellsSpatial', 'V293_target_wstate_star', 'DTlow_owned',
                      'Theorem DEliteral', 'forall P ks sd enabled duration', 'Theorem DEhigh_unsigned',
                      'DEmem(Int.repr 2147483648)0 0', 'V293_task_records Mf(DEblocked duration)',
                      'V293_bitmap_tasks 64 0(DEblocked duration)', 'Vint32(Int.repr 99)',
                      'get(DEfinalabs duration)curtid=Some(oscurt OwnershipReady)']:
            self.assertIn(token, probe)

    def test_single_factor_reaches_late_auxiliary_state_gate(self):
        protocol = read('ablation-protocol.json')
        self.assertTrue(protocol['prospective'])
        for suffix in ['-03', '-final']:
            base = (D / ('gate-base' + suffix + '.v.snapshot.txt')).read_text()
            mutant = (D / ('gate-mutant' + suffix + '.v.snapshot.txt')).read_text()
            self.assertEqual(base.count(protocol['old']), 1)
            self.assertEqual(base.replace(protocol['old'], protocol['new']), mutant)
            self.assertEqual(read('gate-base' + suffix + '.json')['exit'], 0)
            self.assertEqual(read('gate-mutant' + suffix + '.json')['exit'], 1)
            log = (D / ('gate-mutant' + suffix + '.log')).read_text()
            for token in ['Executed : DErun', 'Step : hmstep', 'Records : V293_task_records',
                          'Bitmap : V293_bitmap_tasks', 'Canary : load Tint32',
                          'ActualAux : DEaux', 'while it is expected']:
                self.assertIn(token, log)
        result = read('ablation-final.json')
        self.assertEqual(result['protocol_sha256'], sha(D / 'ablation-protocol.json'))
        self.assertTrue(result['single_factor'] and result['same_initial_heap_and_control_endpoint'])
        self.assertTrue(result['physical_records_bitmap_and_canary_before_gate'])
        self.assertEqual(result['canary_after_both'], 99)
        self.assertEqual(result['production_sha256'], sha(R / P))
        self.assertEqual(result['probe_sha256'], sha(R / Q))
        probe = (R / Q).read_text()
        self.assertIn('Lemma DEbaseline_exact : DEvariant true=DEbody.', probe)
        self.assertIn('Lemma DEomitted_restore_detected : forall enabled', probe)

    def test_recursive_trust_and_repeated_compiles(self):
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

    def test_frozen_history_protocols_and_documented_limits(self):
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
        doc = (R / 'audit/STAGE318_TIME_DELAY_ENTRY.md').read_text()
        for token in ['不是完整回切', '不是全局记录不变量', '不是从之前真实 Waiting 状态唤醒',
                      '不是 raw port', '全局 ProgSim', 'GOOD_OS', 'uCOS3']:
            self.assertIn(token, doc)


if __name__ == '__main__':
    unittest.main()
