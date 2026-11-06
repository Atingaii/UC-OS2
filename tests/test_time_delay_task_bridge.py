"""延时临界片段的同堆/原抽象一步连接，不是完整 API 或全局不变量。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage317-time-delay-task-bridge'
OLD = R / 'audit/logs/stage316-time-delay-block'
P = 'certiucos/v293/proofs/V293TimeDlyTaskBridge.v'
Q = 'audit/probes/V293TimeDlyTaskBridgeProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class TimeDelayTaskBridgeTests(unittest.TestCase):
    def test_exact_source_identity_and_partial_boundary(self):
        identity = read('source-identity.json')
        inventory = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        self.assertEqual(identity, next(x for x in inventory['functions'] if x['name'] == 'OSTimeDly'))
        self.assertEqual(identity, json.loads((OLD / 'source-identity.json').read_text()))
        self.assertEqual(sha(D / 'OSTimeDly.source.c.snapshot.txt'), identity['source_lines_sha256'])
        self.assertEqual(hashlib.sha256((D / 'OSTimeDly.configured.c.snapshot.txt').read_bytes()[:-1]).hexdigest(),
                         identity['preprocessed_definition_sha256'])
        boundary = read('function-boundary.json')
        self.assertTrue(boundary['stages']['located'])
        self.assertFalse(boundary['full_api_proved'])
        self.assertFalse(boundary['stages']['full_target_linked'])
        self.assertIn('original_spec_step', boundary['partial_evidence'])

    def test_same_terminal_heap_and_derived_shared_slots(self):
        s = (R / P).read_text()
        statement, proof = s.split('Theorem V293_OSTimeDly_updates_refines :', 1)[1].split('Proof.', 1)
        inputs, outputs = statement.split('exists Mf,', 1)
        for forbidden in ['cstepstar', 'spec_step', 'V293_task_records Mf', 'store ']:
            self.assertNotIn(forbidden, inputs)
        for token in ['cstepstar P', '(ge,le,Mf)', 'spec_step sd', 'V293_task_records Mf blocked',
                      'V293_bitmap_tasks', 'V293_shared_fields(bt,Int.repr base)blocked events now **R']:
            self.assertIn(token, outputs)
        for token in ['V293_OSTimeDly_blocking_bridge', 'V293_tick_records_replace',
                      'V293_shared_fields_get', 'V293_star_abst_get_l', 'V293_shared_replace_slot']:
            self.assertIn(token, proof)
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertNotIn('set O curtid', s)

    def test_original_primitive_reads_current_and_preserves_domains(self):
        s = (R / P).read_text()
        contract = s.split('Definition V293_dly_block_step', 1)[1].split('Theorem', 1)[0]
        for token in ['get O curtid=Some(oscurt t)', 'get O abstcblsid=Some(abstcblist tasks)',
                      'get tasks t=Some(priority,rdy,message)', 'duration<>Int.zero',
                      'wait os_stat_time duration']:
            self.assertIn(token, contract)
        proof = s.split('Theorem V293_dly_block_transition :', 1)[1].split('Qed.', 1)[0]
        for token in ['spec_prim_step', 'eqdomtls', 'unfold tidsame', 'map_join_emp']:
            self.assertIn(token, proof)
        self.assertIn('V293_dly_other_abstract_slots', s)

    def test_literal_two_task_ownership_and_canary(self):
        s = (R / Q).read_text()
        for token in ['DLcells++(DLextra++(DLlow++DTframecells))', 'OwnershipCellsSpatial',
                      'V293_target_wstate_star', 'DTlow_owned', 'DTentry', 'DTliteral',
                      'V293_OSTimeDly_updates_refines', 'V293_task_records Mf DTblocked',
                      'V293_bitmap_tasks 64 0 DTblocked', 'Vint32(Int.repr 99)',
                      'DTstale_slot_mismatch', 'already ready; this is not wakeup reachability']:
            self.assertIn(token, s)
        self.assertIn('get DTfinalabs curtid=Some(oscurt OwnershipReady)', s)
        self.assertIn('get DTfinalabs ostmid=Some(ostm(Int.repr 37))', s)

    def test_single_factor_late_abstract_slot_gate(self):
        protocol, result = read('ablation-protocol.json'), read('ablation.json')
        self.assertTrue(protocol['prospective'])
        for suffix in ['', '-final']:
            base = (D / ('gate-base' + suffix + '.v.snapshot.txt')).read_text()
            mutant = (D / ('gate-mutant' + suffix + '.v.snapshot.txt')).read_text()
            self.assertEqual(base.count(protocol['old']), 1)
            self.assertEqual(base.replace(protocol['old'], protocol['new']), mutant)
            self.assertEqual(read('gate-base' + suffix + '.json')['exit'], 0)
            self.assertEqual(read('gate-mutant' + suffix + '.json')['exit'], 1)
            log = (D / ('gate-mutant' + suffix + '.log')).read_text()
            for token in ['Executed : DTexecution', 'Records : V293_task_records', 'Bitmap :',
                          'Canary : load Tint32', 'ActualSlot : get', 'while it is expected']:
                self.assertIn(token, log)
        self.assertEqual(result['protocol_sha256'], sha(D / 'ablation-protocol.json'))
        self.assertTrue(result['same_physical_execution'])
        self.assertTrue(result['physical_blocked_records_and_bitmap'])
        self.assertEqual(result['canary_after_both'], 99)
        final = read('ablation-final.json')
        self.assertTrue(final['final_replay_after_stable_probe'])
        self.assertEqual(final['production_sha256'], sha(R / P))
        self.assertEqual(final['probe_sha256'], sha(R / Q))

    def test_recursive_trust_stable_compiles_and_history(self):
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']), {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        for stem, p, runs in [('production', P, [1, 2]), ('probe', Q, [2, 3])]:
            for i in runs:
                row = read(f'stable-{stem}-{i}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / p))
                self.assertEqual(row['source_sha256'], sha(R / p))
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


if __name__ == '__main__':
    unittest.main()
