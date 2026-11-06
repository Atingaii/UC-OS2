"""原 tick while 的回归门；文本检查不替代 Coq 内核验证。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage160-tick-while-hoare'
SOURCES = ('certiucos/v293/proofs/V293TimeTickWhileHoare.v',
           'audit/probes/V293TimeTickWhileHoareProbe.v')


class TickWhileHoareTests(unittest.TestCase):
    def setUp(self):
        self.prod, self.probe = [(R / p).read_text() for p in SOURCES]

    def test_fixed_source_ast_and_previous_evidence(self):
        base = json.loads((D / 'baseline.json').read_text())['files']
        for p in ('certiucos/v293/code/V293OSTimeTick.v',
                  'certiucos/v293/proofs/V293TimeTickIterationHoare.v',
                  'certiucos/v293/proofs/V293TimeTickLoop.v',
                  'audit/probes/V293TimeTickLoopProbe.v',
                  'audit/logs/stage159-tick-iteration-hoare/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), base[p])
        identity = json.loads((D / 'source-identity.json').read_text())
        self.assertEqual(identity, json.loads((D.parent / 'stage159-tick-iteration-hoare/source-identity.json').read_text()))
        raw = (R / identity['current_upstream_file']).read_bytes()
        self.assertEqual(hashlib.sha256(raw).hexdigest(), identity['current_upstream_file_sha256'])

    def test_public_contract_has_no_oracle_premise(self):
        part = self.prod.split('Theorem V293_tick_while_hoare :', 1)[1].split('Proof.', 1)[0]
        pre, result = part.split(' InfRules ', 1)
        for term in ('V293_local_steps', 'RuleSem', 'evalval', 'evaltype', 'InfRules'):
            self.assertNotIn(term, pre)
        for term in ('Forall V293_tick_task_valid tasks', 'g<256', 'lo<256', 'hi<256',
                     'V293_tick_delay_env', 'GoodFrm R', '(R ==> CurLINV li tid)', 'gettopis si<=INUM'):
            self.assertIn(term, pre)
        self.assertIn('(swhile (V293_tick_guard ptcb) (V293_tick_iteration ptcb rows group))', result)
        self.assertIn('V293_tick_chain_cells (map V293_tick_task_after tasks) idle', result)
        self.assertIn('V293_tick_chain_bitmap tasks g lo hi', pre)

    def test_while_direct_composition_not_execution_renaming(self):
        for term in ('apply V293_tick_iteration_hoare', 'apply V293_tick_node_iteration_hoare',
                     'apply V293_tick_while_step_hoare', 'apply while_rule with (tp:=Tint32)',
                     'V293_tick_while_guard_resource', 'V293_tick_next_bitmap_bounds'):
            self.assertIn(term, self.prod)
        semantics = self.prod.split('Theorem V293_tick_while_semantics :', 1)[1]
        self.assertIn('apply RuleSound', semantics)
        self.assertIn('V293_tick_while_hoare Spec', semantics)
        self.assertNotIn('V293_local_steps', self.prod)
        self.assertNotIn('CertiOS.audit.', self.prod)
        self.assertNotRegex(self.prod, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture)\b')

    def test_exact_invariant_guard_and_resource_preservation(self):
        invariant = self.prod.split('Definition V293_tick_while_invariant', 1)[1].split('Theorem ', 1)[0]
        for term in ('EX processed:list V293_record_cell', 'EX remaining:list V293_tick_task',
                     'finalcells=processed++V293_tick_chain_cells (map V293_tick_task_after remaining) idle',
                     'finalbitmap=V293_tick_chain_bitmap remaining g lo hi'):
            self.assertIn(term, invariant)
        guard = self.prod.split('Lemma V293_tick_while_guard_owned', 1)[1].split('Local Lemma', 1)[0]
        for term in ('V293_rdy_raw_load', 'V293_tick_guard_eval', 'Nat.eqb_neq', 'Int.repr_unsigned'):
            self.assertIn(term, guard)
        self.assertIn('V293_tick_head_after in Cells', self.prod)
        self.assertIn('OS[ir,enabled,si,ci]', self.prod)

    def test_nonempty_literal_entry_both_ie_and_legal_stack(self):
        for term in ('OwnershipCellsSpatial', 'DHcurrent_spatial', 'DHbinding_spatial', 'DHlinv_spatial',
                     'WHmemory := merge', '(enabled,[1],[false])', 'WHnonvacuous',
                     'forall enabled', 'WHvalid', 'GoodFrm WHframe'):
            self.assertIn(term, self.probe)
        loop = (R / 'audit/probes/V293TimeTickLoopProbe.v').read_text()
        initial = loop.split('Definition LoopTasks :', 1)[1].split('Definition LoopFinalTasks', 1)[0]
        self.assertEqual(initial.count('Build_V293_tick_task'), 6)
        self.assertIn('change (1<=INUM)%nat;unfold INUM;lia', self.probe)
        self.assertNotIn('enabled,[3]', self.probe)

    def test_same_actual_output_single_observation_controls(self):
        for root in ('WHwrong_pointer', 'WHwrong_row'):
            part = self.probe.split('Theorem ' + root + ' :', 1)[1].split('Qed.', 1)[0]
            for term in ('exists Mf,', 'WHliteral_execution P ks enabled', 'WHexecution P ks enabled Mf',
                         'Int.repr 99'):
                self.assertIn(term, part)
            for term in ('store ', 'set Mf', 'del '):
                self.assertNotIn(term, part)
        self.assertIn('V293_tick_while_owned_execution LoopTasks', self.probe)
        exit_guard = self.probe.split('Theorem WHguard_exit :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('WHliteral_execution P ks enabled', exit_guard)
        self.assertIn('V293_tick_guard_eval', exit_guard)
        self.assertIn('Some(Vint32 Int.zero)', exit_guard)
        limits = json.loads((D / 'protocol.json').read_text())['limits']
        self.assertTrue(any('production Inv' in x for x in limits))
        self.assertTrue(any('GOOD_OS' in x for x in limits))

    def test_stable_compilation_and_independent_kernel_check(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, source in zip(('while', 'probe'), SOURCES):
            result = json.loads((D / (stable[kind] + '.json')).read_text())
            digest = hashlib.sha256((R / source).read_bytes()).hexdigest()
            self.assertEqual(result['exit'], 0)
            self.assertEqual(digest, result['initial_source_sha256'])
            self.assertEqual(digest, result['source_sha256'])
        trust = json.loads((D / 'trust.json').read_text())
        self.assertTrue(trust['passed'])
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
        expected = [Path(p).stem + '.' + n for p in SOURCES
                    for n in re.findall(r'^(?:Local )?(?:Lemma|Theorem) (\w+)\s*:', (R / p).read_text(), re.M)]
        self.assertEqual(trust['roots'], expected)
        self.assertEqual(trust['roots_printed'], len(expected))


if __name__ == '__main__':
    unittest.main()
