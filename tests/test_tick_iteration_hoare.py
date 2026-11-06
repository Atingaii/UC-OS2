"""原 tick 单次循环体的回归门；文本检查不替代 Coq 内核检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage159-tick-iteration-hoare'
SOURCES = ('certiucos/v293/proofs/V293TimeTickIterationHoare.v',
           'audit/probes/V293TimeTickIterationHoareProbe.v')


class TickIterationHoareTests(unittest.TestCase):
    def setUp(self):
        self.prod, self.probe = [(R / p).read_text() for p in SOURCES]

    def test_unchanged_release_source_ast_and_previous_evidence(self):
        identity = json.loads((D / 'source-identity.json').read_text())
        self.assertEqual(identity, json.loads((D.parent / 'stage158-tick-delay-hoare/source-identity.json').read_text()))
        raw = (R / identity['current_upstream_file']).read_bytes()
        self.assertEqual(hashlib.sha256(raw).hexdigest(), identity['current_upstream_file_sha256'])
        i = identity['identity']
        self.assertEqual(hashlib.sha256(b''.join(raw.splitlines(keepends=True)[i['first_line'] - 1:i['last_line']])).hexdigest(), i['source_lines_sha256'])
        baseline = json.loads((D / 'baseline.json').read_text())['files']
        for p in ('certiucos/v293/code/V293OSTimeTick.v',
                  'certiucos/v293/proofs/V293TimeTickDelayHoare.v',
                  'audit/probes/V293TimeTickDelayHoareProbe.v',
                  'audit/logs/stage158-tick-delay-hoare/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), baseline[p])
        self.assertFalse(identity['new_AST'])

    def test_public_contract_has_no_execution_or_evaluator_premise(self):
        statement = self.prod.split('Theorem V293_tick_iteration_hoare :', 1)[1].split('Proof.', 1)[0]
        premises, result = statement.split(' InfRules ', 1)
        for term in ('V293_local_steps', 'RuleSem', 'evalval', 'evaltype'):
            self.assertNotIn(term, premises)
        for term in ('(0<=d<=Int.max_unsigned)%Z', 's<256', 'pend<256', 'y<2', 'x<8',
                     'V293_tick_delay_env', '(R ==> CurLINV li tid)', 'GoodFrm R', '(gettopis si <= INUM)%nat'):
            self.assertIn(term, premises)
        self.assertIn('(V293_tick_iteration ptcb rows group)', result)
        self.assertIn('base next (Int.repr (V293_tick_after_delay d)) next', result)
        self.assertEqual(result.count('OS[ir,enabled,si,ci]'), 2)

    def test_direct_rules_original_right_association_and_soundness_direction(self):
        for term in ('V293_raw_assign_hoare', 'V293_tick_raw_field_eval', 'V293_tick_delay_fragment_hoare',
                     'sseq (V293_tick_delay ptcb rows group) (sseq (V293_tick_advance ptcb) tail)',
                     'encrit1_rule', 'encrit2_rule', 'excrit1_rule', 'excrit2_rule',
                     'invlth_isr I 0 (gettopis si)', 'apply Work'):
            self.assertIn(term, self.prod)
        semantic = self.prod.split('Theorem V293_tick_iteration_semantics :', 1)[1]
        self.assertIn('simulation.RuleSem', semantic)
        self.assertIn('apply RuleSound. apply V293_tick_iteration_hoare', semantic)
        self.assertNotIn('RuleSem', self.prod.split('Theorem V293_tick_iteration_semantics :', 1)[0])

    def test_literal_entry_preserves_bytes_with_legal_interrupt_stack(self):
        entry = self.probe.split('Theorem IHentry :', 1)[1].split('Theorem IHrules :', 1)[0]
        for term in ('DHentry d s S', 'goodfrm_prop', 'IHframe_good', 'astar_l_aie_intro', 'astar_l_acs_intro'):
            self.assertIn(term, entry)
        self.assertNotIn('Execution', entry)
        self.assertIn('(enabled,[1],[false])', self.probe)
        self.assertIn('change (1<=INUM)%nat;unfold INUM;lia', self.probe)
        self.assertNotIn('enabled,[3]', self.probe)
        self.assertIn('IHoperational_entry enabled s S', self.probe)

    def test_same_actual_output_single_observation_controls(self):
        for root in ('IHwrong_pointer', 'IHwrong_ie'):
            part = self.probe.split('Theorem ' + root + ' :', 1)[1].split('Qed.', 1)[0]
            for term in ('exists Mf,', 'IHliteralExecution', 'IHexecution P ks enabled 1 Mf', 'Int.repr 99'):
                self.assertIn(term, part)
            for term in ('store ', 'del ', 'set Mf'):
                self.assertNotIn(term, part)
        pointer = self.probe.split('Theorem IHwrong_pointer :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('<>Some(Vptr (81%positive,Int.repr 8))', pointer)
        self.assertIn('(81%positive,28%Z)=Some(Vptr TickNext)', pointer)
        control = self.probe.split('Theorem IHwrong_ie :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('~ (IHopstate enabled Mf |= Aie (negb enabled) ** Atrue)', control)
        self.assertIn('Acs (false::nil) ** Atrue', control)

    def test_nonvacuous_branch_cases_and_bounded_scope(self):
        for term in ('forall enabled d s', '[0%Z;1%Z;3%Z;4294967295%Z]',
                     '[0;1;2;4;8;9;16;32;64;128;255]', 'apply IHentry', 'apply IHrules'):
            self.assertIn(term, self.probe)
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertEqual(len(protocol['controls']), 3)
        self.assertEqual(len(protocol['limits']), 3)
        self.assertIn('CPU hook remains enabled and open', protocol['unchanged'])
        self.assertIn('arbitrary untouched frame, not a source of production TCB ownership', self.prod)

    def test_stable_compiles_roots_and_no_trust_extension(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        roots = []
        for kind, p in zip(('iteration', 'probe'), SOURCES):
            raw = (R / p).read_bytes()
            row = json.loads((D / (stable[kind] + '.json')).read_text())
            self.assertEqual(row['exit'], 0)
            self.assertEqual(hashlib.sha256(raw).hexdigest(), row['source_sha256'])
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(raw, (D / (stable[kind] + '.v.snapshot.txt')).read_bytes())
            text = raw.decode()
            self.assertNotRegex(text, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            self.assertNotRegex(text, r'^Inductive ')
            roots += re.findall(r'^(?:Local )?(?:Theorem|Lemma) (\w+)\s*:', text, re.M)
        self.assertEqual(len(roots), 12)
        self.assertNotIn('CertiOS.audit.', self.prod)
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(SOURCES[0]), 1)
        self.assertNotIn(SOURCES[1], (R / '_CoqProject').read_text().splitlines())
