"""tick 同一共享资源更新回归；结构检查不替代 Coq 内核检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage163-tick-ready-update'
SOURCES = ('certiucos/v293/proofs/V293TimeTickReadyUpdate.v',
           'audit/probes/V293TimeTickReadyUpdateProbe.v')


class TickReadyUpdateTests(unittest.TestCase):
    def setUp(self):
        self.prod, self.probe = [(R / p).read_text() for p in SOURCES]

    def test_fixed_sources_and_previous_evidence(self):
        base = json.loads((D / 'baseline.json').read_text())['files']
        for p in ('certiucos/v293/code/V293OSTimeTick.v',
                  'certiucos/v293/proofs/V293TimeReadyShared.v',
                  'certiucos/v293/proofs/V293TimeTickWhileHoare.v',
                  'certiucos/v293/proofs/V293TimeTickLosslessFields.v',
                  'audit/logs/stage162-time-ready-shared/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), base[p])
        self.assertEqual(json.loads((D / 'source-identity.json').read_text()),
                         json.loads((D.parent / 'stage162-time-ready-shared/source-identity.json').read_text()))

    def test_real_rule_no_execution_oracle(self):
        contract = self.prod.split('Theorem V293_tick_ready_wait_iteration_hoare :', 1)[1].split('Proof.', 1)[0]
        pre, result = contract.split('  InfRules ', 1)
        for term in ('V293_local_steps', 'evalval', 'evaltype', 'RuleSem', 'InfRules'):
            self.assertNotIn(term, pre)
        for term in ('NoAbs li', 'GoodFrm frame', 'can_change_aop frame',
                     '((CurTid ct ** frame) ==> CurLINV li tid)', 'gettopis si<=INUM'):
            self.assertIn(term, pre)
        self.assertIn('OS[ir,false,si,ci]', result)
        self.assertIn('V293_tick_iteration ptcb rows group', result)
        self.assertIn('apply V293_tick_node_iteration_hoare', self.prod)
        self.assertIn('apply RuleSound', self.prod)

    def test_legal_abstract_step_and_lossless_return(self):
        for term in ('V293_tick_wait_absinfer', 'V293_tick_wait_transition',
                     'V293_tick_wait_records_close', 'V293_tick_ready_wait_before_open',
                     'V293_tick_ready_wait_raw_close', 'V293_tick_ready_wait_finish',
                     'V293_tick_wait_layout_permutation', 'V293_tick_raw_to_owned'):
            self.assertIn(term, self.prod)
        post = self.prod.split('Definition V293_tick_ready_wait_post', 1)[1].split('Lemma ', 1)[0]
        post = re.sub(r'\(\*.*?\*\)', '', post, flags=re.S)
        self.assertIn('V293_time_ready_core br bg bp bn **', post)
        self.assertIn('V293_tick_residual_cells', post)
        self.assertIn('** frame', post)
        self.assertNotIn('Atrue', post)
        for src in (self.prod, self.probe):
            self.assertNotRegex(src, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            self.assertNotRegex(src, re.compile(r'^Inductive ', re.M))
        self.assertNotIn('CertiOS.audit.', self.prod)

    def test_nonempty_literal_entry_and_actual_execution(self):
        for term in ('RUentry', 'RUrules', 'RUliteral_execution', 'OwnershipCellsSeparated',
                     'RUphysical_good', 'RUabstract', 'RUnoabs', 'RUcur',
                     'V293_tick_node_iteration_owned_execution', 'V293_tick_ready_wait_raw_close'):
            self.assertIn(term, self.probe)
        self.assertIn('p=4 /\\ t=OwnershipReady', self.probe)
        self.assertIn('false,[1],[false]', self.probe)
        self.assertIn('Int.repr 37', self.probe)
        self.assertIn('Int.repr 99', self.probe)

    def test_neutralized_update_keeps_nonempty_bitmap(self):
        for term in ('RUreject_neutralized', 'RUexpiry_control', 'RUobservations',
                     'V293_byteval 80', 'RUonly_ready', 'RUexecution'):
            self.assertIn(term, self.probe)
        correct = self.probe.split('Definition RUout d M : RstateOP :=', 1)[1].split('Definition ', 1)[0]
        neutral = self.probe.split('Definition RUneutralized d M : RstateOP :=', 1)[1].split('Definition ', 1)[0]
        self.assertIn('END None', correct)
        self.assertIn('END None', neutral)
        self.assertEqual(correct.split('set(RUabs d)', 1)[0].strip(),
                         neutral.split('RUabs d', 1)[0].strip())
        self.assertIn('~ RUneutralized 1 Mf |=', self.probe)
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertEqual(len(protocol['controls']), 4)
        self.assertIn('bitmap remains nonempty', protocol['controls'][1])

    def test_zero_countdown_and_exact_residual(self):
        for term in ('RUbranch_cases', 'RUresidual_expiry', 'RUresidual_waiting'):
            self.assertIn(term, self.probe)
        self.assertIn('(41%positive,52%Z)', self.probe)
        self.assertIn('(41%positive,57%Z)', self.probe)
        self.assertIn('(41%positive,36%Z)', self.probe)

    def test_current_compilation_and_independent_trust(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for key, path in zip(('update', 'probe'), SOURCES):
            row = json.loads((D / (stable[key] + '.json')).read_text())
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256((R / path).read_bytes()).hexdigest())
        trust = json.loads((D / 'trust.json').read_text())
        self.assertTrue(trust['passed'])
        self.assertEqual((trust['checked_active_modules'], trust['checked_extra_modules']), (333, 53))
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))


if __name__ == '__main__':
    unittest.main()
