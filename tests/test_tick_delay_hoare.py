"""片段 Hoare 回归；文本门不能替代独立 Coq 内核检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage158-tick-delay-hoare'
SOURCES = ('certiucos/v293/proofs/V293TimeTickDelayHoare.v',
           'audit/probes/V293TimeTickDelayHoareProbe.v')


class TickDelayHoareTests(unittest.TestCase):
    def setUp(self):
        self.prod, self.probe = [(R / p).read_text() for p in SOURCES]

    def test_unchanged_release_source_ast_and_previous_evidence(self):
        identity = json.loads((D / 'source-identity.json').read_text())
        self.assertEqual(identity, json.loads((D.parent / 'stage157-tick-reentry/source-identity.json').read_text()))
        raw = (R / identity['current_upstream_file']).read_bytes()
        self.assertEqual(hashlib.sha256(raw).hexdigest(), identity['current_upstream_file_sha256'])
        i = identity['identity']
        self.assertEqual(hashlib.sha256(b''.join(raw.splitlines(keepends=True)[i['first_line'] - 1:i['last_line']])).hexdigest(), i['source_lines_sha256'])
        self.assertFalse(identity['new_AST'])
        baseline = json.loads((D / 'baseline.json').read_text())['files']
        for p in ('certiucos/v293/code/V293OSTimeTick.v',
                  'certiucos/v293/proofs/V293TimeTickReentryReturn.v',
                  'audit/logs/stage157-tick-reentry/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), baseline[p])

    def test_public_contract_has_no_execution_or_evaluator_premise(self):
        statement = self.prod.split('Theorem V293_tick_delay_fragment_hoare :', 1)[1].split('Proof.', 1)[0]
        premises, result = statement.split(' InfRules ', 1)
        for term in ('V293_local_steps', 'RuleSem', 'evalval', 'evaltype'):
            self.assertNotIn(term, premises)
        for term in ('(0<=d<=Int.max_unsigned)%Z', 's<256', 'pend<256', 'y<2', 'x<8',
                     'V293_tick_delay_env', '(R ==> CurLINV li tid)'):
            self.assertIn(term, premises)
        self.assertIn('(V293_tick_delay ptcb rows group)', result)
        self.assertEqual(result.count(' next'), 2)
        self.assertEqual(result.count(') R)'), 2)

    def test_direct_rules_all_branches_and_soundness_direction(self):
        for term in ('V293_tick_known_if_hoare', 'V293_tick_known_ift_hoare', 'V293_raw_assign_hoare',
                     'V293_rdy_raw_load', 'Z.eqb d 0', 'Z.eqb d 1', 'V293_tick_status_arithmetic',
                     'V293_tick_expired_stat', 'V293_tick_expired_pend', 'V293_tick_expired_group',
                     'V293_tick_expired_row'):
            self.assertIn(term, self.prod)
        semantic = self.prod.split('Theorem V293_tick_delay_fragment_semantics :', 1)[1]
        self.assertIn('simulation.RuleSem', semantic)
        self.assertIn('apply RuleSound. apply V293_tick_delay_fragment_hoare', semantic)
        self.assertNotIn('RuleSem', self.prod.split('Theorem V293_tick_delay_fragment_semantics :', 1)[0])

    def test_literal_entry_separates_readonly_current_and_canary(self):
        entry = self.probe.split('Theorem DHentry :', 1)[1].split('Theorem DHrules :', 1)[0]
        for term in ('OwnershipCellsSpatial', 'OwnershipCellsOutside', 'V293_tick_cells_append',
                     'DHbinding_spatial', 'DHlinv_spatial', 'DHcurrent_spatial', 'DHowned_raw'):
            self.assertIn(term, entry)
        self.assertNotIn('Execution', entry)
        self.assertIn('94%positive 0 false', self.probe)
        self.assertIn('CurTid DHtid ** LINV V293_witness_li DHtid [] ** ExpiryFrame', self.probe)
        self.assertIn('A_notin_lenv 902%Z', self.probe)
        self.assertIn('A_notin_lenv 903%Z', self.probe)

    def test_same_actual_output_single_observation_controls(self):
        for root, right, wrong in (('DHwrong_row', '132', '128'), ('DHwrong_pend', '1', '0')):
            part = self.probe.split('Theorem ' + root + ' :', 1)[1].split('Qed.', 1)[0]
            self.assertIn('exists Mf,', part)
            self.assertIn('ExpiryLiteralExecution', part)
            self.assertIn('Some(V293_byteval ' + right + ')', part)
            self.assertIn('<>Some(V293_byteval ' + wrong + ')', part)
            self.assertIn('Int.repr 99', part)
            self.assertNotIn('store ', part)
            self.assertNotIn('del ', part)

    def test_nonvacuous_branch_cases_and_explicit_scope(self):
        for term in ('[0%Z;1%Z;3%Z;4294967295%Z]', '[0;1;2;4;8;9;16;32;64;128;255]',
                     'apply DHentry', 'apply DHrules'):
            self.assertIn(term, self.probe)
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertEqual(len(protocol['controls']), 3)
        self.assertEqual(len(protocol['limits']), 3)
        self.assertIn('CPU hook remains enabled and open', protocol['unchanged'])
        self.assertIn('not the hook, loop, ISR, or whole-function contract', self.prod)

    def test_stable_compiles_roots_and_no_trust_extension(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        roots = []
        for kind, p in zip(('delay', 'probe'), SOURCES):
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
        self.assertEqual(len(roots), 21)
        self.assertNotIn('CertiOS.audit.', self.prod)
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(SOURCES[0]), 1)
        self.assertNotIn(SOURCES[1], (R / '_CoqProject').read_text().splitlines())
