"""原 post-hook 后缀回归门；文本检查不替代 Coq 内核验证。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage161-tick-post-hook-hoare'
SOURCES = ('certiucos/v293/proofs/V293TimeTickPostHookHoare.v',
           'audit/probes/V293TimeTickPostHookHoareProbe.v')


class TickPostHookHoareTests(unittest.TestCase):
    def setUp(self):
        self.prod, self.probe = [(R / p).read_text() for p in SOURCES]

    def test_fixed_release_ast_old_proofs_and_evidence(self):
        base = json.loads((D / 'baseline.json').read_text())['files']
        for p in ('certiucos/v293/code/V293OSTimeTick.v',
                  'certiucos/v293/proofs/V293TimeTickWhileHoare.v',
                  'certiucos/v293/proofs/V293TimeTickSuffix.v',
                  'audit/probes/V293TimeTickWhileHoareProbe.v',
                  'audit/logs/stage160-tick-while-hoare/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), base[p])
        identity = json.loads((D / 'source-identity.json').read_text())
        self.assertEqual(identity, json.loads((D.parent / 'stage160-tick-while-hoare/source-identity.json').read_text()))
        self.assertFalse(identity['new_AST'])

    def test_public_contract_no_execution_or_guard_oracle(self):
        contract = self.prod.split('Theorem V293_tick_post_hook_hoare :', 1)[1].split('Proof.', 1)[0]
        pre, result = contract.split(' InfRules ', 1)
        for term in ('V293_local_steps', 'RuleSem', 'evalval', 'evaltype', 'InfRules'):
            self.assertNotIn(term, pre)
        for term in ('Forall V293_tick_task_valid tasks', 'run<256', 'g<256', 'lo<256', 'hi<256',
                     'V293_tick_post_env', 'GoodFrm R', '(R ==> CurLINV li tid)', 'gettopis si<=INUM'):
            self.assertIn(term, pre)
        self.assertIn('(V293_tick_post_hook ptcb rows group now running head)', result)
        self.assertIn('(Int.add tick Int.one)', result)
        self.assertIn('bc scan tasks idle', result)

    def test_direct_original_order_and_positive_soundness(self):
        for term in ('V293_tick_clock_assign_hoare', 'V293_tick_head_assign_hoare',
                     'V293_tick_running_guard_owned', 'V293_tick_known_ift_hoare',
                     'V293_tick_while_hoare Spec', 'apply encrit1_rule', 'apply encrit2_rule',
                     'apply excrit1_rule', 'apply excrit2_rule'):
            self.assertIn(term, self.prod)
        semantics = self.prod.split('Theorem V293_tick_post_hook_semantics :', 1)[1]
        self.assertIn('apply RuleSound', semantics)
        self.assertIn('apply V293_tick_post_hook_hoare', semantics)
        self.assertNotIn('V293_local_steps', self.prod)
        self.assertNotIn('CertiOS.audit.', self.prod)
        self.assertNotRegex(self.prod, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort)\b')
        self.assertNotRegex(self.prod, re.compile(r'^Inductive ', re.M))

    def test_exact_running_equality_and_frame(self):
        result = self.prod.split('Definition V293_tick_post_result', 1)[1].split('Theorem ', 1)[0]
        for term in ('if Nat.eqb run 1 then', 'else scan', 'else tasks', 'else (g,(lo,hi))',
                     'map V293_tick_task_after tasks'):
            self.assertIn(term, result)
        for term in ('tick_post_swap', 'tick_post_unswap', 'V293_tick_post_globals',
                     'V293_raw_cells_good_frame', 'V293_raw_cells_CurLINV',
                     'invlth_isr I 0 (gettopis si)'):
            self.assertIn(term, self.prod)

    def test_literal_entry_nonempty_chain_current_and_legal_stack(self):
        for term in ('OwnershipCellsSpatial', 'PHcurrent_spatial', 'PHbinding_spatial', 'PHlinv_spatial',
                     'PHmemory tick run := merge', '(enabled,[1],[false])', 'PHnonvacuous',
                     'PHentry', 'PHrules', 'exact WHvalid', 'GoodFrm PHframe',
                     'change (1<=INUM)%nat;unfold INUM;lia'):
            self.assertIn(term, self.probe)
        self.assertNotIn('(enabled,[3]', self.probe)
        loop = (R / 'audit/probes/V293TimeTickLoopProbe.v').read_text()
        initial = loop.split('Definition LoopTasks :', 1)[1].split('Definition LoopFinalTasks', 1)[0]
        self.assertEqual(initial.count('Build_V293_tick_task'), 6)

    def test_boundary_cases_and_independent_single_field_controls(self):
        for term in ('PHliteral_execution', 'V293_tick_post_hook_owned_execution', 'PHrunning_wrapped',
                     'PHstopped_wrapped', 'PHguard_before_head', r'run=0 \/ run=255', 'PHuint32_wrap', 'PHexpectedcells'):
            self.assertIn(term, self.probe)
        for name, dependency in (('PHwrong_clock_stopped', 'PHliteral_execution'),
                                 ('PHwrong_skipped_loop', 'PHrunning_wrapped')):
            control = self.probe.split('Theorem ' + name + ' :', 1)[1].split('Qed.', 1)[0]
            for term in ('exists Mf,', 'PHexecution', 'Int.repr 99', dependency, '<>Some'):
                self.assertIn(term, control)
            for term in ('store ', 'del ', 'set Mf'):
                self.assertNotIn(term, control)

    def test_stable_compiles_and_unchanged_allowed_assumptions(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in zip(('post', 'probe'), SOURCES):
            row = json.loads((D / (stable[kind] + '.json')).read_text())
            digest = hashlib.sha256((R / path).read_bytes()).hexdigest()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], digest)
            self.assertEqual(row['source_sha256'], digest)
        trust = json.loads((D / 'trust.json').read_text())
        old = json.loads((D.parent / 'stage160-tick-while-hoare/trust.json').read_text())
        self.assertTrue(trust['passed'])
        self.assertEqual(set(trust['allowed']), set(old['allowed']))
        self.assertLessEqual(set(trust['assumptions']), set(old['allowed']))
        self.assertEqual((trust['checked_active_modules'], trust['checked_extra_modules']), (331, 51))
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        roots = [Path(p).stem + '.' + n for p in SOURCES for n in re.findall(
            r'^(?:Local )?(?:Lemma|Theorem) (\w+)\s*:', (R / p).read_text(), re.M)]
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
