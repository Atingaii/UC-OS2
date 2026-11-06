"""共享时钟／ready 借还回归；文本检查不替代 Coq 内核验证。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage162-time-ready-shared'
SOURCES = ('certiucos/v293/proofs/V293TimeReadyShared.v',
           'audit/probes/V293TimeReadySharedProbe.v')


class TimeReadySharedTests(unittest.TestCase):
    def setUp(self):
        self.prod, self.probe = [(R / p).read_text() for p in SOURCES]

    def test_fixed_release_and_unchanged_previous_evidence(self):
        base = json.loads((D / 'baseline.json').read_text())['files']
        for p in ('certiucos/v293/code/V293OSTimeTick.v',
                  'certiucos/v293/proofs/V293TimeTickPostHookHoare.v',
                  'certiucos/v293/proofs/V293TimeShared.v',
                  'certiucos/v293/proofs/V293ReadyTaskInvariant.v',
                  'audit/probes/V293TimeTickPostHookHoareProbe.v',
                  'audit/logs/stage161-tick-post-hook-hoare/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), base[p])
        identity = json.loads((D / 'source-identity.json').read_text())
        self.assertEqual(identity, json.loads((D.parent / 'stage161-tick-post-hook-hoare/source-identity.json').read_text()))
        self.assertFalse(identity['new_AST'])

    def test_single_task_and_clock_witness_no_duplicate_abstract_slots(self):
        fields = self.prod.split('Definition V293_time_ready_fields n :=', 1)[1].split('Lemma ', 1)[0]
        self.assertEqual(fields.count('V293_shared_fields t ts es n'), 1)
        self.assertEqual(fields.count('V293_ready_payload br bg bp ts'), 1)
        self.assertNotIn('V293_ready_core', fields)
        self.assertNotIn('V293_time_core', fields)
        self.assertIn('PV (bn,Int.zero) @ Tint32 |-> Vint32 n', fields)
        for term in ('V293_time_ready_core_precise', 'V293_time_ready_core_isr',
                     'V293_time_ready_irq_open_asrt', 'V293_time_ready_irq_close_asrt',
                     'V293_time_ready_switch_store', 'GoodI (V293_time_ready_inv bn) V293_scheduler V293_shared_li'):
            self.assertIn(term, self.prod)

    def test_closed_prefix_borrows_without_raw_clock_or_execution_oracle(self):
        contract = self.prod.split('Theorem V293_tick_ready_clock_prefix :', 1)[1].split('Proof.', 1)[0]
        pre, result = contract.split(' InfRules ', 1)
        for term in ('InfRules', 'RuleSem', 'V293_local_steps', 'evalval', 'evaltype', 'tail'):
            self.assertNotIn(term, pre)
        for term in ('NoAbs li', '(forall i, ir i=false)', 'gettopis si <= INUM',
                     'GoodFrm frame', '(frame ==> CurLINV li tid)'):
            self.assertIn(term, pre)
        caller = result.split('(sseq (sprim encrit)', 1)[0]
        self.assertNotIn('PV ', caller)
        self.assertNotIn('V293_time_ready_core', caller)
        self.assertIn('OS[ir,true,si,ci]', caller)
        self.assertIn('V293_time_binding false now bn ** frame', caller)
        self.assertIn('(sprim excrit)', result)

    def test_legal_clock_refinement_and_explicit_continuation_obligation(self):
        for term in ('apply encrit1_rule', 'apply excrit1_rule', 'apply V293_OSSched_counter_increment',
                     'apply V293_tick_clock_absinfer', 'V293_time_ready_change', 'apply RuleSound'):
            self.assertIn(term, self.prod)
        contract = self.prod.split('Theorem V293_tick_ready_clock_with_tail :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(contract.count('InfRules '), 2)
        self.assertIn('tail q tid ->', contract)
        self.assertNotIn('V293_local_steps', self.prod)
        self.assertNotIn('CertiOS.audit.', self.prod)
        for source in (self.prod, self.probe):
            self.assertNotRegex(source, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            self.assertNotRegex(source, re.compile(r'^Inductive ', re.M))

    def test_literal_shared_entry_is_nonempty_and_byte_separated(self):
        for term in ('TRretime', 'TRclock_join', 'TRliteral_spatial', 'V293_target_wstate_star',
                     'V293_shared_replace_slot', 'V293_encoded_memory_mapsto', 'V293_time_ready_switch_full_close',
                     'TRclock_load', 'TRready_loads', 'TRclosed_good'):
            self.assertIn(term, self.probe)
        old = (R / 'audit/probes/V293ReadyTaskInvariantProbe.v').read_text()
        self.assertIn('RTliteral_rel', old)
        self.assertIn('p=4 /\\ t=OwnershipReady', old)
        self.assertIn('Vptr OwnershipWaiting', old)
        self.assertIn('V293_encoded_memory 150%positive', self.probe)

    def test_separate_clock_and_ready_single_factor_controls(self):
        clock = self.probe.split('Theorem TRclock_ablation :', 1)[1].split('Qed.', 1)[0]
        for term in ('bad<>n', 'TRready_loads', 'b<>150%positive', 'TRreject_clock'):
            self.assertIn(term, clock)
        self.assertIn('TRincrement_ablation_cases', self.probe)
        self.assertIn('Int.add (Int.repr 4294967295) Int.one=Int.zero', self.probe)
        ready = self.probe.split('Theorem TRready_ablation :', 1)[1].split('Qed.', 1)[0]
        for term in ('store Tint8', 'V293_byteval 32', 'get Mf a=get (TRmemory ct n) a',
                     'V293_bitmap_ready 32 0 5', 'V293_ready_group 32 0=V293_ready_group 16 0',
                     'TRreject_ready_32', 'V293_put_byte_store', 'exact Clock'):
            self.assertIn(term, ready)
        reject = self.probe.split('Lemma TRreject_ready_32 :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('Bitmap 4', reject)
        self.assertIn('get OwnershipTasks t=Some', reject)

    def test_stable_compiles_and_independent_trust(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in zip(('ready', 'probe'), SOURCES):
            row = json.loads((D / (stable[kind] + '.json')).read_text())
            digest = hashlib.sha256((R / path).read_bytes()).hexdigest()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], digest)
            self.assertEqual(row['source_sha256'], digest)
        trust = json.loads((D / 'trust.json').read_text())
        old = json.loads((D.parent / 'stage161-tick-post-hook-hoare/trust.json').read_text())
        self.assertTrue(trust['passed'])
        self.assertEqual(set(trust['allowed']), set(old['allowed']))
        self.assertLessEqual(set(trust['assumptions']), set(old['allowed']))
        self.assertEqual((trust['checked_active_modules'], trust['checked_extra_modules']), (332, 52))
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        roots = [Path(p).stem + '.' + n for p in SOURCES for n in re.findall(
            r'^(?:Local )?(?:Lemma|Theorem) (\w+)\s*:', (R / p).read_text(), re.M)]
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
