"""完整原while接共享core的结构回归；语义由独立Coq检查验收。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage165-tick-while-core'
PROD = 'certiucos/v293/proofs/V293TimeTickWhileCore.v'
PROBE = 'audit/probes/V293TimeTickWhileCoreProbe.v'


class TickWhileCoreTests(unittest.TestCase):
    def test_old_sources_and_frozen_evidence(self):
        base = json.loads((D / 'baseline.json').read_text())['files']
        for p in ('certiucos/v293/proofs/V293TimeTickCoreFocus.v',
                  'certiucos/v293/proofs/V293TimeTickWhileHoare.v',
                  'certiucos/v293/proofs/V293TimeTickWhileShared.v',
                  'certiucos/v293/code/V293OSTimeTick.v',
                  'audit/logs/stage164-tick-core-focus/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), base[p])
        self.assertEqual(json.loads((D / 'source-identity.json').read_text()),
                         json.loads((D.parent / 'stage164-tick-core-focus/source-identity.json').read_text()))

    def test_formal_original_while_not_execution_oracle(self):
        text = (R / PROD).read_text()
        contract = text.split('Theorem V293_tick_while_core_hoare :', 1)[1].split('Proof.', 1)[0]
        premises, conclusion = contract.split('  InfRules ', 1)
        for token in ('InfRules', 'RuleSem', 'V293_local_steps', 'evalval', 'evaltype'):
            self.assertNotIn(token, premises)
        self.assertIn('swhile(V293_tick_guard ptcb)(V293_tick_iteration ptcb rows group)', conclusion)
        self.assertIn('enabled', conclusion)
        self.assertIn('pose proof(V293_tick_while_hoare ', text)
        self.assertIn('apply RuleSound', text)
        for p in (PROD, PROBE):
            src = (R / p).read_text()
            self.assertNotRegex(src, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
        self.assertNotIn('CertiOS.audit.', text)

    def test_existing_ordered_action_not_batch_primitive(self):
        text = (R / PROD).read_text()
        for token in ('V293_tick_chain_absinfer', 'apply absinfer_seq;', 'apply absinfer_seq_end;',
                      'apply V293_tick_wait_absinfer', 'rewrite map_get_set\'',
                      'V293_tick_bindings_run_map', 'V293_tick_record_map_member'):
            self.assertIn(token, text)
        self.assertNotIn('spec_prim nil (fun', text)

    def test_lossless_shared_core_and_honest_raw_entry(self):
        text = (R / PROD).read_text()
        post = text.split('Definition V293_tick_while_core_post ', 1)[1].split('Lemma ', 1)[0]
        for token in ('V293_time_ready_core br bg bp bn', 'V293_tick_chain_residual bindings idle',
                      'V293_tick_pointer_cell bc idle', 'frame'):
            self.assertIn(token, post)
        self.assertNotIn('Atrue', post)
        self.assertIn('apply V293_tick_chain_records_lossless', text)
        self.assertIn('V293_tick_record_chain_ready_rel', text)
        pre = text.split('Definition V293_tick_while_core_pre ', 1)[1].split('Definition ', 1)[0]
        self.assertIn('V293_rdy_raw_cells', pre)
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertEqual(len(protocol['controls']), 4)
        self.assertEqual(len(protocol['limits']), 3)

    def test_joint_encoded_entry_and_both_interrupt_modes(self):
        text = (R / PROBE).read_text()
        for token in ('WCspatial', 'WCentry', 'WCrules', 'WCsemantics', 'WCcurrent_spatial',
                      'WCcurrent_member', 'OwnershipCellsSpatial', 'enabled', 'WCclock'):
            self.assertIn(token, text)
        entry = text.split('Theorem WCentry', 1)[1].split('Qed.', 1)[0]
        self.assertNotIn('RCentry', entry)
        self.assertIn('WCspatial', entry)
        self.assertNotIn('Stage165Debug', text)

    def test_independent_real_output_and_neutralization(self):
        text = (R / PROBE).read_text()
        for token in ('WCliteral_execution', 'V293_tick_while_owned_execution', 'WCobservations',
                      'WCexecution_control', 'WCreject_neutralized', 'WCneutralized',
                      'spec_stepstar', 'V293_tick_chain_records_lossless', 'V293_byteval 20'):
            self.assertIn(token, text)
        control = text.split('Theorem WCexecution_control', 1)[1]
        self.assertIn('WCliteral_execution', control)
        self.assertNotIn('RuleSound', control)

    def test_current_compilation_and_trust(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, p in (('while', PROD), ('probe', PROBE)):
            row = json.loads((D / (stable[kind] + '.json')).read_text())
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256((R / p).read_bytes()).hexdigest())
        trust = json.loads((D / 'trust.json').read_text())
        self.assertTrue(trust['passed'])
        self.assertEqual((trust['checked_active_modules'], trust['checked_extra_modules']), (335, 55))
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))


if __name__ == '__main__':
    unittest.main()
