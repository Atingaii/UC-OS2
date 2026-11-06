"""整链canonical入口回归；语义结果以独立Coq检查为准。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage166-tick-chain-open'
PROD = 'certiucos/v293/proofs/V293TimeTickChainOpen.v'
PROBE = 'audit/probes/V293TimeTickChainOpenProbe.v'


class TickChainOpenTests(unittest.TestCase):
    def test_frozen_predecessor(self):
        base = json.loads((D / 'baseline.json').read_text())['files']
        for p in ('certiucos/v293/proofs/V293TimeTickWhileCore.v',
                  'certiucos/v293/proofs/V293TimeTickCoreFocus.v',
                  'certiucos/v293/code/V293OSTimeTick.v',
                  'audit/logs/stage165-tick-while-core/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), base[p])
        self.assertEqual(json.loads((D / 'source-identity.json').read_text()),
                         json.loads((D.parent / 'stage165-tick-while-core/source-identity.json').read_text()))

    def test_canonical_not_all_raw_entry(self):
        src = (R / PROD).read_text()
        pre = src.split('Definition V293_tick_chain_core_pre :=', 1)[1].split('Lemma ', 1)[0]
        self.assertIn('V293_ready_payload br bg bp tasks', pre)
        self.assertIn('V293_shared_fields ct tasks es n', pre)
        self.assertIn('V293_tick_chain_missing bindings idle', pre)
        for token in ('V293_tick_task_cells', 'V293_tick_chain_cells', 'V293_tick_binding_extra',
                      'V293_rdy_raw_cells', 'V293_tick_idle_extra'):
            self.assertNotIn(token, pre)
        self.assertIn('V293_tick_canonical_chain_open', src)
        self.assertIn('V293_tick_owned_to_raw', src)

    def test_hidden_event_pend_not_hint(self):
        src = (R / PROD).read_text()
        missing = src.split('Definition V293_tick_node_missing ', 1)[1].split('Fixpoint ', 1)[0]
        self.assertIn('| wait _ _ => []', missing)
        self.assertIn('| wait os_stat_time _ =>', missing)
        self.assertIn('V293_tick_pend_choices_properties', src)
        probe = (R / PROBE).read_text()
        for token in ('COhint_same', 'COevent_selected', 'V293_byteval_injective_bounded',
                      'COtime_ready_supplements', '99', 'pend=7'):
            self.assertIn(token, probe)

    def test_formal_original_while_oracle_free(self):
        src = (R / PROD).read_text()
        contract = src.split('Theorem V293_tick_chain_core_hoare :', 1)[1].split('Proof.', 1)[0]
        premises, conclusion = contract.split('  InfRules ', 1)
        for token in ('InfRules', 'RuleSem', 'V293_local_steps', 'evalval', 'evaltype'):
            self.assertNotIn(token, premises)
        self.assertIn('swhile(V293_tick_guard ptcb)(V293_tick_iteration ptcb rows group)', conclusion)
        self.assertIn('V293_tick_while_core_post actual idle br bg bp bn bc frame', conclusion)
        self.assertNotIn('Atrue', conclusion)
        self.assertIn('apply V293_tick_while_core_hoare', src)
        self.assertIn('apply RuleSound', src)
        self.assertNotIn('CertiOS.audit.', src)
        for p in (PROD, PROBE):
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')

    def test_independent_joint_entry_and_both_modes(self):
        src = (R / PROBE).read_text()
        entry = src.split('Theorem COentry', 1)[1].split('Qed.', 1)[0]
        self.assertIn('WCspatial', entry)
        self.assertIn('WCabstract', entry)
        for token in ('WCentry', 'V293_tick_chain_core_open', 'COopened', 'COhoare'):
            self.assertNotIn(token, entry)
        for token in ('COhoare', 'COsemantics', 'COopened', 'COhint_entry', 'WCcurrent_member'):
            self.assertIn(token, src)

    def test_controls_and_bounded_scope(self):
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertEqual(len(protocol['controls']), 4)
        self.assertEqual(len(protocol['limits']), 3)
        probe = (R / PROBE).read_text()
        control = probe.split('Theorem COexecution_control', 1)[1]
        self.assertIn('WCexecution_control', control)
        self.assertIn('COentry', control)
        self.assertNotIn('RuleSound', control)
        self.assertIn('复用165', protocol['controls'][3])

    def test_current_compilation_and_trust(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, p in (('open', PROD), ('probe', PROBE)):
            row = json.loads((D / (stable[kind] + '.json')).read_text())
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256((R / p).read_bytes()).hexdigest())
        trust = json.loads((D / 'trust.json').read_text())
        self.assertTrue(trust['passed'])
        self.assertEqual((trust['checked_active_modules'], trust['checked_extra_modules']), (336, 56))
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))


if __name__ == '__main__':
    unittest.main()
