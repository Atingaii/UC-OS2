"""共享core取节点结构回归；不替代独立Coq内核检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage164-tick-core-focus'
PROD = 'certiucos/v293/proofs/V293TimeTickCoreFocus.v'
PROBE = 'audit/probes/V293TimeTickCoreFocusProbe.v'


class TickCoreFocusTests(unittest.TestCase):
    def test_old_sources_and_evidence_unchanged(self):
        base = json.loads((D / 'baseline.json').read_text())['files']
        for p in ('certiucos/v293/proofs/V293TimeTickReadyUpdate.v',
                  'certiucos/v293/proofs/V293TimeReadyShared.v',
                  'certiucos/v293/proofs/V293TimeTickRecordReassembly.v',
                  'certiucos/v293/code/V293OSTimeTick.v',
                  'audit/logs/stage163-tick-ready-update/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), base[p])
        self.assertEqual(json.loads((D / 'source-identity.json').read_text()),
                         json.loads((D.parent / 'stage163-tick-ready-update/source-identity.json').read_text()))

    def test_canonical_not_focused_pre(self):
        text = (R / PROD).read_text()
        pre = text.split('Definition V293_tick_wait_core_pre ', 1)[1].split('Lemma ', 1)[0]
        pre = re.sub(r'\(\*.*?\*\)', '', pre, flags=re.S)
        self.assertIn('V293_ready_payload br bg bp tasks', pre)
        self.assertIn('V293_shared_fields ct tasks es n', pre)
        self.assertNotIn('del tasks', pre)
        self.assertNotIn('V293_tick_ready_wait_pre', pre)
        for token in ('V293_tick_wait_core_unfold', 'V293_tick_wait_core_fold',
                      'V293_owned_task_records_focus', 'V293_tick_wait_record_open'):
            self.assertIn(token, text)
        self.assertNotIn('Atrue', text)

    def test_actual_rule_and_minimal_resources(self):
        text = (R / PROD).read_text()
        contract = text.split('Theorem V293_tick_core_wait_iteration :', 1)[1].split('Proof.', 1)[0]
        premises, conclusion = contract.split('  InfRules ', 1)
        for token in ('InfRules', 'RuleSem', 'V293_local_steps', 'evalval', 'evaltype'):
            self.assertNotIn(token, premises)
        self.assertIn('reason=os_stat_time -> timepend<256', premises)
        self.assertIn('EX tasks:TcbMod.map, EX es:EcbMod.map, EX n:int32', conclusion)
        self.assertIn('get tasks (b,Int.repr base)=Some', conclusion)
        self.assertIn('V293_tick_iteration ptcb rows group', conclusion)
        self.assertIn('OS[ir,false,si,ci]', conclusion)
        self.assertIn('apply V293_tick_ready_wait_iteration_hoare', text)
        self.assertIn('apply RuleSound', text)
        for p in (PROD, PROBE):
            src = (R / p).read_text()
            self.assertNotRegex(src, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
        self.assertNotIn('CertiOS.audit.', text)

    def test_joint_nonempty_canonical_entry(self):
        text = (R / PROBE).read_text()
        for token in ('CFcanonical_spatial', 'CFentry', 'CFrules', 'CFcore',
                      'V293_owned_task_records_reassemble', 'RUspatial', 'RUabstract'):
            self.assertIn(token, text)
        entry = text.split('Theorem CFentry', 1)[1].split('Qed.', 1)[0]
        self.assertNotIn('RUentry', entry)
        self.assertIn('CFcanonical_spatial', entry)
        self.assertIn('CFwrong_lookup', text)

    def test_real_pend_and_explicit_time_supplement(self):
        text = (R / PROD).read_text()
        self.assertIn('reason=os_stat_time -> pend=timepend', text)
        text = (R / PROBE).read_text()
        for token in ('CF_event_pend', 'CF_time_pend', 'CF_event_selected',
                      'CF_time_selected', 'CFpend_load', 'pend=7'):
            self.assertIn(token, text)

    def test_actual_output_control(self):
        text = (R / PROBE).read_text()
        for token in ('CFexecution_control', 'RUexpiry_control', 'RUbranch_cases',
                      'RUexecution', 'RUreject_neutralized', 'V293_byteval 80'):
            self.assertIn(token, text)
        protocol = json.loads((D / 'protocol.json').read_text())
        self.assertEqual(len(protocol['controls']), 4)
        self.assertEqual(len(protocol['limits']), 3)

    def test_current_compilation_and_trust(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, p in (('focus', PROD), ('probe', PROBE)):
            row = json.loads((D / (stable[kind] + '.json')).read_text())
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256((R / p).read_bytes()).hexdigest())
        trust = json.loads((D / 'trust.json').read_text())
        self.assertTrue(trust['passed'])
        self.assertEqual((trust['checked_active_modules'], trust['checked_extra_modules']), (334, 54))
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))


if __name__ == '__main__':
    unittest.main()
