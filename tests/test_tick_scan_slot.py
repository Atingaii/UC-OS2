"""真实未初始化扫描槽的结构回归；不以文本检查替代 Coq。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage169-tick-scan-slot'
PROD='certiucos/v293/proofs/V293TimeTickScanSlot.v'
PROBE='audit/probes/V293TimeTickScanSlotProbe.v'
class TickScanSlotTests(unittest.TestCase):
    def test_frozen_predecessors(self):
        base=json.loads((D/'baseline.json').read_text())['files']
        for p in ('certiucos/v293/proofs/V293TimeTickSwitchBoundary.v','certiucos/v293/proofs/V293TimeTickPostHookCore.v','certiucos/v293/code/V293OSTimeTick.v','audit/logs/stage168-tick-switch-boundary/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R/p).read_bytes()).hexdigest(),base[p])
    def test_raw_slot_not_a_typed_undef(self):
        src=(R/PROD).read_text()
        state=src.split('Definition V293_tick_scan_state ',1)[1].split('Definition ',1)[0]
        self.assertIn('Amapsto(bc,0%Z)(Tptr V293_tcb_type)true scan',state)
        store=src.split('Lemma V293_tick_scan_head_store :',1)[1].split('Qed.',1)[0]
        self.assertIn('initial)::rest',store)
        self.assertIn('V293_raw_assign_hoare',store)
        self.assertNotIn('rule_type_val_match (Tptr V293_tcb_type) initial',store)
        self.assertNotIn('V293_tick_raw_pointer_load',store)
    def test_original_program_and_existing_inv(self):
        src=(R/PROD).read_text()
        contract=src.split('Theorem V293_tick_scan_switch_hoare :',1)[1].split('Proof.',1)[0]
        pre,post=contract.split('  InfRules ',1)
        for token in ('evalval','evaltype','V293_local_steps','RuleSem','InfRules'):
            self.assertNotIn(token,pre)
        for token in ('V293_time_ready_inv','V293_tick_post_hook ptcb rows group now running head','V293_tick_scan_switch_result'):
            self.assertIn(token,post)
        self.assertIn('V293_tick_switch_open',src)
        self.assertIn('V293_tick_switch_close',src)
        self.assertIn('apply RuleSound',src)
        self.assertNotIn('CertiOS.audit.',src)
        for p in (PROD,PROBE):
            self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
    def test_fresh_entry_controls(self):
        src=(R/PROBE).read_text()
        for name in ('SSentry','SSwrong_pointer','SSundef_not_typed','SSrunning','SSstopped','SSexecution','SSwrap','SSclock_neutralized'):
            self.assertIn(name,src)
        pack=src.split('Lemma SSpack',1)[1].split('Qed.',1)[0]
        self.assertNotIn('V293_tick_scan_switch_hoare',pack)
        self.assertNotIn('V293_tick_scan_switch_entry',pack)
        self.assertIn('Vundef',src)
        self.assertEqual(len(json.loads((D/'protocol.json').read_text())['controls']),4)
    def test_compile_and_trust(self):
        stable=json.loads((D/'stable-compiles.json').read_text())
        for key,p in (('slot',PROD),('probe',PROBE)):
            row=json.loads((D/(stable[key]+'.json')).read_text())
            self.assertEqual(row['exit'],0)
            self.assertEqual(row['initial_source_sha256'],row['source_sha256'])
            self.assertEqual(row['source_sha256'],hashlib.sha256((R/p).read_bytes()).hexdigest())
        trust=json.loads((D/'trust.json').read_text())
        self.assertTrue(trust['passed'])
        old=json.loads((D.parent/'stage168-tick-switch-boundary/trust.json').read_text())
        self.assertEqual(set(trust['allowed']),set(old['allowed']))
        self.assertLessEqual(set(trust['assumptions']),set(trust['allowed']))
