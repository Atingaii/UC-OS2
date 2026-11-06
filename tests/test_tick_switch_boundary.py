"""既有 SWINV 取还连接；文本门不替代 Coq 与独立字节堆检验。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage168-tick-switch-boundary'
PROD='certiucos/v293/proofs/V293TimeTickSwitchBoundary.v'
PROBE='audit/probes/V293TimeTickSwitchBoundaryProbe.v'
class TickSwitchBoundaryTests(unittest.TestCase):
    def test_frozen_predecessors(self):
        base=json.loads((D/'baseline.json').read_text())['files']
        for p in ('certiucos/v293/proofs/V293TimeTickPostHookCore.v','certiucos/v293/proofs/V293TimeReadyShared.v','certiucos/v293/code/V293OSTimeTick.v','audit/logs/stage167-tick-post-hook-core/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R/p).read_bytes()).hexdigest(),base[p])
    def test_existing_inv_and_no_execution_oracle(self):
        src=(R/PROD).read_text()
        contract=src.split('Theorem V293_tick_post_hook_switch_hoare :',1)[1].split('Proof.',1)[0]
        pre,post=contract.split('  InfRules ',1)
        for token in ('evalval','evaltype','V293_local_steps','RuleSem','InfRules'):
            self.assertNotIn(token,pre)
        for token in ('V293_time_ready_inv','V293_tick_post_hook ptcb rows group now running head','V293_tick_switch_result'):
            self.assertIn(token,post)
        for token in ('V293_time_ready_switch_open','V293_time_ready_switch_close','V293_tick_post_hook_core_hoare','apply RuleSound'):
            self.assertIn(token,src)
        self.assertNotIn('CertiOS.audit.',src)
        self.assertNotRegex(src,r'Definition \w+\s*: Inv')
    def test_same_map_view_and_exact_resources(self):
        src=(R/PROD).read_text()
        view=src.split('Definition V293_tick_switch_view ',1)[1].split('Lemma ',1)[0]
        self.assertIn('SWINV(V293_time_ready_inv',view)
        self.assertIn('//\\\\',view)
        entry=src.split('Definition V293_tick_switch_pre ',1)[1].split('Definition ',1)[0]
        self.assertIn('V293_tick_switch_view',entry)
        for token in ('V293_time_ready_core','V293_tick_chain_cells','V293_ready_payload'):
            self.assertNotIn(token,entry)
        result=src.split('Definition V293_tick_switch_result ',1)[1].split('Lemma ',1)[0]
        for token in ('V293_tick_chain_residual actual','V293_tick_pend_choices','coreframe','V293_tick_switch_supplement scan','SWINV'):
            self.assertIn(token,result)
        for p in (PROD,PROBE):
            self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
    def test_independent_entry_and_single_factor_controls(self):
        src=(R/PROBE).read_text()
        pack=src.split('Lemma SCpack',1)[1].split('Qed.',1)[0]
        for token in ('V293_tick_switch_open','V293_tick_switch_entry','V293_tick_post_hook_switch_hoare','PCentry'):
            self.assertNotIn(token,pack)
        for token in ('PCjoint','PCpack','SCentry','SCrunning','SCstopped','SCwrong_clock','SCwrong_tasks','PCclock_neutralized','PCexecution_control','Int.max_unsigned','255'):
            self.assertIn(token,src)
        p=json.loads((D/'protocol.json').read_text())
        self.assertEqual(len(p['controls']),4)
        self.assertEqual(len(p['limits']),3)
    def test_current_compile_and_trust(self):
        stable=json.loads((D/'stable-compiles.json').read_text())
        for k,p in (('boundary',PROD),('probe',PROBE)):
            row=json.loads((D/(stable[k]+'.json')).read_text())
            self.assertEqual(row['exit'],0)
            self.assertEqual(row['initial_source_sha256'],row['source_sha256'])
            self.assertEqual(row['source_sha256'],hashlib.sha256((R/p).read_bytes()).hexdigest())
        trust=json.loads((D/'trust.json').read_text())
        self.assertTrue(trust['passed'])
        self.assertLessEqual(set(trust['assumptions']),set(trust['allowed']))
