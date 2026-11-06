"""canonical 后 hook 连接；语义由 Coq 复核，不以文本检查代替证明。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage167-tick-post-hook-core'
PROD='certiucos/v293/proofs/V293TimeTickPostHookCore.v'
PROBE='audit/probes/V293TimeTickPostHookCoreProbe.v'
class TickPostHookCoreTests(unittest.TestCase):
    def test_frozen_predecessors(self):
        base=json.loads((D/'baseline.json').read_text())['files']
        for p in ('certiucos/v293/proofs/V293TimeTickChainOpen.v','certiucos/v293/proofs/V293TimeTickPostHookHoare.v','certiucos/v293/code/V293OSTimeTick.v','audit/logs/stage166-tick-chain-open/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R/p).read_bytes()).hexdigest(),base[p])
    def test_source_link_and_no_oracle(self):
        src=(R/PROD).read_text()
        contract=src.split('Theorem V293_tick_post_hook_core_hoare :',1)[1].split('Proof.',1)[0]
        pre,post=contract.split('  InfRules ',1)
        for token in ('evalval','evaltype','V293_local_steps','RuleSem','InfRules'):
            self.assertNotIn(token,pre)
        for token in ('V293_tick_post_hook ptcb rows group now running head','V293_tick_post_hook_core_result'):
            self.assertIn(token,post)
        for token in ('V293_tick_chain_core_hoare','V293_tick_clock_absinfer','V293_tick_head_assign_hoare','V293_tick_running_guard_owned','apply RuleSound'):
            self.assertIn(token,src)
        self.assertNotIn('CertiOS.audit.',src)
    def test_canonical_entry(self):
        src=(R/PROD).read_text()
        entry=src.split('Definition V293_tick_post_hook_core_state ',1)[1].split('Lemma ',1)[0]
        for token in ('V293_ready_payload','V293_shared_fields','V293_tick_chain_missing','scan'):
            self.assertIn(token,entry)
        for token in ('V293_tick_chain_cells','V293_tick_binding_extra','V293_rdy_raw_cells'):
            self.assertNotIn(token,entry)
        for p in (PROD,PROBE):
            self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
    def test_nonvacuous_controls(self):
        src=(R/PROBE).read_text()
        for token in ('PCentry','PCrunning','PCstopped','PCclock_neutralized','PCscan_not_head','255','Int.max_unsigned','PCexecution_control'):
            self.assertIn(token,src)
        entry=src.split('Theorem PCentry',1)[1].split('Qed.',1)[0]
        for token in ('PCrunning','PCstopped','V293_tick_post_hook_core_hoare','COentry'):
            self.assertNotIn(token,entry)
        p=json.loads((D/'protocol.json').read_text())
        self.assertEqual(len(p['controls']),4)
    def test_current_compile_and_trust(self):
        stable=json.loads((D/'stable-compiles.json').read_text())
        for k,p in (('core',PROD),('probe',PROBE)):
            row=json.loads((D/(stable[k]+'.json')).read_text())
            self.assertEqual(row['exit'],0)
            self.assertEqual(row['initial_source_sha256'],row['source_sha256'])
            self.assertEqual(row['source_sha256'],hashlib.sha256((R/p).read_bytes()).hexdigest())
        trust=json.loads((D/'trust.json').read_text())
        self.assertTrue(trust['passed'])
        self.assertLessEqual(set(trust['assumptions']),set(trust['allowed']))
