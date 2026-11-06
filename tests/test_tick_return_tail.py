"""真实返回尾部的结构回归；语义由 Coq 编译及递归信任检查支持。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage172-tick-return-tail'
PROD='certiucos/v293/proofs/V293TimeTickReturnTail.v'
PROBE='audit/probes/V293TimeTickReturnTailProbe.v'
class TickReturnTailTests(unittest.TestCase):
    def test_fixed_target_and_predecessors(self):
        base=json.loads((D/'baseline.json').read_text())['files']
        for p in ('certiucos/v293/code/V293OSTimeTick.v',
                  'certiucos/v293/proofs/V293TimeTickHookContract.v',
                  'audit/probes/V293TimeTickHookContractProbe.v',
                  'audit/logs/stage171-tick-hook-contract/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R/p).read_bytes()).hexdigest(),base[p])
    def test_real_return_and_both_free_orders(self):
        src=(R/PROD).read_text()
        for token in ('eapply free_locality2\'', 'Permutation_length_2_inv',
                      'sret_step','sfreeend_step','V293_tick_freels_execution',
                      'Theorem V293_tick_return_tail :','V293_tick_result_forget_bindings',
                      '(B ==> Aemp)','GoodFunAsrt R'):
            self.assertIn(token,src)
        self.assertNotIn('CertiOS.audit.',src)
        for p in (PROD,PROBE):
            self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
    def test_same_freed_endpoint_and_caller_cells(self):
        src=(R/PROBE).read_text()
        control=src.split('Theorem TRsame_allocated_return :',1)[1].split('Proof.',1)[0]
        for token in ('CCexecution ks clock run Ms','(PCge,caller,Mf)',
                      'get Mf(171%positive,Z.of_nat k)=None',
                      'get Mf(172%positive,Z.of_nat k)=None',
                      'Mf(90%positive,0%Z)=Some(Vint32(Int.repr 99))',
                      'Mf(70%positive,0%Z)=Some(Vptr WhileIdle)',
                      'Amapsto(171%positive,0%Z)','Amapsto(172%positive,0%Z)'):
            self.assertIn(token,control)
        self.assertIn('forall k,k<4 ->',control)
        self.assertIn('V293_tick_raw_owned_writable',src)
    def test_nonvacuous_stopped_result_not_hook_execution(self):
        src=(R/PROBE).read_text()
        for name in ('TRstopped_result_fixture','TRstopped_fixture_return','TRmissing_hook_still_blocked'):
            self.assertRegex(src,r'Theorem '+name+r'\s*:')
        self.assertIn('run<256 -> run<>1 ->',src)
        self.assertIn('eapply change_aop_rule',src)
        self.assertIn('exact Post',src)
        self.assertIn('apply HCmissing_no_step',src)
        self.assertEqual(len(json.loads((D/'protocol.json').read_text())['controls']),4)
    def test_stable_compiles_and_recursive_trust(self):
        stable=json.loads((D/'stable-compiles.json').read_text())
        for key,p in (('tail',PROD),('probe',PROBE)):
            row=json.loads((D/(stable[key]+'.json')).read_text())
            self.assertEqual(row['exit'],0)
            self.assertEqual(row['initial_source_sha256'],row['source_sha256'])
            self.assertEqual(row['source_sha256'],hashlib.sha256((R/p).read_bytes()).hexdigest())
        trust=json.loads((D/'trust.json').read_text())
        self.assertTrue(trust['passed'])
        self.assertTrue(trust['recursive'])
        self.assertEqual(len(trust['entry_modules']),2)
        self.assertEqual(len(trust['roots']),20)
        self.assertEqual(len(trust['roots']),trust['roots_printed'])
        self.assertEqual([x['exit'] for x in trust['commands']],[0,0])
        old=json.loads((D.parent/'stage171-tick-hook-contract/trust.json').read_text())
        self.assertEqual(set(trust['allowed']),set(old['allowed']))
        self.assertLessEqual(set(trust['assumptions']),set(trust['allowed']))
