"""完整tick body的结构回归；语义依据是Coq编译与递归信任检查。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage173-tick-body-hoare'
PROD='certiucos/v293/proofs/V293TimeTickBodyHoare.v'
PROBE='audit/probes/V293TimeTickBodyHoareProbe.v'
class TickBodyHoareTests(unittest.TestCase):
    def test_fixed_target_and_predecessors(self):
        base=json.loads((D/'baseline.json').read_text())['files']
        for p in ('certiucos/v293/code/V293OSTimeTick.v',
                  'certiucos/v293/proofs/V293TimeTickHookContract.v',
                  'certiucos/v293/proofs/V293TimeTickReturnTail.v',
                  'audit/logs/stage172-tick-return-tail/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R/p).read_bytes()).hexdigest(),base[p])
    def test_exact_body_initialization_hook_and_return(self):
        src=(R/PROD).read_text()
        for token in ('Theorem V293_tick_body_hoare :','apply V293_time_zero.',
                      '(sseq(V293_tick_body ptcb rows group saved now running head hook)sret)',
                      'apply V293_tick_hook_then_suffix with(good:=good)',
                      'apply ret_rule','[|result=None|]',
                      'Spec hook=Some','(B ==> Aemp)',
                      'eapply V293_tick_return_tail'):
            self.assertIn(token,src)
        self.assertNotIn('CertiOS.audit.',src)
        for p in (PROD,PROBE):
            self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
    def test_same_initialization_endpoints_and_composition(self):
        src=(R/PROBE).read_text()
        control=src.split('Theorem BHsame_initialization_controls :',1)[1].split('Proof.',1)[0]
        for token in ('BHprefix ks clock run(BHmemory clock run)',
                      'CCexecution ks clock run Ms',
                      'BHentry Vundef clock run',
                      'BHentry(Vint32 Int.zero)clock run',
                      'Ms(90%positive,0%Z)=Some(Vint32(Int.repr 99))',
                      'Ms(70%positive,0%Z)=Some(Vptr WhileIdle)'):
            self.assertIn(token,control)
        for token in ('V293_tick_allocate_frame','V293_tick_raw_slot_update',
                      'V293_success_assign_zero','exact(BHallocated_prefix ks clock run)|exact Exec'):
            self.assertIn(token,src)
    def test_return_nonvacuity_and_missing_hook(self):
        src=(R/PROBE).read_text()
        for name in ('BHsemantics','BHwrong_return','BHstopped_return_fixture',
                     'BHreturn_releases_locals','BHmissing_hook_still_blocked'):
            self.assertRegex(src,r'Theorem '+name+r'\s*:')
        for token in ('run<256 ->run<>1 ->exists Ms','BHreturn run None',
                      'BHreturn run(Some(Vint32 Int.zero))',
                      'V293_tick_body_return_to_caller','apply HCmissing_no_step'):
            self.assertIn(token,src)
        self.assertEqual(len(json.loads((D/'protocol.json').read_text())['controls']),4)
    def test_stable_compiles_and_recursive_trust(self):
        stable=json.loads((D/'stable-compiles.json').read_text())
        for key,p in (('body',PROD),('probe',PROBE)):
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
        old=json.loads((D.parent/'stage172-tick-return-tail/trust.json').read_text())
        self.assertEqual(set(trust['allowed']),set(old['allowed']))
        self.assertLessEqual(set(trust['assumptions']),set(trust['allowed']))
