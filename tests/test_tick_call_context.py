"""真实调用分配与共享后缀入口的结构回归；Coq 检查另行记录。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage170-tick-call-context'
PROD='certiucos/v293/proofs/V293TimeTickCallContext.v'
PROBE='audit/probes/V293TimeTickCallContextProbe.v'
class TickCallContextTests(unittest.TestCase):
    def test_frozen_source_and_predecessors(self):
        base=json.loads((D/'baseline.json').read_text())['files']
        for p in ('certiucos/v293/code/V293OSTimeTick.v',
                  'certiucos/v293/proofs/V293TimeTickLifecycle.v',
                  'certiucos/v293/proofs/V293TimeTickScanSlot.v',
                  'audit/logs/stage169-tick-scan-slot/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R/p).read_bytes()).hexdigest(),base[p])
    def test_real_call_and_shared_suffix_not_hook_skip(self):
        src=(R/PROD).read_text()
        contract=src.split('Theorem V293_tick_call_shared_to_hook :',1)[1].split('Proof.',1)[0]
        self.assertIn('fresh M bc',contract)
        self.assertIn('fresh(allocb M bc',contract)
        self.assertIn('V293_tick_locals ptcb saved bc bs,M',contract)
        self.assertIn('curs(scall tickfn nil)',contract)
        self.assertIn('curs(scall hook nil)',contract)
        self.assertIn('exists Ms,',contract)
        self.assertIn('V293_tick_call_suffix clock',contract)
        self.assertIn('V293_tick_call_to_hook',src)
        self.assertIn('apply V293_tick_scan_switch_hoare',src)
        self.assertNotIn('CertiOS.audit.',src)
        for p in (PROD,PROBE):
            self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
    def test_callee_bindings_are_independent(self):
        src=(R/PROBE).read_text()
        self.assertIn('V293_tick_locals 901%Z 904%Z 171%positive 172%positive',src)
        entry=src.split('Lemma CCentry :',1)[1].split('Qed.',1)[0]
        self.assertIn('CCbare_good_fun clock run',entry)
        self.assertIn('CCbindings_spatial',entry)
        self.assertNotIn('V293_tick_call_shared_to_hook',entry)
        self.assertNotIn('V293_tick_scan_switch_hoare',entry)
        for name in ('CCfresh','CCfresh_saved','CCwrong_env','CCcaller_cells'):
            self.assertRegex(src,r'(?:Lemma|Theorem) '+name+r'\s*:')
        self.assertIn('else None',src.split('Definition CCprogram',1)[1].split('Definition CCexecution',1)[0])
    def test_same_allocated_endpoint_controls(self):
        src=(R/PROBE).read_text()
        endpoint=src.split('Theorem CCsame_endpoint_controls :',1)[1].split('Proof.',1)[0]
        for token in ('CCexecution ks clock run Ms','CCsuffix clock run',
                      'Ms(171%positive,0%Z)=Some Vundef',
                      'Ms(172%positive,0%Z)=Some(Vint32 Int.zero)',
                      'Ms(90%positive,0%Z)=Some(Vint32(Int.repr 99))',
                      'Ms(70%positive,0%Z)=Some(Vptr WhileIdle)',
                      'CCbad_saved clock run'):
            self.assertIn(token,endpoint)
        wrong=src.split('Definition CCbad_saved',1)[1].split('Lemma CCwrong_saved',1)[0]
        self.assertIn('Vint32 Int.one',wrong)
        self.assertIn('clock Vundef',wrong)
        self.assertIn('apply RuleSound;apply CCrules',src)
        for name in ('CCrunning','CCstopped','CCwrap'):
            self.assertIn('Theorem '+name+' :',src)
        self.assertEqual(len(json.loads((D/'protocol.json').read_text())['controls']),4)
    def test_stable_compile_and_independent_trust(self):
        stable=json.loads((D/'stable-compiles.json').read_text())
        for key,p in (('context',PROD),('probe',PROBE)):
            row=json.loads((D/(stable[key]+'.json')).read_text())
            self.assertEqual(row['exit'],0)
            self.assertEqual(row['initial_source_sha256'],row['source_sha256'])
            self.assertEqual(row['source_sha256'],hashlib.sha256((R/p).read_bytes()).hexdigest())
        trust=json.loads((D/'trust.json').read_text())
        self.assertTrue(trust['passed'])
        self.assertEqual(trust['roots_printed'],23)
        self.assertEqual((trust['checked_active_modules'],trust['checked_extra_modules']),(340,60))
        old=json.loads((D.parent/'stage169-tick-scan-slot/trust.json').read_text())
        self.assertEqual(set(trust['allowed']),set(old['allowed']))
        self.assertLessEqual(set(trust['assumptions']),set(trust['allowed']))
