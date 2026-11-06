"""hook 契约连接的结构回归；语义和负控由独立 Coq 检查支持。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage171-tick-hook-contract'
PROD='certiucos/v293/proofs/V293TimeTickHookContract.v'
PROBE='audit/probes/V293TimeTickHookContractProbe.v'
class TickHookContractTests(unittest.TestCase):
    def test_fixed_target_and_predecessors(self):
        base=json.loads((D/'baseline.json').read_text())['files']
        for p in ('certiucos/v293/code/V293OSTimeTick.v',
                  'certiucos/v293/proofs/V293TimeTickCallContext.v',
                  'audit/probes/V293TimeTickCallContextProbe.v',
                  'audit/logs/stage170-tick-call-context/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R/p).read_bytes()).hexdigest(),base[p])
    def test_real_call_composed_not_skip(self):
        src=(R/PROD).read_text()
        self.assertIn('eapply call_rule',src)
        self.assertIn('(sseq(scall hook[])',src)
        self.assertIn('apply V293_tick_call_suffix_hoare',src)
        self.assertIn('Spec hook=Some(V293_tick_hook_fpre',src)
        self.assertIn('result=None',src)
        self.assertNotIn('CertiOS.audit.',src)
        for p in (PROD,PROBE):
            self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
    def test_same_actual_endpoint_and_frame(self):
        src=(R/PROBE).read_text()
        control=src.split('Theorem HCsame_endpoint :',1)[1].split('Proof.',1)[0]
        for token in ('CCexecution ks clock run Ms','HCresource clock run ** CCbindings',
                      'Ms(171%positive,0%Z)=Some Vundef',
                      'Ms(172%positive,0%Z)=Some(Vint32 Int.zero)',
                      'Ms(90%positive,0%Z)=Some(Vint32(Int.repr 99))',
                      'Ms(70%positive,0%Z)=Some(Vptr WhileIdle)','CCbad_saved clock run'):
            self.assertIn(token,control)
        self.assertIn('~GoodFunAsrt CCbindings',src)
        self.assertIn('apply RuleSound;apply HCrules',src)
    def test_guard_controls_and_missing_body(self):
        src=(R/PROBE).read_text()
        guard=src.split('Theorem HCsame_guard_controls :',1)[1].split('Proof.',1)[0]
        for token in ('[][]WhileReady','[Vint32 Int.zero][]WhileReady',
                      '[]None[]WhileReady','[](Some(Vint32 Int.zero))[]WhileReady'):
            self.assertIn(token,guard)
        for name in ('HCnil_required','HCvoid_required','HCmissing_no_step','HCmissing_no_return'):
            self.assertRegex(src,r'(?:Lemma|Theorem) '+name+r'\s*:')
        self.assertIn('sfexec 2002%Z[][]',src)
        self.assertIn('apply V293_missing_port_has_no_step',src)
        self.assertEqual(len(json.loads((D/'protocol.json').read_text())['controls']),4)
    def test_stable_compiles_and_recursive_trust(self):
        stable=json.loads((D/'stable-compiles.json').read_text())
        for key,p in (('contract',PROD),('probe',PROBE)):
            row=json.loads((D/(stable[key]+'.json')).read_text())
            self.assertEqual(row['exit'],0)
            self.assertEqual(row['initial_source_sha256'],row['source_sha256'])
            self.assertEqual(row['source_sha256'],hashlib.sha256((R/p).read_bytes()).hexdigest())
        trust=json.loads((D/'trust.json').read_text())
        self.assertTrue(trust['passed'])
        self.assertTrue(trust['recursive'])
        self.assertEqual(len(trust['entry_modules']),2)
        self.assertEqual(len(trust['roots']),trust['roots_printed'])
        self.assertEqual([x['exit'] for x in trust['commands']],[0,0])
        old=json.loads((D.parent/'stage170-tick-call-context/trust.json').read_text())
        self.assertEqual(set(trust['allowed']),set(old['allowed']))
        self.assertLessEqual(set(trust['assumptions']),set(trust['allowed']))
