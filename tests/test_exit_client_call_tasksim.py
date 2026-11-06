"""固定客户端调用组合的接口与证据；证明有效性由 Coq kernel 检查。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage289-exit-client-call'
P='certiucos/v293/proofs/V293ExitClientCallTaskSim.v'
Q='audit/probes/V293ExitClientCallTaskSimProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda n:json.loads((D/n).read_text())
class ExitClientCallTests(unittest.TestCase):
 def test_identity_and_fixed_program(self):
  self.assertEqual(sha(R/P),'f326df3a880eb602105996ad3274cfd38753f99dde37c7e9356bbbfc181a4c6c')
  self.assertEqual(sha(R/Q),'f6ccee8d3ff51f2954e91200a8a0495e7f9ceeaa793bedafbc4cd3a36edf3b3c')
  self.assertEqual((R/'_CoqProject').read_text().splitlines().count(P),1)
  self.assertNotIn(Q,(R/'_CoqProject').read_text())
  self.assertEqual(len(read('baseline.json')['files']),1675)
  self.assertEqual((D/'protocol.sha256').read_text().split(),[sha(D/'protocol.json'),'protocol.json'])
  for p,h in read('source-identity.json')['files'].items():self.assertEqual(sha(R/p),h,p)
 def test_public_matching_calls_no_simulation_premise(self):
  s=(R/P).read_text();public=s.split('Theorem V293_exit_client_call_TaskSim :',1)[1].split('Proof.',1)[0]
  self.assertEqual(len(re.findall(r'^Theorem ',s,re.M)),1)
  self.assertEqual(public.count('TaskSim('),1)
  self.assertEqual(public.count('(curs(scall f nil),(kenil,tail))'),2)
  for term in ['fst(fst A)f=Some','n<=1','~V293_highest_ready tasks t','V293_exit_active_resource br bg','RDYINV G t']:
   self.assertIn(term,public)
  self.assertNotRegex(public,r'\b(?:cstep|cstepstar|store|load|evalval|evaladdr|evaltype|fresh|InOS)\b')
  self.assertNotIn('Amapsto',public)
  for p in [P,Q]:self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
 def test_constructed_client_and_api_steps(self):
  s=(R/P).read_text()
  for term in ['V293_client_nil_call_low','V293_client_nil_call_high','V293_client_nil_call_abort','V293_client_nil_call_outside','apply task_sim','eapply ht_starS','apply V293_client_nil_api_enter','V293_exit_active_call_TaskSim','V293_exit_active_current']:
   self.assertIn(term,s)
  publicproof=s.split('Theorem V293_exit_client_call_TaskSim :',1)[1].split('Proof.',1)[1]
  self.assertIn('eapply V293_client_nil_call_bridge',publicproof)
  self.assertIn('eapply V293_exit_active_call_TaskSim',publicproof)
 def test_nonempty_instance_and_bounded_control(self):
  q=(R/Q).read_text();public=q.split('Theorem CCnonempty_client_call :',1)[1].split('Proof.',1)[0]
  self.assertNotIn('getsched',public);self.assertNotIn('fun _=>True',public)
  for term in ['ACmemory n','ACbase','CCspec','CCbinding_single_factor','CCabstract_entry','CCmissing_binding_no_high_step','CCactual_client_low_step','CCclient_step_unchanged']:
   self.assertIn(term,q)
  doc=(R/'audit/STAGE289_EXIT_CLIENT_CALL.md').read_text()
  for term in ['不是完整调用执行消融','强 current guard 缺口','uCOS3 未开始','不是 Post=True','没有改写第288步']:
   self.assertIn(term,doc)
  old=json.loads((R/'audit/logs/stage288-exit-active-call/verification.json').read_text())
  self.assertFalse(old['client_scall_TaskSim']);self.assertFalse(old['protocol_fully_completed'])
 def test_stable_compiles_and_recursive_trust(self):
  roots=[]
  for p,row in read('stable-compiles.json').items():
   self.assertEqual(sha(R/p),row['sha256']);self.assertEqual(len(row['runs']),2)
   roots += [Path(p).stem+'.'+n for n in row['roots']]
   for run in row['runs']:
    self.assertEqual(run['exit'],0);self.assertEqual(run['initial_source_sha256'],sha(R/p));self.assertEqual(run['source_sha256'],sha(R/p))
  t=read('trust.json');self.assertTrue(t['passed']);self.assertTrue(t['recursive'])
  self.assertEqual(t['roots'],roots);self.assertEqual(t['roots_printed'],len(roots));self.assertEqual(list(read('assumptions-by-root.json')),roots)
  for row in t['commands']:self.assertEqual(row['exit'],0)
  self.assertLessEqual(set(t['assumptions']),{'Classical_Prop.classic','FunctionalExtensionality.functional_extensionality_dep'})
if __name__=='__main__':unittest.main()
