"""锁定 API 入口接口和未完成的 scall 门槛；语义由 Coq kernel 验证。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage288-exit-active-call'
P='certiucos/v293/proofs/V293ExitActiveCallTaskSim.v'
Q='audit/probes/V293ExitActiveCallTaskSimProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda n:json.loads((D/n).read_text())
class ExitActiveCallTests(unittest.TestCase):
 def test_identity_and_fixed_program(self):
  self.assertEqual(sha(R/P),'f1c96f114e8476eec6b9cd81079a71b3b3e5602aceecfd2acf3c79a5f2fd750d')
  self.assertEqual(sha(R/Q),'cb831d374844a6da6b78cf15ceaf87bd689db194471b1f11c8faff1ae12804bc')
  self.assertEqual((R/'_CoqProject').read_text().splitlines().count(P),1)
  self.assertNotIn(Q,(R/'_CoqProject').read_text())
  self.assertEqual(len(read('baseline.json')['files']),1671)
  self.assertEqual((D/'protocol.sha256').read_text().split(),[sha(D/'protocol.json'),'protocol.json'])
  for p,h in read('source-identity.json')['files'].items():self.assertEqual(sha(R/p),h,p)
 def test_public_interface_not_execution_premise(self):
  s=(R/P).read_text();public=s.split('Theorem V293_exit_active_call_TaskSim :',1)[1].split('Proof.',1)[0]
  self.assertEqual(len(re.findall(r'^Theorem ',s,re.M)),1)
  self.assertEqual(public.count('TaskSim('),1)
  for term in ['(curs(sfexec f nil nil),(kenil,tail))','n<=1','~V293_highest_ready tasks t','V293_exit_active_resource n oldhigh','RDYINV G t']:
   self.assertIn(term,public)
  self.assertNotIn('Amapsto',public)
  self.assertNotRegex(public,r'\b(?:cstep|cstepstar|store|load|evalval|evaladdr|evaltype|fresh|InOS)\b')
  for p in [P,Q]:self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
 def test_fresh_branches_and_original_body(self):
  s=(R/P).read_text()
  for term in ['assert(Body:forall b,fresh M b','V293_branching_cstep_TaskSim','V293_exit_saved_successor','V293_exit_exec_successor','V293_tick_allocate_frame','V293_tick_raw_slot_update','V293_exit_active_running_eval','V293_exit_guard_helper_TaskSim','V293_exit_active_saved_pack']:
   self.assertIn(term,s)
  self.assertIn('((bu,0%Z),Tint8)::rest',s)
  self.assertNotIn('GoodInvAsrt(SWINVt',s)
 def test_nonempty_controls_and_unmet_gate(self):
  q=(R/Q).read_text();public=q.split('Theorem ACnonempty_API_entry :',1)[1].split('Proof.',1)[0]
  self.assertNotIn('getsched',public);self.assertNotIn('fun _=>True',public)
  for term in ['ACbase','ACfresh_exists','ACsaved_initialization_control','Some Vundef','Some(Vint32 Int.zero)','ACclient_call_not_OS','GHspec','152%positive']:
   self.assertIn(term,q)
  e=read('entry-classification-review.json')
  self.assertFalse(e['protocol_primary_gate_satisfied']);self.assertFalse(e['scall_TaskSim'])
  self.assertIn('from scall',read('protocol.json')['subject'])
  doc=(R/'audit/STAGE288_EXIT_ACTIVE_CALL.md').read_text()
  for term in ['不是客户端 `scall` 完整调用 TaskSim','不是完整调用执行消融','强 current guard 缺口','uCOS3 未开始','不是 Post=True','未满足这个主门槛']:
   self.assertIn(term,doc)
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
