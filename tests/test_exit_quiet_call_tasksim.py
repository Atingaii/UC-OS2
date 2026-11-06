"""结构与证据回归；形式正确性以 Coq kernel 检查为准。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage291-exit-quiet-call'
P='certiucos/v293/proofs/V293ExitQuietCallTaskSim.v'
Q='audit/probes/V293ExitQuietCallTaskSimProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda n:json.loads((D/n).read_text())
class ExitQuietCallTests(unittest.TestCase):
 def test_fixed_identity_and_project(self):
  self.assertEqual(sha(R/P),'0d592bb59e21144cf0dc927c818e65fb965677474fda1b5a2d7e283904740a92')
  self.assertEqual(sha(R/Q),'2e048618cb56d485d1b3ed790ca665a1a2915ec5d72ade374c1ef47ce9fff6c9')
  self.assertEqual((R/'_CoqProject').read_text().splitlines().count(P),1)
  self.assertNotIn(Q,(R/'_CoqProject').read_text())
  self.assertEqual(len(read('baseline.json')['files']),1979)
  self.assertEqual((D/'protocol.sha256').read_text().split(),[sha(D/'protocol.json'),'protocol.json'])
  for p,h in read('source-identity.json')['files'].items():self.assertEqual(sha(R/p),h,p)
  self.assertEqual(read('source-identity-scope.json')['branch'],'OSRunning=0; false running guard')
 def test_same_client_call_without_execution_or_simulation_premise(self):
  s=(R/P).read_text();public=s.split('Theorem V293_exit_quiet_client_call_TaskSim :',1)[1].split('Proof.',1)[0]
  self.assertEqual(len(re.findall(r'^Theorem ',s,re.M)),1)
  self.assertEqual(public.count('TaskSim('),1)
  self.assertEqual(public.count('(curs(scall f nil),(kenil,tail))'),2)
  for term in ['fst(fst A)f=Some','spec_done None','saved<>running','get ge running=Some(bu,Tint8)','RDYINV G t']:
   self.assertIn(term,public)
  self.assertNotRegex(public,r'\b(?:cstep|cstepstar|store|load|evalval|evaladdr|evaltype|fresh|InOS)\b')
  for term in ['po helper','get ge nesting','get ge lock','getsched','V293_highest_ready','Amapsto']:
   self.assertNotIn(term,public)
  for p in [P,Q]:self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
 def test_constructed_entry_false_guard_and_original_postcondition(self):
  s=(R/P).read_text()
  for term in ['V293_tick_allocate_frame','V293_exit_saved_successor','V293_tick_raw_slot_update','V293_quiet_running_eval','(take:=false)','V293_quiet_reclose','V293_invariant_return_suffix','V293_storage_return_disabled_SWINV','V293_nested_nil_call_bridge','V293_quiet_entry_TaskSim']:
   self.assertIn(term,s)
  self.assertIn('V293_owned_record_cell((bu,0%Z),Tint8,V293_byteval 0) **(Base **CurTid t)',s)
  self.assertNotIn('spec_seq sched',s)
  self.assertNotIn('eapply V293_exit_active_call_TaskSim',s)
 def test_nonempty_independent_heap_and_local_one_byte_control(self):
  q=(R/Q).read_text();public=q.split('Theorem QCnonempty_client_call :',1)[1].split('Proof.',1)[0]
  for term in ['QCmemory','QCspec','RDYINV QCinv']:
   self.assertIn(term,public)
  for term in ['QCjoin','QCbase','RTfull OwnershipWaiting','OwnershipCellsMemory QCcells','QCrunning_control','(b,i)<>(152%positive,0%Z)','V293_storebytes_outside','Some(Vint32 Int.zero)','Some(Vint32 Int.one)']:
   self.assertIn(term,q)
  self.assertNotIn('ACmemory',q)
  doc=(R/'audit/STAGE291_EXIT_QUIET_CALL.md').read_text()
  for term in ['不是完整调用执行消融','强 current guard 缺口','uCOS3 未开始','不是 Post=True','分支专用','旧失败保留','没有 helper 绑定']:
   self.assertIn(term,doc)
 def test_repeat_compiles_and_recursive_kernel_check(self):
  roots=[]
  for p,row in read('stable-compiles.json').items():
   self.assertEqual(sha(R/p),row['sha256']);self.assertEqual(len(row['runs']),2)
   roots += [Path(p).stem+'.'+n for n in row['roots']]
   for run in row['runs']:
    self.assertEqual(run['exit'],0);self.assertEqual(run['initial_source_sha256'],sha(R/p));self.assertEqual(run['source_sha256'],sha(R/p))
  t=read('trust.json');self.assertTrue(t['passed']);self.assertTrue(t['recursive'])
  self.assertEqual(len(roots),13);self.assertEqual(t['roots'],roots);self.assertEqual(t['roots_printed'],len(roots));self.assertEqual(list(read('assumptions-by-root.json')),roots)
  for row in t['commands']:self.assertEqual(row['exit'],0)
  self.assertLessEqual(set(t['assumptions']),{'Classical_Prop.classic','FunctionalExtensionality.functional_extensionality_dep'})
if __name__=='__main__':unittest.main()
