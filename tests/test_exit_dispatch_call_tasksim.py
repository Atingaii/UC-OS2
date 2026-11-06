"""结构检查不替代 Coq kernel；边界含非空完整调用与单步对照。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage295-exit-dispatch-call'
P='certiucos/v293/proofs/V293ExitDispatchCallTaskSim.v'
Q='audit/probes/V293ExitDispatchCallTaskSimProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda n:json.loads((D/n).read_text())
class ExitDispatchCallTests(unittest.TestCase):
 def test_frozen_identity_and_project(self):
  self.assertEqual(sha(R/P),'5bb402ae6cb681585082dc30dceeefca222203276dade68c9a3fc0903c79f8fb')
  self.assertEqual(sha(R/Q),'2fae6f3acb741d1ccaa39b2e52887b2126b3d78da52b282a022f35a4736bfef3')
  self.assertEqual((R/'_CoqProject').read_text().splitlines().count(P),1)
  self.assertNotIn(Q,(R/'_CoqProject').read_text())
  self.assertEqual((D/'protocol.sha256').read_text().split(),[sha(D/'protocol.json'),'protocol.json'])
  for p,h in read('source-identity.json')['files'].items():self.assertEqual(sha(R/p),h,p)
 def test_public_interface_hides_branch_and_execution(self):
  s=(R/P).read_text();public=s.split('Theorem V293_exit_dispatch_client_call_TaskSim :',1)[1].split('Proof.',1)[0]
  self.assertEqual(len(re.findall(r'^Theorem ',s,re.M)),1)
  self.assertEqual(public.count('TaskSim('),1);self.assertEqual(public.count('curs(scall f nil)'),2)
  for term in ['getsched(pc,A)=V293_scheduler','spec_seq sched(spec_done None)','V293_current_task tasks t nc','n<=1','(forall i,ir i=false)','RDYINV G t']:
   self.assertIn(term,public)
  self.assertNotIn('V293_highest_ready',public)
  self.assertNotRegex(public,r'\b(?:cstep|cstepstar|store|load|evalval|evaladdr|evaltype|fresh|InOS)\b')
  for p in [P,Q]:self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
 def test_real_self_sched_and_both_full_entries_connected(self):
  s=(R/P).read_text()
  for term in ['spec_sched_step','spec_seq_step2','spec_seq_step1','hapiexit_step','V293_self_sched_nil_call_bridge','V293_exit_active_abstract_current','V293_ready_switch_full','V293_shared_abs_get','V293_exit_equal_entry_TaskSim','V293_exit_self_sched_client_call_TaskSim','V293_exit_client_call_TaskSim','classic(V293_highest_ready tasks t)']:
   self.assertIn(term,s)
  self.assertIsNone(re.search(r'^Definition ',s,re.M))
 def test_nonempty_same_program_and_abstract_only_control(self):
  s=(R/Q).read_text()
  for name,heap,task in [('DCsame_nonempty_client_call','ECmemory n','OwnershipReady'),('DCchanged_nonempty_client_call','ACmemory n','OwnershipWaiting')]:
   public=s.split('Theorem '+name+' :',1)[1].split('Proof.',1)[0]
   for term in ['forall n ip','n<=1',heap,'(ACpo,CGempty,ip)','(RCprogram,CCspec)','RDYINV',task]:self.assertIn(term,public)
  self.assertEqual(s.count('eapply V293_exit_dispatch_client_call_TaskSim'),2)
  for term in ['apply ECbase','apply ACbase','DCcurrent_single_factor','DCself_sched_step','DCself_sched_requires_highest','DCwaiting_no_self_sched','DCself_sched_skip_with_frame']:
   self.assertIn(term,s)
  doc=(R/'audit/STAGE295_EXIT_DISPATCH_CALL.md').read_text()
  for term in ['不是完整调用执行消融','强 current guard','uCOS3 未开始','不是 Post=True','仅统一 enabled dispatch','旧失败保留','不是统一 OSIntExit']:
   self.assertIn(term,doc)
 def test_repeated_compiles_and_recursive_kernel(self):
  roots=[]
  for p,row in read('stable-compiles.json').items():
   self.assertEqual(sha(R/p),row['sha256']);self.assertEqual(len(row['runs']),2)
   roots += [Path(p).stem+'.'+n for n in row['roots']]
   for run in row['runs']:
    self.assertEqual(run['exit'],0);self.assertEqual(run['initial_source_sha256'],sha(R/p));self.assertEqual(run['source_sha256'],sha(R/p))
  t=read('trust.json');self.assertTrue(t['passed']);self.assertTrue(t['recursive'])
  self.assertEqual(len(roots),12);self.assertEqual(t['roots'],roots);self.assertEqual(t['roots_printed'],12);self.assertEqual(list(read('assumptions-by-root.json')),roots)
  for row in t['commands']:self.assertEqual(row['exit'],0)
  self.assertLessEqual(set(t['assumptions']),{'Classical_Prop.classic','FunctionalExtensionality.functional_extensionality_dep'})
if __name__=='__main__':unittest.main()
