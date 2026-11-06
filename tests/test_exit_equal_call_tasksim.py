"""结构检查不替代 Coq kernel；最终检查仍含非空实例及递归 coqchk。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage294-exit-equal-call'
P='certiucos/v293/proofs/V293ExitEqualCallTaskSim.v'
Q='audit/probes/V293ExitEqualCallTaskSimProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda n:json.loads((D/n).read_text())
class ExitEqualCallTests(unittest.TestCase):
 def test_frozen_identity_and_project(self):
  self.assertEqual(sha(R/P),'537f7a7b3d0ca271b347d0f822cd1c090e6e3a39a3e8b774b6513dac26c8fa40')
  self.assertEqual(sha(R/Q),'5b4d06680d6e6ac99ce6256ca536dd434eed814c8403b43de20b445d0441eff6')
  self.assertEqual((R/'_CoqProject').read_text().splitlines().count(P),1)
  self.assertNotIn(Q,(R/'_CoqProject').read_text())
  self.assertEqual((D/'protocol.sha256').read_text().split(),[sha(D/'protocol.json'),'protocol.json'])
  self.assertEqual(sha(D/'protocol.json'),'015cc32c70061a83cbc357d16d856220c2de167e5e1c3568b97446967519bc84')
  for p,h in read('source-identity.json')['files'].items():self.assertEqual(sha(R/p),h,p)
 def test_public_interface_does_not_delegate_execution(self):
  s=(R/P).read_text();public=s.split('Theorem V293_exit_equal_client_call_TaskSim :',1)[1].split('Proof.',1)[0]
  self.assertEqual(len(re.findall(r'^Theorem ',s,re.M)),1)
  self.assertEqual(public.count('TaskSim('),1);self.assertEqual(public.count('curs(scall f nil)'),2)
  for term in ['spec_done None','V293_current_task tasks t nc','V293_highest_ready tasks t','n<=1','(forall i,ir i=false)','RDYINV G t']:
   self.assertIn(term,public)
  self.assertNotRegex(public,r'\b(?:cstep|cstepstar|store|load|evalval|evaladdr|evaltype|fresh|InOS)\b')
  self.assertNotIn('getsched',public)
  for p in [P,Q]:self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
 def test_fresh_allocation_prefix_and_helper_are_connected(self):
  s=(R/P).read_text()
  for term in ['V293_nested_nil_call_bridge','V293_exit_exec_successor','V293_exit_saved_successor','V293_tick_allocate_frame','memory_has_fresh_block','V293_tick_raw_slot_update','V293_exit_saved_assignment_TaskSim','V293_exit_active_running_eval','V293_invariant_encrit_TaskSim','V293_exit_nesting_prefix_TaskSim','V293_exit_equal_helper_TaskSim','V293_exit_active_saved_pack']:
   self.assertIn(term,s)
  self.assertNotRegex(s,r'^Definition ',re.M)
 def test_nonempty_heap_and_entry_only_binding_control(self):
  q=(R/Q).read_text();public=q.split('Theorem ECnonempty_client_call :',1)[1].split('Proof.',1)[0]
  for term in ['forall n ip','n<=1','ECmemory n','RIabstract OwnershipReady','RDYINV ECinv OwnershipReady']:
   self.assertIn(term,public)
  for term in ['ECbase','ECjoin','RTfull OwnershipReady','V293_byteval 4','ECbinding_single_factor','ECabstract_entry','ECmissing_binding_no_high_step','ECclient_step_unchanged','ECactual_client_low_step']:
   self.assertIn(term,q)
  self.assertNotIn('ACmemory',q)
  doc=(R/'audit/STAGE294_EXIT_EQUAL_CALL.md').read_text()
  for term in ['不是完整调用执行消融','强 current guard','uCOS3 未开始','不是 Post=True','分支专用','旧失败保留','尚未消费抽象 sched no-op','不是统一 OSIntExit']:
   self.assertIn(term,doc)
 def test_repeated_compiles_and_recursive_kernel(self):
  roots=[]
  for p,row in read('stable-compiles.json').items():
   self.assertEqual(sha(R/p),row['sha256']);self.assertEqual(len(row['runs']),2)
   roots += [Path(p).stem+'.'+n for n in row['roots']]
   for run in row['runs']:
    self.assertEqual(run['exit'],0);self.assertEqual(run['initial_source_sha256'],sha(R/p));self.assertEqual(run['source_sha256'],sha(R/p))
  t=read('trust.json');self.assertTrue(t['passed']);self.assertTrue(t['recursive'])
  self.assertEqual(len(roots),13);self.assertEqual(t['roots'],roots);self.assertEqual(t['roots_printed'],13);self.assertEqual(list(read('assumptions-by-root.json')),roots)
  for row in t['commands']:self.assertEqual(row['exit'],0)
  self.assertLessEqual(set(t['assumptions']),{'Classical_Prop.classic','FunctionalExtensionality.functional_extensionality_dep'})
if __name__=='__main__':unittest.main()
