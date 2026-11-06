"""检查分支接口及冻结证据；形式证明以 Coq kernel 为准。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage290-exit-nested-call'
P='certiucos/v293/proofs/V293ExitNestedCallTaskSim.v'
Q='audit/probes/V293ExitNestedCallTaskSimProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda n:json.loads((D/n).read_text())
class ExitNestedCallTests(unittest.TestCase):
 def test_identity_and_fixed_program(self):
  self.assertEqual(sha(R/P),'40de75c96650a257eabe7b2528d39bb44e0342f5f811fbf92844aebe997c4125')
  self.assertEqual(sha(R/Q),'638f57689f6e257fe61883374382e9835087678834d43323d7866d4c0eb98d1c')
  self.assertEqual((R/'_CoqProject').read_text().splitlines().count(P),1)
  self.assertNotIn(Q,(R/'_CoqProject').read_text())
  self.assertEqual(len(read('baseline.json')['files']),1807)
  self.assertEqual((D/'protocol.sha256').read_text().split(),[sha(D/'protocol.json'),'protocol.json'])
  for p,h in read('source-identity.json')['files'].items():self.assertEqual(sha(R/p),h,p)
 def test_public_matching_calls_no_simulation_premise(self):
  s=(R/P).read_text();public=s.split('Theorem V293_exit_nested_client_call_TaskSim :',1)[1].split('Proof.',1)[0]
  self.assertEqual(len(re.findall(r'^Theorem ',s,re.M)),1)
  self.assertEqual(public.count('TaskSim('),1)
  self.assertEqual(public.count('(curs(scall f nil),(kenil,tail))'),2)
  for term in ['fst(fst A)f=Some','spec_done None','2<=n','n<256','RDYINV G t']:
   self.assertIn(term,public)
  self.assertNotRegex(public,r'\b(?:cstep|cstepstar|store|load|evalval|evaladdr|evaltype|fresh|InOS)\b')
  for term in ['Amapsto','po helper','get ge lock','getsched','V293_highest_ready']:
   self.assertNotIn(term,public)
  for p in [P,Q]:self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
 def test_constructed_whole_branch_and_reclose(self):
  s=(R/P).read_text()
  for term in ['V293_exit_decrement_eval','V293_owned_record_cell_update','V293_nested_zero_eval','V293_helper_assignment_TaskSim','V293_nested_reclose','V293_storage_pending_TaskSim','V293_tick_allocate_frame','V293_exit_saved_successor','V293_nested_entry_TaskSim','apply hapiexit_step']:
   self.assertIn(term,s)
  self.assertNotIn('spec_seq sched',s)
  self.assertIn('V293_exit_active_resource br bg bp bt bc bh bo bk bn bl bu rest t nc oldtarget c',s)
 def test_nonempty_instance_and_single_factor(self):
  q=(R/Q).read_text();public=q.split('Theorem NCnonempty_client_call :',1)[1].split('Proof.',1)[0]
  for term in ['2<=n','n<256','ACmemory n','RDYINV ACinv']:
   self.assertIn(term,public)
  for term in ['ACbase','NCdecrement_control','NCdecrement_control_2','NCdecrement_control_255','V293_storebytes_outside','V293_byteval_injective_bounded']:
   self.assertIn(term,q)
  self.assertEqual(q.count('eapply V293_nested_zero_eval'),2)
  self.assertIn('(b,i)<>(150%positive,0%Z)',q)
  doc=(R/'audit/STAGE290_EXIT_NESTED_CALL.md').read_text()
  for term in ['不是完整调用执行消融','强 current guard 缺口','uCOS3 未开始','不是 Post=True','分支专用','旧失败保留']:
   self.assertIn(term,doc)
 def test_stable_compiles_and_recursive_trust(self):
  roots=[]
  for p,row in read('stable-compiles.json').items():
   self.assertEqual(sha(R/p),row['sha256']);self.assertEqual(len(row['runs']),2)
   roots += [Path(p).stem+'.'+n for n in row['roots']]
   for run in row['runs']:
    self.assertEqual(run['exit'],0);self.assertEqual(run['initial_source_sha256'],sha(R/p));self.assertEqual(run['source_sha256'],sha(R/p))
  t=read('trust.json');self.assertTrue(t['passed']);self.assertTrue(t['recursive'])
  self.assertEqual(len(roots),14);self.assertEqual(t['roots'],roots);self.assertEqual(t['roots_printed'],len(roots));self.assertEqual(list(read('assumptions-by-root.json')),roots)
  for row in t['commands']:self.assertEqual(row['exit'],0)
  self.assertLessEqual(set(t['assumptions']),{'Classical_Prop.classic','FunctionalExtensionality.functional_extensionality_dep'})
if __name__=='__main__':unittest.main()
