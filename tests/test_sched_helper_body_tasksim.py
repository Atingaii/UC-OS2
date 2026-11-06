"""检查原 helper 的条件调用组合、原体非空实例与单赋值执行控制。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage284-helper-body'
P='certiucos/v293/proofs/V293SchedHelperBodyTaskSim.v'
Q='audit/probes/V293SchedHelperBodyProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda n:json.loads((D/n).read_text())
class SchedHelperBodyTests(unittest.TestCase):
 def test_frozen_sources_and_registration(self):
  self.assertEqual(sha(R/P),'26c2fa6518781e803a03d4780280d5a7f2948990353e41f02d8bb4ea8cd7a597')
  self.assertEqual(sha(R/Q),'a5eab7e0e118dcc69b27486ba5054ecff1c0880bc69e19905c61fbb6194e73b2')
  self.assertEqual((R/'_CoqProject').read_text().splitlines().count(P),1)
  self.assertNotIn(Q,(R/'_CoqProject').read_text())
  self.assertEqual(len(read('baseline.json')['files']),1655)
  self.assertEqual((D/'protocol.sha256').read_text().split(),[sha(D/'protocol.json'),'protocol.json'])
  for p,h in read('source-identity.json')['files'].items():self.assertEqual(sha(R/p),h,p)
 def test_public_interface_only_restored_caller(self):
  s=(R/P).read_text();public=s.split('Theorem V293_sched_helper_full_TaskSim :',1)[1].split('Proof.',1)[0]
  self.assertEqual(len(re.findall(r'^Theorem ',s,re.M)),1)
  self.assertEqual(public.count('TaskSim('),2)
  self.assertIn('V293_helper_resource br bg bp bt bh t R oldhigh',public)
  self.assertIn('(forall tasks lo hi entries next message Mret,',public)
  self.assertIn('(SKIP,(kenil,ks))(ge,caller,Mret,ir,(false,nil,ci))',public)
  self.assertNotRegex(public,r'\b(?:free|cstep|cstepstar|store|satp|evalval|evaladdr|evaltype|fresh|allocb)\b')
  for p in [P,Q]:self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
 def test_real_assignments_allocation_and_environment(self):
  s=(R/P).read_text()
  for token in ['V293_OSSchedNew_row_eval','V293_OSSchedNew_priority_eval','V293_helper_assignment_TaskSim','join_store_join','V293_tick_raw_slot_update','V293_ready_release_byte','V293_helper_ready_return_TaskSim','V293_branching_cstep_TaskSim','V293_helper_fresh_byte_distinct','forall b,fresh M b','V293_ready_lenv_frame']:
   self.assertIn(token,s)
  self.assertNotIn('GoodInvAsrt(SWINVt',s)
  self.assertNotIn('GoodInvAsrt (SWINVt',s)
  self.assertIn('GoodInvAsrt R',s)
  q=(R/Q).read_text()
  for token in ['HBall_fresh_body','HBnonempty_body','Vundef','memory_has_fresh_block','HBbase','HBloads','HBallocation_load']:
   self.assertIn(token,q)
 def test_single_high_assignment_control_and_limits(self):
  q=(R/Q).read_text();mutant=q.split('Definition HBwithout_high :=',1)[1].split('.',1)[0]
  self.assertIn('sassign(evar 104%Z)',mutant);self.assertIn('(sskip None))sret',mutant)
  control=q.split('Theorem HBhigh_omission_control :',1)[1].split('Proof.',1)[0]
  self.assertEqual(control.count('(RHge,HBlocal b,allocb(RHmemory OwnershipWaiting)b 0%Z 1)'),2)
  for token in ['curs HBbody','curs HBwithout_high','kcall 107%Z HBbody RTle ks','Some(V293_byteval 4)','Some(V293_byteval 88)','Some(V293_byteval 99)','(c,i)<>(91%positive,0%Z)']:
   self.assertIn(token,control)
  for token in ['V293_OSSchedNew_updates_execution','V293_helper_return_steps','HBfree_local_write']:
   self.assertIn(token,q)
  doc=(R/'audit/STAGE284_HELPER_BODY.md').read_text()
  for token in ['不是原完整活跃调用入口','不是完整外层调用执行消融','没有单独消融 y 赋值','Aie false','uCOS3 未开始']:
   self.assertIn(token,doc)
 def test_stable_compiles_and_recursive_kernel(self):
  stable=read('stable-compiles.json');roots=[]
  for p,row in stable.items():
   self.assertEqual(row['sha256'],sha(R/p));self.assertEqual(len(row['runs']),2)
   roots += [Path(p).stem+'.'+n for n in row['roots']]
   for run in row['runs']:
    self.assertEqual(run['exit'],0);self.assertEqual(run['initial_source_sha256'],run['source_sha256']);self.assertEqual(run['source_sha256'],sha(R/p))
  t=read('trust.json');self.assertTrue(t['passed']);self.assertTrue(t['recursive'])
  self.assertEqual(t['roots'],roots);self.assertEqual(len(roots),19);self.assertEqual(t['roots_printed'],19)
  self.assertEqual(list(read('assumptions-by-root.json')),roots)
  for row in t['commands']:self.assertEqual(row['exit'],0)
  self.assertLessEqual(set(t['assumptions']),{'Classical_Prop.classic','FunctionalExtensionality.functional_extensionality_dep'})
if __name__=='__main__':unittest.main()
