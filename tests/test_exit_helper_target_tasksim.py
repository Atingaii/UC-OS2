"""检查 helper 调用到目标/changed 后缀的连接，不把局部实例算作整核入口。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage285-helper-target'
P='certiucos/v293/proofs/V293ExitHelperTargetTaskSim.v'
Q='audit/probes/V293ExitHelperTargetProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda n:json.loads((D/n).read_text())
class ExitHelperTargetTests(unittest.TestCase):
 def test_frozen_identity_registration_and_old_sources(self):
  self.assertEqual(sha(R/P),'ee8a23a70b3f8d7ab4d625dfc9abe222030c1696888f6d34a31c110ac06d7cbb')
  self.assertEqual(sha(R/Q),'67f41a9f1b11d3208735e981146854840f274a620ee824ea17d7b82912f5bed9')
  self.assertEqual((R/'_CoqProject').read_text().splitlines().count(P),1)
  self.assertNotIn(Q,(R/'_CoqProject').read_text())
  self.assertEqual(len(read('baseline.json')['files']),1659)
  self.assertEqual((D/'protocol.sha256').read_text().split(),[sha(D/'protocol.json'),'protocol.json'])
  for p,h in read('source-identity.json')['files'].items():self.assertEqual(sha(R/p),h,p)
  self.assertEqual(sha(R/'certiucos/v293/proofs/V293SchedHelperBodyTaskSim.v'),'26c2fa6518781e803a03d4780280d5a7f2948990353e41f02d8bb4ea8cd7a597')
  self.assertEqual(sha(R/'audit/probes/V293SchedHelperBodyProbe.v'),'a5eab7e0e118dcc69b27486ba5054ecff1c0880bc69e19905c61fbb6194e73b2')
 def test_public_interface_has_no_simulation_or_execution_premise(self):
  s=(R/P).read_text();public=s.split('Theorem V293_exit_helper_target_TaskSim :',1)[1].split('Proof.',1)[0]
  self.assertEqual(len(re.findall(r'^Theorem ',s,re.M)),1)
  self.assertEqual(public.count('TaskSim('),1)
  self.assertNotRegex(public,r'\b(?:cstep|cstepstar|free|store|load|evalval|evaladdr|evaltype|fresh|allocb)\b')
  for token in ['V293_current_task tasks t nc','~V293_highest_ready tasks t','V293_exit_helper_frame oldhigh','curs(scall helper nil)','V293_OSSched_target_update table high target','V293_OSSched_increment counter','V293_interrupt_handoff high current target']:
   self.assertIn(token,public)
  for p in [P,Q]:self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
 def test_permission_reunion_and_continuation_discharge(self):
  s=(R/P).read_text()
  decoder=s.split('Lemma V293_helper_decoder_storage :',1)[1].split('Qed.',1)[0]
  self.assertEqual(decoder.split('Proof.',1)[0].count('V293_read_bytes bt 0%Z V293_ready_table'),2)
  for token in ['V293_read_bytes_array','V293_array_reunite','V293_array_to_storage']:self.assertIn(token,decoder)
  for token in ['Let Rest := DecoderCells++rest.','V293_read_bytes bt 0%Z V293_ready_table **V293_storage rest','V293_exit_helper_target_resources','V293_storage_append','V293_sched_helper_full_TaskSim','V293_exit_target_TaskSim','V293_OSSched_current_target','assert(Different:nh<>nc).','V293_ready_selection_task']:
   self.assertIn(token,s)
  self.assertNotIn('GoodInvAsrt(SWINVt',s)
 def test_constructed_cut_and_single_permission_control_limits(self):
  q=(R/Q).read_text()
  for token in ['HTbase','HTentry','HTnonempty_call_cut','V293_full_array_witness','V293_array_borrow','RTenv_spatial','OwnershipCellsSpatial','exact HTentry.']:
   self.assertIn(token,q)
  control=q.split('Theorem HTpermission_control :',1)[1].split('Proof.',1)[0]
  for token in ['load Tint8(HTone false)','load Tint8(HTone true)','store Tint8(HTone false)','store Tint8(HTone true)','(true,Byte(Byte.repr 4))']:
   self.assertIn(token,control)
  self.assertEqual(control.count('Some(V293_byteval 0)'),2)
  self.assertEqual(control.count('(92%positive,0%Z)'),5)
  self.assertEqual(control.count('(V293_byteval 4)'),2)
  doc=(R/'audit/STAGE285_HELPER_TARGET.md').read_text()
  for token in ['不是原完整活跃调用入口可达性','不是完整外层调用执行消融','初始资源更强','不承诺原表值不变','等优先级返回待连接','强 current guard 缺口不变','uCOS3 未开始']:
   self.assertIn(token,doc)
 def test_stable_compiles_and_recursive_kernel(self):
  stable=read('stable-compiles.json');roots=[]
  for p,row in stable.items():
   self.assertEqual(row['sha256'],sha(R/p));self.assertEqual(len(row['runs']),2)
   roots += [Path(p).stem+'.'+n for n in row['roots']]
   for run in row['runs']:
    self.assertEqual(run['exit'],0);self.assertEqual(run['initial_source_sha256'],run['source_sha256']);self.assertEqual(run['source_sha256'],sha(R/p))
  t=read('trust.json');self.assertTrue(t['passed']);self.assertTrue(t['recursive'])
  self.assertEqual(t['roots'],roots);self.assertEqual(len(roots),10);self.assertEqual(t['roots_printed'],10)
  self.assertEqual(list(read('assumptions-by-root.json')),roots)
  for row in t['commands']:self.assertEqual(row['exit'],0)
  self.assertLessEqual(set(t['assumptions']),{'Classical_Prop.classic','FunctionalExtensionality.functional_extensionality_dep'})
if __name__=='__main__':unittest.main()
