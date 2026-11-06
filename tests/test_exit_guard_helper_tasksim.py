"""锁定组合接口及证据边界；语义正确性由 Coq kernel 检查。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage287-guard-helper'
P='certiucos/v293/proofs/V293ExitGuardHelperTaskSim.v'
Q='audit/probes/V293ExitGuardHelperProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda n:json.loads((D/n).read_text())
class ExitGuardHelperTests(unittest.TestCase):
 def test_identity_and_fixed_program(self):
  self.assertEqual(sha(R/P),'243be7a74344f116d3a6663833269965419e0b0bb4e10a2f26d96c7ddac3c939')
  self.assertEqual(sha(R/Q),'6e643be4d4ba91e4da04966713cbb8bfefbda9d12b13ac1bd8d1b3b8c88071f9')
  self.assertEqual((R/'_CoqProject').read_text().splitlines().count(P),1)
  self.assertNotIn(Q,(R/'_CoqProject').read_text())
  self.assertEqual(len(read('baseline.json')['files']),1667)
  self.assertEqual((D/'protocol.sha256').read_text().split(),[sha(D/'protocol.json'),'protocol.json'])
  for p,h in read('source-identity.json')['files'].items():self.assertEqual(sha(R/p),h,p)
 def test_public_interface_has_no_simulation_or_execution_premise(self):
  s=(R/P).read_text();public=s.split('Theorem V293_exit_guard_helper_TaskSim :',1)[1].split('Proof.',1)[0]
  self.assertEqual(len(re.findall(r'^Theorem ',s,re.M)),1)
  self.assertEqual(public.count('TaskSim('),1)
  self.assertIn('n<=1',public)
  self.assertIn('~V293_highest_ready tasks t',public)
  self.assertIn('V293_exit_guard_resource bn bl n(Resource oldhigh)',public)
  self.assertIn('sseq(V293_OSIntExit_nesting_dispatch',public)
  self.assertIn(')(sprim excrit)',public)
  self.assertNotRegex(public,r'\b(?:cstep|cstepstar|store|load|evalval|evaladdr|evaltype)\b')
  for p in [P,Q]:self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
 def test_stack_transport_and_storage_ownership(self):
  s=(R/P).read_text()
  for name in ['V293_guard_helper_stack','V293_ready_critical_stack','V293_guard_helper_storage','V293_exit_cell_to_storage','V293_invariant_encrit_TaskSim','V293_exit_nesting_prefix_TaskSim','V293_exit_helper_target_TaskSim']:
   self.assertIn(name,s)
  self.assertIn('(((bn,0%Z),Tint8)::((bl,0%Z),Tint8)::rest)',s)
  self.assertNotIn('GoodInvAsrt(SWINVt',s)
  self.assertNotIn('apply V293_exit_critical_prefix_TaskSim',s)
 def test_nonempty_and_ablation_limits(self):
  q=(R/Q).read_text();public=q.split('Theorem GHinstantiated_critical_cut :',1)[1].split('Proof.',1)[0]
  self.assertNotIn('getsched',public);self.assertNotIn('fun _=>True',public)
  self.assertEqual(public.count('TaskSim('),1)
  for name in ['GHbase','GHguard_permission_control','GHoriginal_critical_shape','GHspec','150%positive','151%positive']:
   self.assertIn(name,q)
  doc=(R/'audit/STAGE287_GUARD_HELPER.md').read_text()
  for term in ['不是原完整活跃调用入口 TaskSim','不是完整调用执行消融','强 current guard 缺口','uCOS3 未开始','不是 Post=True']:
   self.assertIn(term,doc)
 def test_serial_compiles_and_recursive_trust(self):
  roots=[]
  for p,row in read('stable-compiles.json').items():
   self.assertEqual(sha(R/p),row['sha256']);self.assertEqual(len(row['runs']),2)
   roots += [Path(p).stem+'.'+n for n in row['roots']]
   for run in row['runs']:
    self.assertEqual(run['exit'],0);self.assertEqual(run['initial_source_sha256'],sha(R/p));self.assertEqual(run['source_sha256'],sha(R/p))
  t=read('trust.json');self.assertTrue(t['passed']);self.assertTrue(t['recursive'])
  self.assertEqual(t['roots'],roots);self.assertEqual(t['roots_printed'],10);self.assertEqual(list(read('assumptions-by-root.json')),roots)
  for row in t['commands']:self.assertEqual(row['exit'],0)
  self.assertLessEqual(set(t['assumptions']),{'Classical_Prop.classic','FunctionalExtensionality.functional_extensionality_dep'})
if __name__=='__main__':unittest.main()
