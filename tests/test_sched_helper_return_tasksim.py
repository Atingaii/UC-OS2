"""检查返回后缀接口、独立控制与实际内核证据，不将其计为完整调用。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage283-helper-return'
P='certiucos/v293/proofs/V293SchedHelperReturnTaskSim.v'
Q='audit/probes/V293SchedHelperReturnProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda n:json.loads((D/n).read_text())
class SchedHelperReturnTests(unittest.TestCase):
 def test_frozen_sources_and_registration(self):
  self.assertEqual(sha(R/P),'6df3aa2ece8a7a147816cbf9127f53a6ed451f24fa401c312f191b46f2383b73')
  self.assertEqual(sha(R/Q),'6eb19c6828918e8cc9b2458ace16f8726c109cbe5135eaae0cad9e0507f79818')
  self.assertEqual((R/'_CoqProject').read_text().splitlines().count(P),1)
  self.assertNotIn(Q,(R/'_CoqProject').read_text())
  self.assertEqual(len(read('baseline.json')['files']),1651)
  self.assertEqual((D/'protocol.sha256').read_text().split(),[sha(D/'protocol.json'),'protocol.json'])
  for p,h in read('source-identity.json')['files'].items():self.assertEqual(sha(R/p),h,p)
 def test_public_interface_owns_byte_not_free_oracle(self):
  s=(R/P).read_text();public=s.split('Theorem V293_sched_helper_return_TaskSim :',1)[1].split('Proof.',1)[0]
  self.assertEqual(len(re.findall(r'^Theorem ',s,re.M)),1)
  self.assertEqual(public.count('TaskSim('),2)
  self.assertIn('Amapsto(b,0%Z)Tint8 true v **R',public)
  self.assertIn('(forall Mret,(ge,caller,Mret,ir,(false,nil,ci),O,op)|=R',public)
  self.assertNotRegex(public,r'\b(?:free|cstep|cstepstar|store|satp)\b')
  self.assertIn('V293_ready_release_byte',s)
  for p in [P,Q]:self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
 def test_actual_return_and_frame_preservation(self):
  s=(R/P).read_text()
  for token in ['V293_helper_byte_layout','sret_step','sfree_step','sfreeend_step','sskip_step','free_mono','join_free','V293_free_one_successor','V293_free_end_successor','V293_invariant_cstep_TaskSim']:
   self.assertIn(token,s)
  self.assertEqual(s.split('Lemma V293_helper_return_steps :',1)[1].split('Qed.',1)[0].count('eapply c_stepstarn'),4)
  q=(R/Q).read_text();self.assertIn('HRframe_preserved',q);self.assertIn('join Mret Mf Mallret',q)
 def test_independent_witness_and_bounded_controls(self):
  q=(R/Q).read_text()
  for token in ['HRnonvacuous_return','HRbase','HRgood','HRchoice_erased','HRtwo_choices_exist','HRowned_boundary','V293_sched_storage','V293_return_client_coinduction','free Tint8 b(emp:mem)=None']:
   self.assertIn(token,q)
  doc=(R/'audit/STAGE283_HELPER_RETURN.md').read_text()
  for token in ['不是原完整活跃调用入口','不证明这些写入堆从原函数体可达','raw Vundef','不是完整程序执行消融','函数体前提','uCOS3 未开始']:
   self.assertIn(token,doc)
  self.assertIn('HAframe_excludes_old_choice',(R/'audit/probes/V293SchedHelperAllocationProbe.v').read_text())
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
