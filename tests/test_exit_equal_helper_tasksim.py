"""结构及证据回归；证明有效性由 Coq kernel 而非文本断言判定。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage293-exit-equal-helper'
P='certiucos/v293/proofs/V293ExitEqualHelperTaskSim.v'
Q='audit/probes/V293ExitEqualHelperTaskSimProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda n:json.loads((D/n).read_text())
class ExitEqualHelperTests(unittest.TestCase):
 def test_identity_and_project(self):
  self.assertEqual(sha(R/P),'154e13e208856fd9916fab62a35180ba06257223fe6b89276d0316bb10f8860e')
  self.assertEqual(sha(R/Q),'1a1a1b6429e2d503d36104186b7a3af38278843bcae25c3cc45723a76f9fc682')
  self.assertEqual((R/'_CoqProject').read_text().splitlines().count(P),1)
  self.assertNotIn(Q,(R/'_CoqProject').read_text())
  self.assertEqual(len(read('baseline.json')['files']),2206)
  self.assertEqual(sha(D/'protocol.json'),'d58aef1e72957dc0f9458b7ce27a04bff23713cf0449343c092fd20a32d2ff75')
  self.assertEqual((D/'protocol.sha256').read_text().split(),[sha(D/'protocol.json'),'protocol.json'])
  for p,h in read('source-identity.json')['files'].items():self.assertEqual(sha(R/p),h,p)
 def test_public_interface_has_no_execution_or_continuation_result_premise(self):
  s=(R/P).read_text();public=s.split('Theorem V293_exit_equal_helper_TaskSim :',1)[1].split('Proof.',1)[0]
  self.assertEqual(len(re.findall(r'^Theorem ',s,re.M)),1)
  self.assertEqual(public.count('TaskSim('),1)
  for term in ['V293_current_task tasks t nc','V293_highest_ready tasks t','po helper=Some','curs(scall helper nil)','(pc,A)(SKIP,(kenil,tail))','RDYINV G t']:
   self.assertIn(term,public)
  self.assertNotRegex(public,r'\b(?:cstep|cstepstar|store|load|evalval|evaladdr|evaltype|fresh|InOS)\b')
  self.assertNotIn('getsched',public)
  for p in [P,Q]:self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
 def test_actual_helper_target_false_comparison_and_original_return(self):
  s=(R/P).read_text()
  for term in ['V293_sched_helper_full_TaskSim','V293_exit_helper_target_resources','V293_highest_unique','V293_OSSched_current_target','rewrite Equal in Owned','V293_owned_record_cell_update','V293_target_assignment_TaskSim','V293_OSSched_byte_comparison_eval','rewrite Nat.eqb_refl','(take:=false)','V293_storage_pending_TaskSim','V293_equal_target_reclose']:
   self.assertIn(term,s)
  self.assertNotIn('getsched',s)
  self.assertNotIn('V293_exit_changed_TaskSim with',s)
 def test_nonempty_heap_and_local_single_byte_control(self):
  q=(R/Q).read_text();public=q.split('Theorem EHnonempty_call_cut :',1)[1].split('Proof.',1)[0]
  for term in ['EHmemory','RIabstract OwnershipReady','RDYINV EHinv OwnershipReady','(RCprogram,A)(SKIP,(kenil,kstop))']:
   self.assertIn(term,public)
  for term in ['EHjoin','EHbase','EHentry','RTfull OwnershipReady','OwnershipCellsMemory EHcells','EHcurrent_byte_control','(b,i)<>(94%positive,0%Z)','V293_storebytes_outside','Some(Vint32 Int.zero)','Some(Vint32 Int.one)']:
   self.assertIn(term,q)
  self.assertNotIn('HTmemory',q)
  doc=(R/'audit/STAGE293_EXIT_EQUAL_HELPER.md').read_text()
  for term in ['不是完整调用执行消融','强 current guard 缺口','uCOS3 未开始','不是 Post=True','分支专用','旧失败保留','尚未消费抽象 sched','不是 OSIntExit 完整客户端调用']:
   self.assertIn(term,doc)
 def test_repeat_compiles_and_recursive_kernel_check(self):
  roots=[]
  for p,row in read('stable-compiles.json').items():
   self.assertEqual(sha(R/p),row['sha256']);self.assertEqual(len(row['runs']),2)
   roots += [Path(p).stem+'.'+n for n in row['roots']]
   for run in row['runs']:
    self.assertEqual(run['exit'],0);self.assertEqual(run['initial_source_sha256'],sha(R/p));self.assertEqual(run['source_sha256'],sha(R/p))
  t=read('trust.json');self.assertTrue(t['passed']);self.assertTrue(t['recursive'])
  self.assertEqual(len(roots),11);self.assertEqual(t['roots'],roots);self.assertEqual(t['roots_printed'],len(roots));self.assertEqual(list(read('assumptions-by-root.json')),roots)
  for row in t['commands']:self.assertEqual(row['exit'],0)
  self.assertLessEqual(set(t['assumptions']),{'Classical_Prop.classic','FunctionalExtensionality.functional_extensionality_dep'})
if __name__=='__main__':unittest.main()
