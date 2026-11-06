"""固定临界/guard 前缀的接口与证据口径；语义正确性由 Coq 检查。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage286-critical-prefix'
P='certiucos/v293/proofs/V293ExitCriticalPrefixTaskSim.v'
Q='audit/probes/V293ExitCriticalPrefixProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda n:json.loads((D/n).read_text())
class ExitCriticalPrefixTests(unittest.TestCase):
 def test_frozen_identity_registration_and_old_sources(self):
  self.assertEqual(sha(R/P),'d60f8648997481ab2e70fb14ca772bbf636060c706f9d11b21db475133281f0e')
  self.assertEqual(sha(R/Q),'433f298ae396590173ba2ef62717ec8868df70d70ea4de23f333b25928354f23')
  self.assertEqual((R/'_CoqProject').read_text().splitlines().count(P),1)
  self.assertNotIn(Q,(R/'_CoqProject').read_text())
  self.assertEqual(len(read('baseline.json')['files']),1663)
  self.assertEqual((D/'protocol.sha256').read_text().split(),[sha(D/'protocol.json'),'protocol.json'])
  for p,h in read('source-identity.json')['files'].items():self.assertEqual(sha(R/p),h,p)
  self.assertEqual(sha(R/'certiucos/v293/proofs/V293ExitHelperTargetTaskSim.v'),'ee8a23a70b3f8d7ab4d625dfc9abe222030c1696888f6d34a31c110ac06d7cbb')
  self.assertEqual(sha(R/'audit/probes/V293ExitHelperTargetProbe.v'),'67f41a9f1b11d3208735e981146854840f274a620ee824ea17d7b82912f5bed9')
 def test_public_continuation_is_explicit(self):
  s=(R/P).read_text();public=s.split('Theorem V293_exit_critical_prefix_TaskSim :',1)[1].split('Proof.',1)[0]
  self.assertEqual(len(re.findall(r'^Theorem ',s,re.M)),1)
  self.assertEqual(public.count('TaskSim('),2)
  self.assertIn('(forall M\'',public)
  self.assertIn('GoodInvAsrt R',public)
  self.assertIn('n<=1',public)
  self.assertIn('V293_exit_guard_resource bn bl 0 R',public)
  self.assertIn('curs(sseq(sprim encrit)',public)
  self.assertNotRegex(public,r'\b(?:cstep|cstepstar|store|load|evalval|evaladdr|evaltype)\b')
  for p in [P,Q]:self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
 def test_real_encrit_and_owned_updates(self):
  s=(R/P).read_text();critical=s.split('Lemma V293_invariant_encrit_TaskSim :',1)[1].split('Qed.',1)[0]
  self.assertIn('apply task_sim.',critical)
  self.assertEqual(len(re.findall(r'^ - ',critical,re.M)),7)
  for token in ['V293_encrit_successor','V293_invariant_nil_empty','V293_pending_join_frame','inapi_step','encrit_step']:
   self.assertIn(token,critical)
  for token in ['V293_owned_record_cell_update','V293_record_star_load_l','V293_record_star_load_r','V293_exit_decrement_eval','V293_helper_assignment_TaskSim','good_inv_prop']:
   self.assertIn(token,s)
  self.assertNotIn('GoodInvAsrt(SWINVt',s)
 def test_nonempty_and_single_decrement_control_limits(self):
  q=(R/Q).read_text();public=q.split('Theorem EPnonempty_prefix :',1)[1].split('Proof.',1)[0]
  self.assertEqual(public.count('TaskSim('),1)
  self.assertIn('fun _=>True',public)
  for token in ['EPentry','EPdispatch','sfree nil None','EPencrit_frame','EPsingle_decrement_control','V293_assign_byte_execution','V293_rekey_if_execution','EPcontrol_guard']:
   self.assertIn(token,q)
  control=q.split('Theorem EPsingle_decrement_control :',1)[1].split('Proof.',1)[0]
  self.assertIn('curs(V293_OSIntExit_nesting_dispatch 130%Z 131%Z sret)',control)
  self.assertIn('curs(V293_OSIntExit_guards 130%Z 131%Z sret)',control)
  self.assertIn('if Nat.eqb n 0 then sret else sskip None',control)
  self.assertIn('then Mf=EPmemory n else store',control)
  self.assertEqual(control.count('cstepstar'),2)
  doc=(R/'audit/STAGE286_CRITICAL_PREFIX.md').read_text()
  for token in ['dispatch TaskSim continuation 前提','尚未与第285步 helper 后缀整合','synthetic sret dispatch 和 Post=True','不是完整外层调用执行消融','强 current guard 缺口','uCOS3 未开始']:
   self.assertIn(token,doc)
 def test_stable_compiles_and_recursive_kernel(self):
  roots=[]
  for p,row in read('stable-compiles.json').items():
   self.assertEqual(row['sha256'],sha(R/p));self.assertEqual(len(row['runs']),2)
   roots += [Path(p).stem+'.'+n for n in row['roots']]
   for run in row['runs']:
    self.assertEqual(run['exit'],0);self.assertEqual(run['initial_source_sha256'],run['source_sha256']);self.assertEqual(run['source_sha256'],sha(R/p))
  t=read('trust.json');self.assertTrue(t['passed']);self.assertTrue(t['recursive'])
  self.assertEqual(t['roots'],roots);self.assertEqual(len(roots),17);self.assertEqual(t['roots_printed'],17)
  self.assertEqual(list(read('assumptions-by-root.json')),roots)
  for row in t['commands']:self.assertEqual(row['exit'],0)
  self.assertLessEqual(set(t['assumptions']),{'Classical_Prop.classic','FunctionalExtensionality.functional_extensionality_dep'})
if __name__=='__main__':unittest.main()
