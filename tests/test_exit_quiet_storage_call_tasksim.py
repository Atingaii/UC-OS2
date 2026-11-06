"""静态检查与内核证据核对分开；不把共同 Inv 当成共同 API。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1]
D=R/'audit/logs/stage296-quiet-storage-call'
P='certiucos/v293/proofs/V293ExitQuietStorageCallTaskSim.v'
Q='audit/probes/V293ExitQuietStorageCallTaskSimProbe.v'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
read=lambda n:json.loads((D/n).read_text())
class ExitQuietStorageCallTests(unittest.TestCase):
 def test_frozen_identity_and_project(self):
  self.assertEqual(sha(R/P),'22fc95e5509bf80962a692db26da6408618299c783999499ebac1af84609799b')
  self.assertEqual(sha(R/Q),'a22aabdab4b961f265668bad7e642b661907ea2a14109236286dfdf7d0bf504e')
  self.assertEqual((R/'_CoqProject').read_text().splitlines().count(P),1)
  self.assertNotIn(Q,(R/'_CoqProject').read_text())
  self.assertEqual((D/'protocol.sha256').read_text().split(),[sha(D/'protocol.json'),'protocol.json'])
  for p,h in read('source-identity.json')['files'].items():self.assertEqual(sha(R/p),h,p)
 def test_public_interface_no_execution_or_continuation_oracle(self):
  s=(R/P).read_text();public=s.split('Theorem V293_exit_quiet_storage_client_call_TaskSim :',1)[1].split('Proof.',1)[0]
  self.assertEqual(len(re.findall(r'^Theorem ',s,re.M)),1)
  self.assertEqual(public.count('TaskSim('),1);self.assertEqual(public.count('curs(scall f nil)'),2)
  for term in ['spec_done None','(forall i,ir i=false)','RDYINV G t','get ge running=Some(bu,Tint8)']:
   self.assertIn(term,public)
  self.assertNotRegex(public,r'\b(?:cstep|cstepstar|store|load|evalval|evaladdr|evaltype|fresh|InOS)\b')
  self.assertNotIn('spec_choice',s);self.assertNotIn('spec_seq sched',s)
  for p in [P,Q]:self.assertNotRegex((R/p).read_text(),r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
 def test_storage_reclosed_without_new_invariant_model(self):
  s=(R/P).read_text()
  for term in ['V293_storage_insert','V293_storage_split','V293_storage_append','prefix++((bu,0%Z),Tint8)::suffix','V293_exit_quiet_resource','V293_tick_raw_slot_update','V293_tick_allocate_frame','V293_exit_saved_successor','V293_invariant_return_suffix','V293_nested_nil_call_bridge']:
   self.assertIn(term,s)
  self.assertIsNone(re.search(r'^Definition ',s,re.M))
  q=(R/Q).read_text();equality=q.split('Lemma QSsame_invariant :',1)[1].split('Qed.',1)[0]
  self.assertIn('=ACinv',equality);self.assertIn('app_assoc',equality)
  doc=(R/'audit/STAGE296_QUIET_STORAGE_CALL.md').read_text()
  for term in ['不是统一 OSIntExit','强 current guard','uCOS3 未开始','不是 Post=True','完整输入单因素对照','旧失败保留','不是固定完整 API']:
   self.assertIn(term,doc)
 def test_same_nonempty_input_single_byte_full_call(self):
  s=(R/Q).read_text();public=s.split('Theorem QSrunning_single_factor_complete_call :',1)[1].split('Proof.',1)[0]
  self.assertIn('n<256 ->exists M0',public)
  for term in ['store Tint8(ACmemory n)','get M0(b,i)=get(ACmemory n)(b,i)','(ACpo,CGempty,ip)','(RCprogram,QCspec)','RDYINV ACinv','Int.one','Int.zero']:
   self.assertIn(term,public)
  for term in ['pose proof(ACbase n Bound)','V293_owned_record_cell_update','V293_storebytes_outside','apply QSnonempty_client_call','eapply QSupdated_resource','rewrite <-QSsame_invariant']:
   self.assertIn(term,s)
  self.assertNotIn('Definition QSmemory',s)
 def test_repeated_compiles_and_recursive_kernel(self):
  roots=[]
  for p,row in read('stable-compiles.json').items():
   self.assertEqual(sha(R/p),row['sha256']);self.assertEqual(len(row['runs']),2)
   roots += [Path(p).stem+'.'+n for n in row['roots']]
   for run in row['runs']:
    self.assertEqual(run['exit'],0);self.assertEqual(run['initial_source_sha256'],sha(R/p));self.assertEqual(run['source_sha256'],sha(R/p))
  t=read('trust.json');self.assertTrue(t['passed']);self.assertTrue(t['recursive'])
  self.assertEqual(len(roots),9);self.assertEqual(t['roots'],roots);self.assertEqual(t['roots_printed'],9)
  self.assertEqual(list(read('assumptions-by-root.json')),roots)
  for row in t['commands']:self.assertEqual(row['exit'],0)
  self.assertLessEqual(set(t['assumptions']),{'Classical_Prop.classic','FunctionalExtensionality.functional_extensionality_dep'})
if __name__=='__main__':unittest.main()
