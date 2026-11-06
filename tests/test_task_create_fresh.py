"""构造实际fresh块、保留零字节分离边界；完整成功仍需uniform真实Hook。"""
from pathlib import Path
import hashlib,json,re,unittest
R=Path(__file__).resolve().parents[1];L=R/'audit/logs/stage74-task-create-fresh'
P='certiucos/v293/proofs/V293TaskCreateFresh.v';B='audit/probes/V293TaskCreateFreshProbe.v';A='audit/probes/V293TaskCreateFreshAnchor.v'
read=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
class TaskCreateFreshTests(unittest.TestCase):
 def test_protected_prefix_and_source_identity(self):
  b=read(L/'baseline.json');allowed={'_CoqProject','README.md','VERIFICATION_STATUS.md','docs/开发中/时钟中断如何跳过零延时任务.md'}
  self.assertEqual((len(b['files']),len(b['sources']),len(b['products'])),(16167,237,1185))
  for p,h in b['files'].items():
   if p not in allowed:self.assertEqual(sha(R/p),h,p)
  for p,h in b['products'].items():self.assertEqual(sha(R/p),h,p)
  self.assertEqual([p for p in (R/'_CoqProject').read_text().splitlines() if p.endswith('.v')][:238],b['sources']+[P])
  s=read(L/'source-connection.json');self.assertTrue(s['all94_identities_equal']);self.assertTrue(all(not h['defined'] for h in s['hook_declarations']))
  self.assertTrue(read(L/'declaration-connection.json')['passed'])
 def test_actual_fresh_allocation_and_conditional_interface(self):
  for p,n in read(L/'accepted-versions.json').items():
   self.assertEqual(sha(R/p),sha(L/(n+'.v.snapshot.txt')));self.assertEqual(read(L/(n+'.json'))['exit'],0)
   self.assertNotRegex((R/p).read_text(),r'\b(Axiom|Admitted|admit|Parameter|Conjecture)\b');self.assertNotIn('Require Import CertiOS.audit.probes.',(R/p).read_text())
  s=(R/P).read_text()
  for n in ['HalfPermMap.bounded','Pos.max','V293_cells_upper_bound','V293_create_fresh_twelve_avoiding','V293_create_call_prologue','V293_OSTaskCreateExt_success_call_under_hooks']:self.assertIn(n,s)
  generic=s[s.index('Theorem V293_create_fresh_call_prologue'):s.index('Proof.',s.index('Theorem V293_create_fresh_call_prologue'))]
  self.assertLess(generic.index('exists btask'),generic.index('NoDup'))
  for n in ['FreshLiteralPrologue','CallLiteralEntry','FreshConditionalExecution','CreateResultReads']:self.assertIn(n,(R/B).read_text())
  self.assertIn('= 31',(L/'probe01.log').read_text())
  x=read(L/'proof-report.json');self.assertTrue(x['uniform_Hook_family_required']);self.assertTrue(x['uniform_Hook_family_is_stronger_than_fixed_layout']);self.assertFalse(x['real_Hook_implementations']);self.assertFalse(x['GOOD_OS'])
 def test_prospective_endpoint_controls_and_survivor_ablation(self):
  x=read(L/'control-results.json');self.assertTrue(x['passed']);self.assertEqual(len(x['rows']),3)
  plan=read(L/'control-plan.json');self.assertTrue(plan['frozen_before_compilation']);s=(L/'positive01.v.snapshot.txt').read_text()
  self.assertEqual(read(L/'positive01.json')['exit'],0);self.assertEqual(sha(L/'positive01.v.snapshot.txt'),plan['positive_sha256'])
  proofs=lambda t:re.findall(r'Proof\.(.*?)Qed\.',t,re.S)
  for n,v in plan['variants'].items():
   t=(L/(n+'01.v.snapshot.txt')).read_text();a=s.index('Theorem '+v['theorem']);b=s.index('Proof.',a)
   self.assertEqual(t,s[:a]+s[a:b].replace(v['old'],v['new'],1)+s[b:]);self.assertEqual(proofs(t),proofs(s));self.assertEqual(sha(L/(n+'01.v.snapshot.txt')),v['sha256']);self.assertEqual(read(L/(n+'01.json'))['exit'],1)
  a=read(L/'survivor-ablation-result.json');self.assertTrue(a['passed']);self.assertTrue(a['both_fresh']);self.assertTrue(a['both_distinct']);self.assertTrue(a['zero_size_owned']);self.assertTrue(a['with_bound_away']);self.assertTrue(a['without_bound_overlap']);self.assertFalse(a['downstream_allocation_body_or_Hook_credit'])
 def test_build_trust_and_bounded_review(self):
  b=read(L/'build.json');self.assertEqual((b['exit'],b['active_sources'],b['old_products_reused']),(0,238,1185));self.assertFalse(b['source_only_cold_build'])
  t=read(L/'trust.json');self.assertTrue(t['passed']);self.assertTrue(t['assumptions_allowed']);self.assertEqual(t['roots_printed'],len(t['roots']));self.assertEqual(t['roots_printed'],60);self.assertEqual([c['exit'] for c in t['commands']],[0,0])
  rows=read(L/'adversarial-review.json');self.assertGreaterEqual(len(rows),15)
  for row in rows:self.assertTrue(row['resolution']);self.assertIn(row['kind'],['test','bounded claim','limitation'])
  self.assertEqual(read(L/'proof-report.json')['formal_six_gates'],[94,1,1,1,1,0])
