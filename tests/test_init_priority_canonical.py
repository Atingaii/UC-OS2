"""初始化阶段的双向优先级表、实际写表及单槽晚拒绝；不是整核验收。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage344-init-priority-canonical'
PS = ['certiucos/v293/proofs/V293InitPriorityTable.v',
      'audit/probes/V293InitPriorityTableProbe.v']
ALLOWED = {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class InitPriorityCanonicalTests(unittest.TestCase):
    def test_prospective_single_factor_protocol(self):
        for n in ['protocol', 'regression-plan']:
            self.assertEqual((D / (n + '.sha256')).read_text().split(),
                             [sha(D / (n + '.json')), n + '.json'])
            self.assertTrue(read(n + '.json')['prospective'])
        p = read('protocol.json')
        self.assertEqual(set(p['allowed']), ALLOWED)
        self.assertEqual(p['regression']['baseline_tests'], 3005)
        self.assertFalse(p['regression']['gate_waived'])
        self.assertIn('same task map', p['ablation']['fixed'])
        self.assertIn('no execution claim for mutation', p['ablation']['negative'])

    def test_fresh_fixed_source_and_literal_fragment(self):
        self.assertEqual(read('source-replay.json')['exit'], 0)
        inventory = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        names = ['OS_InitTCBList', 'OS_TCBInit']
        self.assertEqual(read('source-identities.json'), [x for x in inventory['functions'] if x['name'] in names])
        for row in read('source-identities.json'):
            name = row['name']
            snapshot = (D / (name + '.configured.c.snapshot.txt')).read_bytes()
            self.assertEqual(hashlib.sha256(snapshot[:-1]).hexdigest(), row['preprocessed_definition_sha256'])
            self.assertEqual(sha(D / (name + '.source.c.snapshot.txt')), row['source_lines_sha256'])
        c = (D / 'OS_TCBInit.configured.c.snapshot.txt').read_text()
        self.assertLess(c.index('OSTCBInitHook(ptcb)'), c.index('OSTCBPrioTbl[prio] = ptcb'))
        self.assertLess(c.index('OSTCBPrioTbl[prio] = ptcb'), c.index('OSTaskCreateHook(ptcb)'))
        q = (R / PS[1]).read_text()
        self.assertIn('Lemma IPLiteralSourceFragment', q)
        self.assertIn('match V293_TCBInit_success_suffix', q)
        self.assertIn('exact V293InitTCBClearProbe.InitLiteralEntry', q)

    def test_constructed_store_same_heap_and_no_output_oracle(self):
        s = (R / PS[0]).read_text().split('Theorem V293_OS_TCBInit_canonical_priority_write :', 1)[1]
        pre, post = s.split('  exists Mf,', 1)
        self.assertIn('V293_owned_priority_table table entries', pre)
        self.assertNotIn('store(', pre)
        self.assertNotIn('V293_table_loads', pre)
        for x in ['nth p entries Vnull=Vnull', 'get tasks t=None', 'get le 92%Z=None']:
            self.assertIn(x, pre)
        for x in ['V293_full_priority_table_any_slot_store', 'V293_assign_pointer_execution',
                  'V293_init_priority_insert', 'V293_full_priority_table_loads']:
            self.assertIn(x, post)
        self.assertIn('exists Mf,', (R / PS[0]).read_text().split('Theorem V293_OS_InitTCBList_canonical_clear', 1)[1])
        self.assertIn(r'nth p entries Vnull=Vnull \/', (R / PS[0]).read_text())

    def test_all_nineteen_roots_and_recursive_trust(self):
        roots = [Path(p).stem + '.' + n for p in PS for n in
                 re.findall(r"^(?:Lemma|Theorem|Corollary) ([\w']+)\s*:", (R / p).read_text(), re.M)]
        t = read('trust.json')
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 19)
        self.assertEqual(len(roots), 19)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertEqual(set(t['allowed']), ALLOWED)
        self.assertTrue(all(c['exit'] == 0 for c in t['commands']))
        byroot = read('assumptions-by-root.json')
        self.assertEqual(set(byroot), set(roots))
        self.assertTrue(all(set(v) <= ALLOWED for v in byroot.values()))
        for label, p in zip(['priority', 'probe'], PS):
            for i in [1, 2]:
                row = read(f'stable-{label}-{i}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / p))
                self.assertEqual(row['source_sha256'], sha(R / p))
            self.assertEqual(read('stable-inputs.json')[p], sha(R / p))
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
        self.assertNotIn('CertiOS.audit.', (R / PS[0]).read_text())

    def test_duplicate_pointer_rejected_only_at_reverse_gate(self):
        a = read('ablation.json')
        self.assertEqual(a['positive_old_relation'], True)
        self.assertEqual(a['negative_old_relation'], True)
        self.assertEqual(a['positive_canonical'], True)
        self.assertEqual(a['negative_canonical'], False)
        self.assertFalse(a['early_rejection'])
        self.assertFalse(a['source_mutation_reachable_claimed'])
        self.assertTrue(a['same_task_map'] and a['outside_four_bytes_unchanged'])
        self.assertIn('V293InitPriorityTableProbe.IPPhysicalSingleSlotControl', read('trust.json')['roots'])
        # 独立有限列表判定重放，证明本身由上面的Coq根及递归检查承担。
        good = [None] * 12 + ['task301']
        bad = list(good)
        bad[0] = 'task301'
        tasks = {'task301': 12}
        old = lambda slots: all(slots[p] == t for t, p in tasks.items())
        canonical = lambda slots: old(slots) and all(t is None or tasks[t] == p for p, t in enumerate(slots))
        self.assertTrue(old(good) and old(bad) and canonical(good))
        self.assertFalse(canonical(bad))
        self.assertEqual([p for p in range(13) if good[p] != bad[p]], [0])
        q = (R / PS[1]).read_text()
        for x in ['Theorem IPConcreteWrite', 'Theorem IPCanonicalClear',
                  'Theorem IPPhysicalSingleSlotControl', 'V293_storebytes_outside',
                  'load Tint32 Mf(99%positive,0)=Some(Vint32(Int.repr 123))']:
            self.assertIn(x, q)

    def test_frozen_old_inputs_and_append_only_registration(self):
        self.assertEqual([p for p, h in read('baseline.json').items()
                          if not (R / p).is_file() or sha(R / p) != h], [])
        prev = json.loads((R / 'audit/logs/stage343-global-soundness-bridge/checkpoint-evidence-manifest.json').read_text())
        self.assertEqual([p for p, row in prev.items() if p not in
                          {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject'} and sha(R / p) != row['sha256']], [])
        expected = (D / '_CoqProject.baseline').read_bytes() + (PS[0] + '\n').encode()
        self.assertTrue((R / '_CoqProject').read_bytes().startswith(expected))
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(PS[0]), 1)
        for n in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / n).read_bytes().endswith((D / (n + '.baseline')).read_bytes()))

    def test_bounded_claims_not_concrete_good_os(self):
        e = json.loads((R / 'audit/init-priority-canonical-evidence-stage344.json').read_text())
        self.assertTrue(e['initialization_table_relation_accepted'])
        for k in ['full_target_linked', 'whole_OSInit_execution', 'concrete_GOOD_OS_instance',
                  'CPU_hooks_executed', 'full_task_record_invariant_established']:
            self.assertFalse(e[k])
        self.assertEqual(e['coverage_registration_status'], 'NOT_REGISTERED_IN_LEGACY_AGGREGATE')
        self.assertEqual(e['source_identity_sha256'], '74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da')
        for p, h in e['inputs'].items():
            self.assertEqual(sha(R / p), h)
        doc = (R / 'audit/STAGE344_INIT_PRIORITY_CANONICAL.md').read_text()
        for x in ['不是具体内核GOOD_OS', '不是OSInit执行证明', '两个CPU hook', 'ADR0005',
                  'K1–K4', 'uCOS3', '总目标保持active', '两个独立入口', '447', '预留']:
            self.assertIn(x, doc)

    def test_build_review_and_cache_preservation(self):
        self.assertTrue(read('adversarial-review.json')['completed'])
        self.assertEqual(read('build.json')['exit'], 0)
        self.assertEqual(read('project-audit.json')['exit'], 0)
        for p, row in read('cache-backups.json').items():
            self.assertEqual(read('cache-restoration.json')['after'][p], row['sha256'])
        self.assertEqual((D / 'diff-check.log').read_bytes(),
                         (R / 'audit/logs/stage343-global-soundness-bridge/diff-check.log').read_bytes())
        self.assertNotEqual(read('make-audit.json')['exit'], 0)
        self.assertIn('stale function evidence input identity', (D / 'make-audit.log').read_text())
