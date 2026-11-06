"""连续初始化返回的完整优先级表与物理记录；两个CPU hook仍为前提。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage345-canonical-init-return'
PS = ['certiucos/v293/proofs/V293CanonicalInitReturn.v',
      'audit/probes/V293CanonicalInitReturnProbe.v']
ALLOWED = {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class CanonicalInitReturnTests(unittest.TestCase):
    def test_prospective_single_factor_protocol(self):
        for n in ['protocol', 'regression-plan']:
            self.assertEqual((D / (n + '.sha256')).read_text().split(),
                             [sha(D / (n + '.json')), n + '.json'])
            self.assertTrue(read(n + '.json')['prospective'])
        p = read('protocol.json')
        self.assertEqual(set(p['allowed']), ALLOWED)
        self.assertEqual(p['regression']['tests'], 3013)
        self.assertFalse(p['regression']['gate_waived'])
        self.assertIn('same physical TCB entry and task map', p['ablation']['fixed'])
        self.assertIn('input gate rejection only', p['ablation']['negative'])

    def test_fresh_fixed_source_and_two_real_hooks(self):
        self.assertEqual(read('source-replay.json')['exit'], 0)
        inventory = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        self.assertEqual(read('source-identities.json'), [x for x in inventory['functions']
                         if x['name'] in ['OS_InitTCBList', 'OS_TCBInit']])
        for row in read('source-identities.json'):
            n = row['name']
            snapshot = (D / (n + '.configured.c.snapshot.txt')).read_bytes()
            self.assertEqual(hashlib.sha256(snapshot[:-1]).hexdigest(), row['preprocessed_definition_sha256'])
            self.assertEqual(sha(D / (n + '.source.c.snapshot.txt')), row['source_lines_sha256'])
        c = (D / 'OS_TCBInit.configured.c.snapshot.txt').read_text()
        self.assertLess(c.index('OSTCBInitHook(ptcb)'), c.index('OSTCBPrioTbl[prio] = ptcb'))
        self.assertLess(c.index('OSTCBPrioTbl[prio] = ptcb'), c.index('OSTaskCreateHook(ptcb)'))

    def test_same_return_heap_joint_resources_no_execution_oracle(self):
        s = (R / PS[0]).read_text().split('Theorem V293_OS_TCBInit_canonical_return_under_hooks :', 1)[1]
        pre, post = s.split(' exists Mf,', 1)
        self.assertEqual(pre.count('V293_records_hook_return'), 2)
        self.assertNotIn('V293_local_steps', pre)
        self.assertNotIn('V293_table_loads', pre)
        for x in ['V293_init_priority_table entries tasks', 'nth p entries Vnull=Vnull',
                  'V293_owned_task_records tasks ** Atrue', 'get tasks (bt,Int.repr base)=None']:
            self.assertIn(x, pre)
        for x in ['V293_local_steps', '(ge,caller,Mf,ir,aux,O,op)',
                  'V293_owned_priority_table table', 'V293_owned_task_records tasks\'',
                  'V293_OS_TCBInit_prefix_return_records_under_hooks', 'V293_priority_reassemble']:
            self.assertIn(x, post)
        self.assertIn('V293_priority_hole entries table 0%Z p++frame', pre)
        self.assertIn('Permutation_app_swap_app', post)

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
        for label, p in zip(['return', 'probe'], PS):
            for i in [1, 2]:
                row = read(f'stable-{label}-{i}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / p))
                self.assertEqual(row['source_sha256'], sha(R / p))
            self.assertEqual(read('stable-inputs.json')[p], sha(R / p))
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
        self.assertNotIn('CertiOS.audit.', (R / PS[0]).read_text())

    def test_nonempty_physical_entry_and_all_reads(self):
        q = (R / PS[1]).read_text()
        for x in ['Theorem CIRLiteralEntry : forall bad', 'Theorem CIRSpatialEntry', 'Theorem CIRPrefix',
                  'Theorem CIRGoodCall', 'Lemma CIRJointReads', 'V293_full_priority_table_loads',
                  'V293_task_record_sub', 'Lemma CIRJointCanary', 'V293_rdy_raw_load']:
            self.assertIn(x, q)
        self.assertNotIn('CIRHooks', q.split('Theorem CIRPrefix :', 1)[1].split('Proof.', 1)[0])
        call = q.split('Theorem CIRGoodCall :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(call.count('CIRHooks'), 2)
        self.assertIn('exists Mf', call)
        self.assertIn('CIRState Mf |= CIRJoint', call)
        self.assertIn('V293_task_records M CIRUpdated', q)
        self.assertIn('Some(Vint32(Int.repr 77))', q)

    def test_single_slot_rejection_is_input_gate_only(self):
        a = read('ablation.json')
        for k in ['positive_old_relation', 'negative_old_relation', 'positive_canonical',
                  'both_physical_entries', 'same_task_map', 'outside_four_bytes_unchanged']:
            self.assertTrue(a[k])
        for k in ['negative_canonical', 'negative_downstream_executed', 'reachable_bad_state_claimed',
                  'downstream_validation_inferred_from_gate_rejection']:
            self.assertFalse(a[k])
        self.assertEqual(a['rejection_stage'], 'input canonical relation gate only')
        for n in ['CIRPhysicalOutside', 'CIRNegativeCanonicalRejected', 'CIRLiteralEntry']:
            self.assertIn('V293CanonicalInitReturnProbe.' + n, read('trust.json')['roots'])
        good = [None] * 12 + ['old']
        bad = list(good)
        bad[0] = 'old'
        tasks = {'old': 12}
        old = lambda slots: all(slots[p] == t for t, p in tasks.items())
        canonical = lambda slots: old(slots) and all(t is None or tasks[t] == p for p, t in enumerate(slots))
        self.assertTrue(old(good) and old(bad) and canonical(good))
        self.assertFalse(canonical(bad))
        self.assertEqual([i for i in range(13) if good[i] != bad[i]], [0])

    def test_frozen_inputs_append_only_registration_and_caches(self):
        self.assertEqual([p for p, h in read('baseline.json').items()
                          if not (R / p).is_file() or sha(R / p) != h], [])
        prev = json.loads((R / 'audit/logs/stage344-init-priority-canonical/checkpoint-evidence-manifest.json').read_text())
        self.assertEqual([p for p, row in prev.items() if p not in
                          {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject'} and sha(R / p) != row['sha256']], [])
        expected = (D / '_CoqProject.baseline').read_bytes() + (PS[0] + '\n').encode()
        self.assertTrue((R / '_CoqProject').read_bytes().startswith(expected))
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(PS[0]), 1)
        for n in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / n).read_bytes().endswith((D / (n + '.baseline')).read_bytes()))
        for p, row in read('cache-backups.json').items():
            self.assertEqual(read('cache-restoration.json')['after'][p], row['sha256'])

    def test_bounded_claims_build_review_not_concrete_good_os(self):
        e = json.loads((R / 'audit/canonical-init-return-evidence-stage345.json').read_text())
        self.assertTrue(e['continuous_return_under_hooks_accepted'])
        for k in ['full_target_linked', 'whole_OSInit_execution', 'concrete_GOOD_OS_instance',
                  'CPU_hook_implementations_proved', 'strong_ready_list_invariant_established']:
            self.assertFalse(e[k])
        self.assertEqual(e['coverage_registration_status'], 'NOT_REGISTERED_IN_LEGACY_AGGREGATE')
        self.assertEqual(e['source_identity_sha256'], '74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da')
        for p, h in e['inputs'].items():
            self.assertEqual(sha(R / p), h)
        doc = (R / 'audit/STAGE345_CANONICAL_INIT_RETURN.md').read_text()
        for x in ['不是具体内核GOOD_OS', '不是OSInit执行证明', '两个CPU hook', 'ADR0005',
                  'K1–K4', 'uCOS3', '总目标保持active', '输入门', '447', '预留']:
            self.assertIn(x, doc)
        self.assertTrue(read('adversarial-review.json')['completed'])
        self.assertEqual(read('build.json')['exit'], 0)
        self.assertEqual(read('project-audit.json')['exit'], 0)
        self.assertEqual((D / 'diff-check.log').read_bytes(),
                         (R / 'audit/logs/stage344-init-priority-canonical/diff-check.log').read_bytes())
        self.assertNotEqual(read('make-audit.json')['exit'], 0)
        self.assertIn('stale function evidence input identity', (D / 'make-audit.log').read_text())
