"""连续初始化返回接入原强就绪payload；不把输入负例早拒绝计作下游执行。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage346-init-ready-payload'
PS = ['certiucos/v293/proofs/V293InitReadyPayload.v',
      'audit/probes/V293InitReadyPayloadProbe.v']
ALLOWED = {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class InitReadyPayloadTests(unittest.TestCase):
    def test_prospective_one_byte_protocol(self):
        for n in ['protocol', 'regression-plan']:
            self.assertEqual((D / (n + '.sha256')).read_text().split(),
                             [sha(D / (n + '.json')), n + '.json'])
            self.assertTrue(read(n + '.json')['prospective'])
        p = read('protocol.json')
        self.assertEqual(set(p['allowed']), ALLOWED)
        self.assertEqual(p['regression']['tests'], 3021)
        self.assertFalse(p['regression']['gate_waived'])
        self.assertEqual(p['ablation']['factor'], 'only unaccessed row0 byte changes from 0 to 1')
        self.assertIn('same complete canonical priority table', p['ablation']['fixed'])
        self.assertIn('input bitmap/task relation gate rejection only', p['ablation']['negative'])

    def test_fixed_source_and_original_hook_order(self):
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

    def test_original_payload_same_heap_no_post_or_execution_oracle(self):
        s = (R / PS[0]).read_text()
        body = s.split('Theorem V293_OS_TCBInit_ready_return_under_hooks :', 1)[1]
        pre, post = body.split(' exists Mf,', 1)
        self.assertEqual(pre.count('V293_records_hook_return'), 2)
        for x in ['V293_local_steps', 'V293_ready_rel', 'V293_ready_payload', 'V293_ready_loads']:
            self.assertNotIn(x, pre)
        for x in ['V293_bitmap_tasks lo0 hi0 tasks', 'V293_init_priority_table entries tasks',
                  'nth p entries Vnull=Vnull', 'V293_owned_task_records tasks ** Atrue',
                  'V293_init_other_row br lo0 hi0 p::frame']:
            self.assertIn(x, pre)
        for x in ['V293_local_steps', '(ge,caller,Mf,ir,aux,O,op)',
                  'V293_ready_payload br bg table tasks\'', 'V293_init_ready_insert',
                  'V293_init_ready_pack', 'V293_OS_TCBInit_canonical_return_under_hooks']:
            self.assertIn(x, post)
        self.assertNotIn('Definition V293_ready_payload', s)
        self.assertIn('Permutation', s)
        self.assertNotIn('CertiOS.audit.', s)

    def test_all_sixteen_roots_repeated_compilation_and_recursive_trust(self):
        roots = [Path(p).stem + '.' + n for p in PS for n in
                 re.findall(r"^(?:Lemma|Theorem|Corollary) ([\w']+)\s*:", (R / p).read_text(), re.M)]
        t = read('trust.json')
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 16)
        self.assertEqual(len(roots), 16)
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

    def test_allocated_entry_prefix_both_inputs_and_return_observations(self):
        q = (R / PS[1]).read_text()
        for x in ['Theorem IRPLiteralEntry : forall bad', 'Theorem IRPSpatialEntry : forall bad',
                  'Theorem IRPPrefix : forall bad', 'Theorem IRPGoodCall', 'Lemma IRPJointReads',
                  'V293_ready_owned_observation', 'V293_task_record_sub', 'Lemma IRPBitmapReads',
                  'Lemma IRPJointCanary', 'V293_rdy_raw_load']:
            self.assertIn(x, q)
        self.assertNotIn('IRPHooks', q.split('Theorem IRPPrefix :', 1)[1].split('Proof.', 1)[0])
        call = q.split('Theorem IRPGoodCall :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(call.count('IRPHooks'), 2)
        self.assertIn('exists Mf', call)
        self.assertIn('CIRState Mf |= IRPJoint', call)
        self.assertIn('V293_task_records M CIRUpdated', q)
        for x in ['Some(V293_byteval 0)', 'Some(V293_byteval 24)', 'Some(V293_byteval 2)',
                  'Some(Vint32(Int.repr 77))']:
            self.assertIn(x, q)

    def test_only_unaccessed_byte_and_input_relation_rejection(self):
        a = read('ablation.json')
        for k in ['positive_bitmap', 'both_canonical_tables', 'both_physical_entries',
                  'same_task_map', 'same_selected_row_and_group', 'outside_one_byte_unchanged',
                  'both_prefixes_to_first_hook_without_hook_contract']:
            self.assertTrue(a[k])
        for k in ['negative_bitmap', 'negative_downstream_executed', 'reachable_bad_state_claimed',
                  'downstream_validation_inferred_from_gate_rejection']:
            self.assertFalse(a[k])
        self.assertEqual(a['rejection_stage'], 'input bitmap/task relation gate only')
        supplement = read('adversarial-supplement.json')
        self.assertFalse(supplement['unique_failing_gate_claimed'])
        self.assertFalse(supplement['group_consistency_mechanism_isolated'])
        group = lambda lo, hi: int(lo != 0) + 2 * int(hi != 0)
        self.assertEqual(supplement['positive_derived_group'], group(0, 16))
        self.assertEqual(supplement['negative_derived_group'], group(1, 16))
        for n in ['IRPPhysicalOutside', 'IRPChangedByte', 'IRPNegativeBitmapRejected', 'IRPLiteralEntry', 'IRPPrefix']:
            self.assertIn('V293InitReadyPayloadProbe.' + n, read('trust.json')['roots'])
        tasks = {12}
        bitmap = lambda lo, hi: {p for p in range(13) if ((lo if p < 8 else hi) >> (p % 8)) & 1}
        self.assertEqual(bitmap(0, 16), tasks)
        self.assertEqual(bitmap(1, 16) - tasks, {0})
        self.assertEqual([p for p in range(16) if (((0 ^ 1) | ((16 ^ 16) << 8)) >> p) & 1], [0])

    def test_old_inputs_append_only_project_and_cache_restoration(self):
        self.assertEqual([p for p, h in read('baseline.json').items()
                          if not (R / p).is_file() or sha(R / p) != h], [])
        prev = json.loads((R / 'audit/logs/stage345-canonical-init-return/checkpoint-evidence-manifest.json').read_text())
        self.assertEqual([p for p, row in prev.items() if p not in
                          {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject'} and sha(R / p) != row['sha256']], [])
        expected = (D / '_CoqProject.baseline').read_bytes() + (PS[0] + '\n').encode()
        self.assertTrue((R / '_CoqProject').read_bytes().startswith(expected))
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(PS[0]), 1)
        for n in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / n).read_bytes().endswith((D / (n + '.baseline')).read_bytes()))
        for p, row in read('cache-backups.json').items():
            self.assertEqual(read('cache-restoration.json')['after'][p], row['sha256'])

    def test_bounded_evidence_and_existing_failures_not_hidden(self):
        e = json.loads((R / 'audit/init-ready-payload-evidence-stage346.json').read_text())
        self.assertTrue(e['continuous_return_under_hooks_accepted'] and e['original_ready_payload_established'])
        for k in ['full_target_linked', 'whole_OSInit_execution', 'concrete_GOOD_OS_instance',
                  'CPU_hook_implementations_proved', 'strong_ready_list_invariant_established',
                  'shared_ready_core_established', 'ghost_map_update_is_abstract_commit']:
            self.assertFalse(e[k])
        self.assertEqual(e['coverage_registration_status'], 'NOT_REGISTERED_IN_LEGACY_AGGREGATE')
        self.assertEqual(e['source_identity_sha256'], '74390755cddc42a391055da46b744bbf32e77ba3dc025c2ae55b9441ba6170da')
        for p, h in e['inputs'].items():
            self.assertEqual(sha(R / p), h)
        doc = (R / 'audit/STAGE346_INIT_READY_PAYLOAD.md').read_text()
        for x in ['不是具体内核GOOD_OS', '不是OSInit执行证明', '两个CPU hook', 'ADR0005',
                  'K1–K4', 'uCOS3', '总目标保持active', '输入门', '447', '预留', 'ready_core']:
            self.assertIn(x, doc)
        self.assertTrue(read('adversarial-review.json')['completed'])
        self.assertEqual(read('build.json')['exit'], 0)
        self.assertEqual(read('project-audit.json')['exit'], 0)
        self.assertEqual((D / 'diff-check.log').read_bytes(),
                         (R / 'audit/logs/stage345-canonical-init-return/diff-check.log').read_bytes())
        self.assertNotEqual(read('make-audit.json')['exit'], 0)
        self.assertIn('stale function evidence input identity', (D / 'make-audit.log').read_text())
