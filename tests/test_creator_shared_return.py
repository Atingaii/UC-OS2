"""实际任务创建前缀接到共享返回；单独记录尚未闭合的 hooks 和整核边界。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage351-creator-shared-return'
SOURCES = ['certiucos/v293/proofs/V293CreatorSharedReturn.v',
           'audit/probes/V293CreatorSharedReturnProbe.v']
ALLOWED = {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class CreatorSharedReturnTests(unittest.TestCase):
    def test_prospective_store_only_control(self):
        p = read('protocol.json')
        self.assertTrue(p['prospective'])
        self.assertEqual((D / 'protocol.sha256').read_text().strip(), sha(D / 'protocol.json'))
        self.assertEqual(set(p['allowed']), ALLOWED)
        self.assertEqual(p['control']['factor'], 'omit only the psp returned-value assignment')
        self.assertIn('same independently anchored after-stack heap', p['control']['fixed'])
        self.assertEqual((p['regression']['tests'], p['regression']['failures'], p['regression']['errors']),
                         (3057, 450, 1))
        self.assertFalse(p['regression']['gate_waived'])
        a = read('ablation.json')
        self.assertEqual(a['prospective_protocol_sha256'], sha(D / 'protocol.json'))
        self.assertTrue(a['positive_and_negative_same_heap'] and a['nonempty_records_preserved'])
        self.assertFalse(a['early_rejection_used'] or a['downstream_hook_or_commit_credit'])

    def test_real_caller_and_actual_task_identity(self):
        s = (R / SOURCES[0]).read_text()
        pre, post = s.split('Theorem V293_OSTaskCreateExt_shared_return_under_hooks :', 1)[1].split(" exists Mf clientM',", 1)
        self.assertEqual(pre.count('V293_records_hook_return'), 2)
        self.assertEqual(pre.count('V293_create_stack_return'), 1)
        self.assertIn('spec_crt (V293_task_selector target) argv', pre)
        self.assertIn('vtoZ (V293_task_selector target)=Some clientf', pre)
        self.assertIn('[options;topv;argv;V293_task_selector target]', pre)
        self.assertNotRegex(pre, r'\bentry\b|\bargument\b')
        for token in ['V293_local_steps', 'hpstep', 'V293_ready_payload']:
            self.assertNotIn(token, pre)
        for token in ['curs(V293_TaskCreateExt_prefix', 'V293_TaskCreateExt_calls psp stack',
                      '(curs(sskip None),(kenil,resume))', 'V293_shared_ready_records',
                      'V293_rdy_raw_cells(returned++before++((berr,0%Z),Tint8,Vint32 Int.zero)::afterframe)Atrue']:
            self.assertIn(token, post)
        self.assertNotIn('CertiOS.audit.', s)

    def test_reuse_same_bridge_heap_and_choose_fresh_blocks(self):
        s = (R / SOURCES[0]).read_text()
        for token in ['V293_tcb_fresh_nine_avoiding M(extra++cells)',
                      'V293_OSTaskCreateExt_to_TCB_under_stack_return', 'as(Mbridge&Prefix&AtTCB)',
                      'V293_creator_fresh_records Mbridge tasks\'(tl after++survivors)',
                      'V293_OS_TCBInit_reserved_call_assign_shared_under_hooks',
                      'caller resume ge Mbridge', 'exact Prefix |exact TCB',
                      'clientf tau arg body (V293_task_selector target) argv']:
            self.assertIn(token, s)
        pre = s.split('Theorem V293_OSTaskCreateExt_shared_return_under_hooks :', 1)[1].split(" exists Mf clientM',", 1)[0]
        self.assertNotIn('fresh M b', pre)
        self.assertNotIn('In b blocks', pre)
        self.assertNotIn('V293_init_raw_frame_drop', s)
        self.assertNotRegex(s, r'Definition V293_(?:ready|shared|init_priority)')

    def test_closed_literal_and_independent_store_contrast(self):
        s = (R / SOURCES[1]).read_text()
        for name in ['CSRLiteralEntry', 'CSRSpatialEntry', 'CSRStackValueBridge',
                     'CSRBridgeLoads', 'CSRStoreOnlyContrast']:
            self.assertRegex(s, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        for token in ['CIRLiteral.', 'V293_OSTaskCreateExt_after_stack_to_TCB',
                      'V293_create_TCB_cont', 'Some Vnull',
                      '~(CSRState(CIRMemory CSRCells)', 'Some(Vptr(700%positive,Int.zero))',
                      'Some CSRValue', 'Vint32(Int.repr 77)']:
            self.assertIn(token, s)
        self.assertNotIn('V293_records_hook_return', s)
        self.assertNotIn('V293_create_stack_return', s)
        self.assertNotIn('Fixpoint', s)
        doc = (R / 'audit/STAGE351_CREATOR_SHARED_RETURN.md').read_text()
        for bound in ['逻辑影子', '物理预留槽', '两个原CPU hook契约',
                      'ADR0009', '独立的栈返回现场', 'Mbridge', 'TaskSim']:
            self.assertIn(bound, doc)

    def test_eight_roots_recursive_trust_and_repeated_compilation(self):
        roots = [Path(p).stem + '.' + n for p in SOURCES for n in
                 re.findall(r"^(?:Lemma|Theorem|Corollary) ([\w']+)\s*:", (R / p).read_text(), re.M)]
        t = read('trust.json')
        self.assertEqual(len(roots), 8)
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 8)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertEqual(set(t['allowed']), ALLOWED)
        byroot = read('assumptions-by-root.json')
        self.assertEqual(set(byroot), set(roots))
        self.assertTrue(all(set(v) <= ALLOWED for v in byroot.values()))
        for label, source in zip(['return', 'probe'], SOURCES):
            for i in [1, 2]:
                row = read(f'stable-{label}-{i}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / source))
                self.assertEqual(row['source_sha256'], sha(R / source))
            self.assertEqual(read('stable-inputs.json')[source], sha(R / source))
            self.assertEqual(read('trust-inputs.json')[source], sha(R / source))
            self.assertNotRegex((R / source).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')

    def test_frozen_release_and_honest_credit_boundaries(self):
        dep = read('source-dependency.json')
        self.assertEqual(dep['target_release'], 'V2.93.01')
        self.assertEqual(dep['target_commit'], '0c4a48e6fbc6e915714e816196619a5481accf0c')
        for field, digest in [('source', 'source_sha256'), ('caller_source', 'caller_source_sha256'), ('component', 'sha256')]:
            self.assertEqual(dep[digest], sha(R / dep[field]))
        self.assertFalse(dep['changed_C'] or dep['verified_frontend'])
        e = json.loads((R / 'audit/creator-shared-return-evidence-stage351.json').read_text())
        for flag in ['runtime_reserved_slot_prefix_connected', 'caller_argument_evaluation_composed',
                     'fresh_local_blocks_selected_at_bridge', 'same_actual_task_and_argument',
                     'real_caller_return_assignment_constructed', 'strong_ready_predicate_unchanged']:
            self.assertTrue(e[flag], flag)
        for flag in ['full_target_linked', 'whole_OSTaskCreate_TaskSim', 'whole_OSInit_execution',
                     'concrete_GOOD_OS_instance', 'CPU_hook_implementations_proved', 'uCOS3_started',
                     'complete_source_hook_entry_inhabited', 'concurrent_reservation_owner_connected',
                     'preallocated_local_cells_required', 'caller_supplied_nine_fresh_blocks_required']:
            self.assertFalse(e[flag], flag)
        for name, expected in e['inputs'].items():
            self.assertEqual(sha(R / name), expected, name)

    def test_prior_files_and_registration_prefix_preserved(self):
        excluded = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject'}
        for name, expected in read('baseline.json').items():
            if name not in excluded:
                self.assertEqual(sha(R / name), expected, name)
        old = R / 'audit/logs/stage350-reserved-call-shared/checkpoint-evidence-manifest.json'
        self.assertEqual(sha(old), (D / 'previous-manifest.sha256').read_text().strip())
        for name, row in json.loads(old.read_text()).items():
            if name not in excluded:
                self.assertEqual(sha(R / name), row['sha256'], name)
        project = (R / '_CoqProject').read_bytes()
        baseline = (D / '_CoqProject.baseline').read_bytes()
        self.assertTrue(project.startswith(baseline + (SOURCES[0] + '\n').encode()))
        self.assertEqual(project.splitlines().count(SOURCES[0].encode()), 1)
