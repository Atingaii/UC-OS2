"""返回赋值保持原共享就绪资源；完整运行期调用者仍有预留槽缺口。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage349-call-result-frame'
SOURCES = ['certiucos/v293/proofs/V293CallResultShared.v',
           'audit/probes/V293CallResultSharedProbe.v']
ALLOWED = {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class CallResultSharedTests(unittest.TestCase):
    def test_prospective_assignment_only_control(self):
        p = read('protocol.json')
        self.assertTrue(p['prospective'])
        self.assertEqual((D / 'protocol.sha256').read_text().strip(), sha(D / 'protocol.json'))
        self.assertEqual(set(p['allowed']), ALLOWED)
        self.assertEqual(p['control']['factor'], 'omit only the caller return assignment')
        self.assertIn('same complete shared-ready frame', p['control']['fixed'])
        self.assertEqual((p['regression']['tests'], p['regression']['failures'], p['regression']['errors']),
                         (3043, 449, 1))
        self.assertFalse(p['regression']['gate_waived'])
        a = read('ablation.json')
        self.assertEqual(a['prospective_protocol_sha256'], sha(D / 'protocol.json'))
        self.assertTrue(a['positive_and_negative_same_heap'] and a['original_shared_ready_frame_preserved'])
        self.assertFalse(a['early_rejection_used'] or a['downstream_hook_or_commit_credit'])

    def test_real_entry_to_assignment_not_execution_oracle(self):
        s = (R / SOURCES[0]).read_text()
        pre, post = s.split('Theorem V293_OS_TCBInit_call_assign_shared_under_hooks :', 1)[1].split(" exists Mf clientM',", 1)
        self.assertEqual(pre.count('V293_records_hook_return'), 2)
        self.assertIn('let retks:=kassignr(evar err)Tint8 ks in', pre)
        self.assertIn('get caller err=Some(berr,Tint8)', pre)
        self.assertIn('In b blocks -> fresh M b', pre)
        self.assertIn('nth p entries Vnull=Vnull', pre)
        for token in ['V293_local_steps', 'hpstep', 'V293_ready_payload', 'V293_tcb_prefix_inputs']:
            self.assertNotIn(token, pre)
        self.assertIn('(curs(sskip None),(kenil,ks)) ((ge,caller,Mf)', post)
        self.assertIn('V293_rdy_raw_cells(returned++before++((berr,0%Z),Tint8,Vint32 Int.zero)::afterframe)Atrue', post)
        self.assertNotIn('CertiOS.audit.', s)

    def test_same_return_heap_keeps_physical_frame(self):
        s = (R / SOURCES[0]).read_text()
        self.assertEqual(s.count('destruct(V293_OS_TCBInit_ready_return_under_hooks'), 1)
        for token in ['as(Mr&Body&Final&Freed&NewCanonical&Payload)',
                      'ge caller Mr ir aux O op hpc A T',
                      'V293_return_ready_shared_keep with(O:=O)',
                      'V293_return_ready_current_keep;[exact CurrentGlobal |exact Physical]',
                      'err berr olderr P ks ge caller Mr',
                      'apply V293_csteps_local. exact Assign.',
                      'V293_init_ready_physical_empty', 'V293_return_raw_abstract_reset in Frame']:
            self.assertIn(token, s)
        reset = s.split('Lemma V293_return_raw_abstract_reset :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('V293_rdy_raw_cells cells Atrue', reset)
        self.assertIn('exists mc. exists mr.', reset)
        self.assertNotIn('V293_init_raw_frame_drop', s)
        self.assertNotIn('Definition V293_ready_core', s)

    def test_closed_assignment_and_reserved_slot_boundary(self):
        s = (R / SOURCES[1]).read_text()
        for name in ['CRSliteral_core', 'CRSfresh', 'CRSreturn_entry',
                     'CRSAssignmentContrast', 'CRSReservedSlotBoundary']:
            self.assertRegex(s, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        for token in ['RTliteral_spatial OwnershipReady', 'V293_tick_allocate_frame',
                      'V293_tick_raw_slot_update', 'V293_return_assign_shared',
                      'load Tint8 M(350%positive,0%Z)<>Some(Vint32 Int.zero)',
                      'Some(Vptr(reserve,Int.zero))', 'V293_tcb_init_read Null']:
            self.assertIn(token, s)
        self.assertNotIn('V293_records_hook_return', s)
        self.assertNotIn('Fixpoint OwnershipCellsMemory', s)
        doc = (R / 'audit/STAGE349_CALL_RESULT_FRAME.md').read_text()
        for bound in ['同一个`Mr`', '独立的返回现场', '不能直接与真实运行期预留槽前缀拼接',
                      '两个原CPU hook契约', 'clientM', 'TaskSim']:
            self.assertIn(bound, doc)

    def test_ten_roots_recursive_trust_and_repeated_compilation(self):
        roots = [Path(p).stem + '.' + n for p in SOURCES for n in
                 re.findall(r"^(?:Lemma|Theorem|Corollary) ([\w']+)\s*:", (R / p).read_text(), re.M)]
        t = read('trust.json')
        self.assertEqual(len(roots), 10)
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 10)
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

    def test_source_identity_and_no_whole_target_credit(self):
        dep = read('source-dependency.json')
        self.assertEqual(dep['target_release'], 'V2.93.01')
        self.assertEqual(dep['target_commit'], '0c4a48e6fbc6e915714e816196619a5481accf0c')
        self.assertEqual(dep['source_sha256'], sha(R / dep['source']))
        self.assertEqual(dep['caller_source_sha256'], sha(R / dep['caller_source']))
        self.assertEqual(dep['sha256'], sha(R / dep['component']))
        self.assertFalse(dep['runtime_reserved_slot_connected'] or dep['changed_C'] or dep['verified_frontend'])
        e = json.loads((R / 'audit/call-result-frame-evidence-stage349.json').read_text())
        self.assertTrue(e['real_caller_return_assignment_constructed'] and e['caller_physical_frame_preserved'])
        for flag in ['full_target_linked', 'whole_OSTaskCreate_TaskSim', 'whole_OSInit_execution',
                     'concrete_GOOD_OS_instance', 'CPU_hook_implementations_proved', 'uCOS3_started',
                     'runtime_reserved_slot_connected', 'complete_source_hook_entry_inhabited']:
            self.assertFalse(e[flag], flag)
        for name, expected in e['inputs'].items():
            self.assertEqual(sha(R / name), expected, name)

    def test_old_sources_tests_evidence_and_registration_prefix(self):
        excluded = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject'}
        for name, expected in read('baseline.json').items():
            if name not in excluded:
                self.assertEqual(sha(R / name), expected, name)
        old = R / 'audit/logs/stage348-call-ready-commit/checkpoint-evidence-manifest.json'
        self.assertEqual(sha(old), (D / 'previous-manifest.sha256').read_text().strip())
        for name, row in json.loads(old.read_text()).items():
            if name not in excluded:
                self.assertEqual(sha(R / name), row['sha256'], name)
        project = (R / '_CoqProject').read_bytes()
        baseline = (D / '_CoqProject.baseline').read_bytes()
        self.assertTrue(project.startswith(baseline + (SOURCES[0] + '\n').encode()))
        self.assertEqual(project.splitlines().count(SOURCES[0].encode()), 1)
