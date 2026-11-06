"""物理预留槽沿真实初始化／发布返回原强共享谓词，不替代并发整函数。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage350-reserved-call-shared'
SOURCES = ['certiucos/v293/proofs/V293ReservedCallShared.v',
           'audit/probes/V293ReservedCallSharedProbe.v']
ALLOWED = {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class ReservedCallSharedTests(unittest.TestCase):
    def test_prospective_publication_only_control(self):
        p = read('protocol.json')
        self.assertTrue(p['prospective'])
        self.assertEqual((D / 'protocol.sha256').read_text().strip(), sha(D / 'protocol.json'))
        self.assertEqual(set(p['allowed']), ALLOWED)
        self.assertEqual(p['control']['factor'], 'omit only the priority-slot publication write')
        self.assertIn('same physical pre-publication heap', p['control']['fixed'])
        self.assertEqual((p['regression']['tests'], p['regression']['failures'], p['regression']['errors']),
                         (3050, 450, 1))
        self.assertFalse(p['regression']['gate_waived'])
        a = read('ablation.json')
        self.assertEqual(a['prospective_protocol_sha256'], sha(D / 'protocol.json'))
        self.assertTrue(a['positive_and_negative_same_heap'] and a['nonempty_records_preserved'])
        self.assertFalse(a['early_rejection_used'] or a['downstream_hook_or_commit_credit'])

    def test_reserved_entry_is_not_a_null_physical_slot(self):
        s = (R / SOURCES[0]).read_text()
        pre, post = s.split('Theorem V293_OS_TCBInit_reserved_call_assign_shared_under_hooks :', 1)[1].split(" exists Mf clientM',", 1)
        self.assertEqual(pre.count('V293_records_hook_return'), 2)
        self.assertIn('let retks:=kassignr(evar err)Tint8 ks in', pre)
        self.assertIn('(bt,Int.repr base)<>(reserve,Int.zero)', pre)
        self.assertIn('In b blocks -> fresh M b', pre)
        self.assertIn('nth p entries Vnull=Vnull', pre)
        self.assertIn('Tptr V293_tcb_type,Vptr(reserve,Int.zero))::tail', pre)
        self.assertIn('options next (Vptr(reserve,Int.zero)) tail', pre)
        self.assertNotIn('options next Vnull tail', pre)
        for token in ['V293_local_steps', 'hpstep', 'V293_ready_payload', 'V293_tcb_prefix_inputs']:
            self.assertNotIn(token, pre)
        self.assertIn('(curs(sskip None),(kenil,ks)) ((ge,caller,Mf)', post)
        self.assertIn('V293_rdy_raw_cells(returned++before++((berr,0%Z),Tint8,Vint32 Int.zero)::afterframe)Atrue', post)
        self.assertNotIn('CertiOS.audit.', s)

    def test_original_arbitrary_slot_trace_and_strong_predicates(self):
        s = (R / SOURCES[0]).read_text()
        for token in ['V293_OS_TCBInit_prefix_return_records_under_hooks tasks',
                      'options pc next old slot prev back extra', 'V293_priority_reassemble_frame',
                      'V293_init_ready_insert', 'V293_init_ready_pack',
                      'as(Mr&Body&Final&Freed&NewCanonical&Payload)',
                      'V293_init_ready_create_commit', 'V293_return_ready_shared_keep with(O:=O)',
                      'err berr olderr P ks ge caller Mr', 'exact Assign.']:
            self.assertIn(token, s)
        self.assertEqual(s.count('destruct(V293_OS_TCBInit_prefix_return_records_under_hooks'), 1)
        self.assertEqual(s.count('destruct(V293_OS_TCBInit_slot_ready_return_under_hooks'), 1)
        self.assertNotIn('destruct(V293_OS_TCBInit_ready_return_under_hooks', s)
        self.assertNotIn('V293_init_raw_frame_drop', s)
        self.assertNotRegex(s, r'Definition V293_(?:ready|shared|init_priority)')

    def test_real_prefix_and_independent_publication_contrast(self):
        s = (R / SOURCES[1]).read_text()
        for name in ['RCSliteral_entry', 'RCSspatial_entry', 'RCSReservedPrefix',
                     'RCSUpdatedCanonical', 'RCSBetweenOwned', 'RCSAfterTable', 'RCSPublicationContrast']:
            self.assertRegex(s, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        for token in ['CIRLiteral.', 'V293_TCBInit_prefix_to_record_hook',
                      'V293_OS_TCBInit_priority_to_second_hook', 'Some(Vptr RCSToken)',
                      'V293_full_priority_table_loads', '~ (CIREntryState M |= RCSJoint)',
                      'V293_byteval 11', 'Vint32(Int.repr 77)']:
            self.assertIn(token, s)
        self.assertNotIn('V293_records_hook_return', s)
        self.assertNotIn('Fixpoint', s)
        doc = (R / 'audit/STAGE350_RESERVED_CALL_SHARED.md').read_text()
        for bound in ['逻辑影子', '物理预留槽', '两个原CPU hook契约',
                      'ADR0009', '独立的第一hook返回现场', '已经求值', 'TaskSim', '同一个`Mr`']:
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

    def test_frozen_source_and_honest_credit_boundaries(self):
        dep = read('source-dependency.json')
        self.assertEqual(dep['target_release'], 'V2.93.01')
        self.assertEqual(dep['target_commit'], '0c4a48e6fbc6e915714e816196619a5481accf0c')
        self.assertEqual(dep['source_sha256'], sha(R / dep['source']))
        self.assertEqual(dep['caller_source_sha256'], sha(R / dep['caller_source']))
        self.assertEqual(dep['sha256'], sha(R / dep['component']))
        self.assertTrue(dep['physical_reserved_slot_accepted'])
        self.assertFalse(dep['runtime_reserved_slot_connected'] or dep['changed_C'] or dep['verified_frontend'])
        e = json.loads((R / 'audit/reserved-call-shared-evidence-stage350.json').read_text())
        self.assertTrue(e['physical_reserved_slot_accepted'] and e['real_caller_return_assignment_constructed'])
        self.assertTrue(e['caller_physical_frame_preserved'] and e['strong_ready_predicate_unchanged'])
        for flag in ['full_target_linked', 'whole_OSTaskCreate_TaskSim', 'whole_OSInit_execution',
                     'concrete_GOOD_OS_instance', 'CPU_hook_implementations_proved', 'uCOS3_started',
                     'runtime_reserved_slot_connected', 'complete_source_hook_entry_inhabited',
                     'concurrent_reservation_owner_connected', 'caller_argument_evaluation_composed']:
            self.assertFalse(e[flag], flag)
        for name, expected in e['inputs'].items():
            self.assertEqual(sha(R / name), expected, name)

    def test_prior_files_and_registration_prefix_preserved(self):
        excluded = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject'}
        for name, expected in read('baseline.json').items():
            if name not in excluded:
                self.assertEqual(sha(R / name), expected, name)
        old = R / 'audit/logs/stage349-call-result-frame/checkpoint-evidence-manifest.json'
        self.assertEqual(sha(old), (D / 'previous-manifest.sha256').read_text().strip())
        for name, row in json.loads(old.read_text()).items():
            if name not in excluded:
                self.assertEqual(sha(R / name), row['sha256'], name)
        project = (R / '_CoqProject').read_bytes()
        baseline = (D / '_CoqProject.baseline').read_bytes()
        self.assertTrue(project.startswith(baseline + (SOURCES[0] + '\n').encode()))
        self.assertEqual(project.splitlines().count(SOURCES[0].encode()), 1)
