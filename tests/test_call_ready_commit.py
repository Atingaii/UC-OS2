"""真实sfexec入口的条件式资源连接；入口负控不替代下游验证。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage348-call-ready-commit'
SOURCES = ['certiucos/v293/proofs/V293CallReadyCommit.v',
           'audit/probes/V293CallReadyCommitProbe.v']
ALLOWED = {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class CallReadyCommitTests(unittest.TestCase):
    def test_prospective_protocol_and_bounded_factor(self):
        p = read('protocol.json')
        self.assertEqual((D / 'protocol.sha256').read_text().strip(), sha(D / 'protocol.json'))
        self.assertTrue(p['prospective'])
        self.assertEqual(set(p['allowed']), ALLOWED)
        self.assertEqual(p['control']['factor'], 'only remove OS_TCBInit function binding from the program')
        self.assertIn('same physical initial heap', p['control']['fixed'])
        self.assertIn('not evidence about downstream', p['control']['limits'])
        self.assertEqual(p['regression']['tests'], 3036)
        self.assertFalse(p['regression']['gate_waived'])

    def test_entry_has_no_allocated_local_or_execution_oracle(self):
        s = (R / SOURCES[0]).read_text()
        pre, post = s.split('Theorem V293_OS_TCBInit_call_shared_return_under_hooks :', 1)[1].split(" exists Mf clientM',", 1)
        self.assertEqual(pre.count('V293_records_hook_return'), 2)
        self.assertIn('P f=Some(V293_TCBInit_function hi hc)', pre)
        self.assertIn('In b blocks -> fresh M b', pre)
        for forbidden in ['V293_local_steps', 'hpstep', 'V293_ready_payload',
                          'V293_tcb_prefix_inputs', 'V293_tcb_function_cells']:
            self.assertNotIn(forbidden, pre)
        self.assertIn('(ge,caller,M,ir,aux,O,op) |= V293_rdy_raw_cells', pre)
        self.assertIn('curs(sfexec f [options;ext;size;identity;bottom;top;V293_byteval p]', post)
        self.assertNotIn('CertiOS.audit.', s)
        self.assertNotIn('Definition V293_ready_core', s)

    def test_prologue_and_original_return_share_actual_memories(self):
        s = (R / SOURCES[0]).read_text()
        for token in ['V293_tcb_call_prologue_records tasks P ks ge caller M',
                      'as (Mi&Prologue&Allocated)', '(ge,le,Mi,ir,aux,O,op)',
                      'V293_OS_TCBInit_shared_return_under_hooks entries tasks lo0 hi0 P f hi hc caller ks ge Mi',
                      "as (Mf&clientM'&Body&Commit&Read&Shared&Core&Stale)",
                      'V293_local_trans;[exact Prologue |exact Body]',
                      '(ge,caller,Mf,ir,aux,set O abstcblsid', 'V293_ready_core br bg table']:
            self.assertIn(token, s)
        self.assertNotIn('eapply hpcrt_step', s)  # 复用原创建桥，不重复造规则。

    def test_closed_same_input_binding_contrast_is_entry_only(self):
        s = (R / SOURCES[1]).read_text()
        for name in ['CRCBindingOnly', 'CRCInitialLocalsAbsent', 'CRCActualPrefix', 'CRCMissingEntryRejected']:
            self.assertIn('Theorem ' + name + ' :', s)
        self.assertIn('f<>900%Z -> CRCProgram true f=CRCProgram false f', s)
        self.assertEqual(s.count('CallGE,CallCaller,CallMemory CallCells'), 3)
        self.assertIn('apply CallPrefix. reflexivity.', s)
        self.assertIn('apply V293_tcb_missing_call_cannot_return. reflexivity.', s)
        self.assertNotIn('V293_records_hook_return', s)
        self.assertNotIn('Fixpoint CallMemory', s)
        doc = (R / 'audit/STAGE348_CALL_READY_COMMIT.md').read_text()
        for bound in ['没有构造满足两个hook契约的完整启动实例', '负向在入口就停止',
                      '同一个Mf', 'TaskSim', 'clientM', '实参表达式求值']:
            self.assertIn(bound, doc)

    def test_six_roots_repeated_compile_and_recursive_trust(self):
        roots = [Path(p).stem + '.' + n for p in SOURCES for n in
                 re.findall(r"^(?:Lemma|Theorem|Corollary) ([\w']+)\s*:", (R / p).read_text(), re.M)]
        t = read('trust.json')
        self.assertEqual(len(roots), 6)
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 6)
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

    def test_unchanged_source_identity_and_not_whole_target(self):
        t = read('source-dependency.json')
        self.assertEqual(t['target_release'], 'V2.93.01')
        self.assertEqual(t['target_commit'], '0c4a48e6fbc6e915714e816196619a5481accf0c')
        self.assertEqual(t['source_sha256'], sha(R / t['source']))
        self.assertEqual(t['sha256'], sha(R / t['component']))
        self.assertFalse(t['changed_C'] or t['verified_frontend'] or t['CPU_hook_implementations_proved'])
        e = json.loads((R / 'audit/call-ready-commit-evidence-stage348.json').read_text())
        for flag in ['full_target_linked', 'whole_OSTaskCreate_TaskSim', 'whole_OSInit_execution',
                     'concrete_GOOD_OS_instance', 'CPU_hook_implementations_proved', 'uCOS3_started']:
            self.assertFalse(e[flag], flag)
        for name, expected in e['inputs'].items():
            self.assertEqual(sha(R / name), expected, name)

    def test_prior_sources_tests_and_frozen_evidence_preserved(self):
        excluded = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject'}
        for name, expected in read('baseline.json').items():
            if name not in excluded:
                self.assertEqual(sha(R / name), expected, name)
        old = R / 'audit/logs/stage347-init-ready-commit/checkpoint-evidence-manifest.json'
        self.assertEqual(sha(old), (D / 'previous-manifest.sha256').read_text().strip())
        for name, row in json.loads(old.read_text()).items():
            if name not in excluded:
                self.assertEqual(sha(R / name), row['sha256'], name)
        project = (R / '_CoqProject').read_bytes()
        baseline = (D / '_CoqProject.baseline').read_bytes()
        self.assertEqual(project, baseline + (SOURCES[0] + '\n').encode())
