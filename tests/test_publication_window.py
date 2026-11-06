"""真实发布窗口及两个抽象map的受限对照，不替代共享不变量集成。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage352-publication-window'
SOURCES = ['certiucos/v293/proofs/V293PublicationWindow.v',
           'audit/probes/V293PublicationWindowProbe.v']
ALLOWED = {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class PublicationWindowTests(unittest.TestCase):
    def test_prospective_single_map_insertion_and_forward_baseline(self):
        p = read('protocol.json')
        self.assertTrue(p['prospective'])
        self.assertEqual((D / 'protocol.sha256').read_text().strip(), sha(D / 'protocol.json'))
        self.assertEqual(set(p['allowed']), ALLOWED)
        self.assertEqual(p['control']['factor'], 'only insert the new ready task into the abstract task map')
        self.assertEqual((p['regression']['tests'], p['regression']['failures'], p['regression']['errors']),
                         (3064, 450, 1))
        self.assertFalse(p['regression']['gate_waived'])
        self.assertTrue(read('baseline-amendment.json')['prospective'])
        a = read('ablation.json')
        self.assertEqual(a['prospective_protocol_sha256'], sha(D / 'protocol.json'))
        self.assertTrue(a['same_physical_window_heap'] and a['old_forward_relation_positive'])
        self.assertFalse(a['all_abstract_maps_rejected'] or a['downstream_hook_or_ready_write_credit'])

    def test_real_window_not_final_state_or_hook_assumption(self):
        s = (R / SOURCES[0]).read_text()
        statement = s.split('Theorem V293_OS_TCBInit_publication_window :', 1)[1].split('Proof.', 1)[0]
        before, after = statement.split(' exists Mf,', 1)
        self.assertNotIn('V293_local_steps', before)
        self.assertNotIn('V293_records_hook_return', s)
        for token in ['V293_OS_TCBInit_priority_to_second_hook', 'V293_tcb_first_hook_cont',
                      'curs(sfexec hook_create', 'load Tint8 Mf(br,0%Z)', 'load Tint8 Mf(br,1%Z)',
                      '~V293_init_priority_table', '~V293_bitmap_tasks', 'V293_ready_set_rows']:
            self.assertIn(token, s)
        self.assertIn('V293_owned_task_records tasks\' ** F', before)
        self.assertNotIn('CertiOS.audit.', s)
        self.assertNotRegex(s, r'Definition V293_(?:ready_rel|init_priority_table|bitmap_tasks)')

    def test_forward_relation_not_conflated_with_reverse_canonical(self):
        s = (R / SOURCES[0]).read_text()
        for name in ['V293_creation_null_slot_not_ready', 'V293_creation_insert_before_ready_rejected',
                     'V293_creation_pointer_before_insert_rejected', 'V293_creation_old_ready_rel_preserved']:
            self.assertRegex(s, r'Lemma ' + name + r'\s*:')
        probe = (R / SOURCES[1]).read_text()
        contrast = probe.split('Theorem PWMapContrast :', 1)[1].split('Proof.', 1)[0]
        for token in ['V293_ready_rel 0 16', '~V293_init_priority_table',
                      '~V293_bitmap_tasks 0 16 CIRUpdated', 'V293_ready_rel 0 24']:
            self.assertIn(token, contrast)
        doc = (R / 'audit/STAGE352_PUBLICATION_WINDOW.md').read_text()
        for token in ['正baseline', '不是新增内核Bug', '第118–130步', '不是**下游ready',
                      '独立的首hook返回入口', 'ADR0009', 'TaskSim']:
            self.assertIn(token, doc)

    def test_closed_literal_prefix_physical_reads_and_nonempty_records(self):
        s = (R / SOURCES[1]).read_text()
        for name in ['PWLiteralEntry', 'PWSpatialEntry', 'PWPrefix', 'PWBetweenOwned',
                     'PWOldReady', 'PWMapContrast', 'PWActualWindow']:
            self.assertRegex(s, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        for token in ['CIRLiteral.', 'V293_TCBInit_prefix_to_record_hook', 'Vptr RCSToken',
                      'V293_OS_TCBInit_publication_window', 'V293_task_records Mf CIRUpdated',
                      '(403%positive,0%Z)', '(403%positive,1%Z)', '(402%positive,0%Z)',
                      '(601%positive,0%Z)', 'Vint32(Int.repr 77)', 'V293_owned_task_records_sound']:
            self.assertIn(token, s)
        self.assertNotIn('V293_records_hook_return', s)
        self.assertNotIn('Fixpoint', s)

    def test_twelve_roots_recursive_trust_and_repeated_compilation(self):
        roots = [Path(p).stem + '.' + n for p in SOURCES for n in
                 re.findall(r"^(?:Lemma|Theorem|Corollary) ([\w']+)\s*:", (R / p).read_text(), re.M)]
        self.assertEqual(len(roots), 12)
        t = read('trust.json')
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 12)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertEqual(set(t['allowed']), ALLOWED)
        self.assertTrue(all(x['exit'] == 0 for x in t['commands']))
        byroot = read('assumptions-by-root.json')
        self.assertEqual(set(byroot), set(roots))
        self.assertTrue(all(set(v) <= ALLOWED for v in byroot.values()))
        for label, source in zip(['window', 'probe'], SOURCES):
            for i in [1, 2]:
                row = read(f'stable-{label}-{i}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / source))
                self.assertEqual(row['source_sha256'], sha(R / source))
            self.assertEqual(read('stable-inputs.json')[source], sha(R / source))
            self.assertEqual(read('trust-inputs.json')[source], sha(R / source))
            self.assertNotRegex((R / source).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')

    def test_fixed_source_identity_and_honest_component_boundaries(self):
        dep = read('source-dependency.json')
        self.assertEqual(dep['target_release'], 'V2.93.01')
        self.assertEqual(dep['target_commit'], '0c4a48e6fbc6e915714e816196619a5481accf0c')
        self.assertEqual(dep['source_sha256'], sha(R / dep['source']))
        self.assertEqual(dep['sha256'], sha(R / dep['component']))
        self.assertFalse(dep['changed_C'] or dep['verified_frontend'])
        lines = (R / dep['source']).read_text().splitlines()
        self.assertIn('OSTCBPrioTbl[prio] = ptcb;', lines[dep['priority_store_line'] - 1])
        self.assertIn('OSRdyGrp', lines[dep['ready_group_line'] - 1])
        self.assertIn('OSRdyTbl', lines[dep['ready_row_line'] - 1])
        e = json.loads((R / 'audit/publication-window-evidence-stage352.json').read_text())
        for flag in ['actual_between_hook_window', 'old_forward_relation_positive',
                     'strong_predicates_unchanged', 'same_physical_window_heap', 'nonempty_records_preserved']:
            self.assertTrue(e[flag], flag)
        for flag in ['full_target_linked', 'whole_OSTaskCreate_TaskSim', 'whole_OSInit_execution',
                     'concrete_GOOD_OS_instance', 'CPU_hook_implementations_proved', 'uCOS3_started',
                     'concurrent_reservation_owner_connected', 'actual_downstream_ready_writes_in_this_step',
                     'all_abstract_maps_rejected']:
            self.assertFalse(e[flag], flag)
        for name, expected in e['inputs'].items():
            self.assertEqual(sha(R / name), expected, name)

    def test_previous_files_and_registration_prefix_preserved(self):
        excluded = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject'}
        for name, expected in read('baseline.json').items():
            if name not in excluded:
                self.assertEqual(sha(R / name), expected, name)
        old = R / 'audit/logs/stage351-creator-shared-return/checkpoint-evidence-manifest.json'
        self.assertEqual(sha(old), (D / 'previous-manifest.sha256').read_text().strip())
        for name, row in json.loads(old.read_text()).items():
            if name not in excluded:
                self.assertEqual(sha(R / name), row['sha256'], name)
        project = (R / '_CoqProject').read_bytes()
        baseline = (D / '_CoqProject.baseline').read_bytes()
        self.assertTrue(project.startswith(baseline + (SOURCES[0] + '\n').encode()))
        self.assertEqual(project.splitlines().count(SOURCES[0].encode()), 1)
