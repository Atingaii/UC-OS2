"""接口形状与冻结证据回归；证明有效性另由 Coq/coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage262-exit-quiet-call-progsim'
PROD = 'certiucos/v293/proofs/V293ExitQuietCallProgSim.v'
PROBE = 'audit/probes/V293ExitQuietCallProgSimProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class ExitQuietCallProgSimTests(unittest.TestCase):
    def test_complete_function_only_final_caller_simulation(self):
        src = (R / PROD).read_text()
        body = theorem(src, 'V293_exit_quiet_call_progsim')
        self.assertEqual(body.split('Proof.', 1)[0].count('ProgSim'), 2)
        for term in ['po f=Some(V293_exit_boundary_function', 'run=1 ->saved<>nesting',
                     'if Nat.eqb run 1 then V293_exit_decrement_memory M bn n else M',
                     'V293_success_scheduler_storage', 'V293_exit_body_progsim',
                     'V293_saved_free_decrement', 'rewrite Restore;exact Post']:
            self.assertIn(term, body)
        whole = theorem(src, 'V293_exit_body_progsim')
        self.assertEqual(whole.split('Proof.', 1)[0].count('ProgSim'), 2)
        for term in ['V293_assign_word_progsim', 'V293_exit_ifthen_progsim',
                     'V293_exit_quiet_return_progsim', 'V293_one_local_return_progsim',
                     '(sassign(evar saved)(econst32 Int.zero))']:
            self.assertIn(term, whole)

    def test_all_fresh_successors_and_original_entry_classification(self):
        src = (R / PROD).read_text()
        entry = theorem(src, 'V293_saved_exec_entry_progsim')
        for term in ['forall b,fresh M b ->', 'memory_has_fresh_block M',
                     'V293_saved_exec_successor', 'V293_saved_alloc_successor',
                     'V293_saved_alloc_step', 'V293_alloc_end_successor',
                     'V293_os_family_progsim']:
            self.assertIn(term, entry)
        bridge = theorem(src, 'V293_saved_call_entry_progsim')
        for term in ['entry=sfexec f nil nil', 'entry=scall f nil /\\ InOS',
                     'V293_context_inos', 'V293_call_nil_successor', 'V293_saved_exec_entry_progsim']:
            self.assertIn(term, bridge)
        probe = theorem((R / PROBE).read_text(), 'QPcomplete_quiet_simulation')
        self.assertEqual(probe.split('Proof.', 1)[0].count('ProgSim'), 1)
        for term in ['(entry:=sfexec 114%Z nil nil)', '(ks:=kstop)', 'SPterminal',
                     'V293_exit_quiet_call_progsim']:
            self.assertIn(term, probe)

    def test_physical_saved_initialization_and_allocation_independent_free(self):
        src = (R / PROD).read_text()
        commute = theorem(src, 'V293_saved_free_write_byte')
        for term in ['induction count', 'bn<>bs', 'HalfPermMap.extensionality']:
            self.assertIn(term, commute)
        probe = (R / PROBE).read_text()
        typed = theorem(probe, 'QPtyped')
        for term in ['V293_tick_allocate_frame', 'V293_tick_raw_slot_update', 'CPtyped_updated',
                     'CGstate OwnershipWaiting(QPmemory br 2 run)cs', 'exact After']:
            self.assertIn(term, typed)
        release = theorem(probe, 'QPsaved_choice_independent')
        self.assertNotIn('ProgSim', release.split('Proof.', 1)[0])
        for term in ['fresh(QPmemory br 2 run)bs', 'store Tint32(allocb',
                     'Some(QPfinal br run)', 'V293_saved_free_decrement']:
            self.assertIn(term, release)
        self.assertIn('memory_has_fresh_block', theorem(probe, 'QPnonvacuous'))

    def test_running_single_byte_control_at_actual_expression_and_full_simulation(self):
        src = (R / PROBE).read_text()
        pair = theorem(src, 'QPstopped_and_running')
        self.assertEqual(pair.split('Proof.', 1)[0].count('ProgSim'), 2)
        self.assertIn('apply QPcomplete_quiet_simulation', pair)
        only = theorem(src, 'QPrunning_only_changed')
        self.assertIn('a<>(br,0%Z)', only)
        self.assertIn('get(QPmemory br 2 0)a=get(QPmemory br 2 1)a', only)
        self.assertIn('V293_success_global_byte_eq', theorem(src, 'QPguard_control'))
        changed = theorem(src, 'QPguard_changes_return')
        for term in ['QPfinal br 0', 'QPfinal br 1', 'Some(V293_byteval 2)', 'Some(V293_byteval 1)']:
            self.assertIn(term, changed)
        self.assertIn('V293_byteval 0<>V293_byteval 1', theorem(src, 'QPrunning_flag_changes'))

    def test_stable_compiles_trust_identity_and_bounded_documentation(self):
        for name in ['protocol', 'protocol-amendment']:
            self.assertEqual(sha(D / (name + '.json')), (D / (name + '.sha256')).read_text().strip())
        stable = read('stable-compiles.json')
        roots = []
        for key, p in [('production', PROD), ('probe', PROBE)]:
            src = (R / p).read_text()
            self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
            row = read(stable[key] + '.json')
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], sha(R / p))
            self.assertEqual(row['source_sha256'], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        self.assertNotIn('CertiOS.audit.', (R / PROD).read_text())
        for label in stable['repeat_passes']:
            self.assertEqual(read(label + '.json')['exit'], 0)
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']),
                             {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertEqual(read('build.json')['exit'], 0)
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(PROD), 1)
        doc = (R / 'audit/STAGE262_EXIT_QUIET_CALL_PROGSIM.md').read_text()
        for term in ['不是 `GOOD_OS`', '不是 `WFInt`', 'IE=false', 'ADR-0010',
                     'K1–K4 未闭合', 'uCOS3 未开始', '未提交／推送', 'high=88',
                     '最终 caller 端点模拟', 'protocol-amendment.json',
                     '没有另建完整有限返回 trace 定理', 'typed 结论用既有 CG 环境']:
            self.assertIn(term, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- exit-quiet-call-progsim-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h)
