"""局部模拟与证据回归；这些静态断言不替代 Coq 内核检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage281-target-tasksim'
PROD = 'certiucos/v293/proofs/V293ExitTargetTaskSim.v'
PROBE = 'audit/probes/V293ExitTargetTaskSimProbe.v'
SOURCES = [PROD, PROBE]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def body(s, name):
    return s.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class ExitTargetTaskSimTests(unittest.TestCase):
    def test_identity_and_registration(self):
        baseline = read('baseline.json')['files']
        self.assertEqual(len(baseline), 1643)
        for p, h in baseline.items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d', '.lia.cache', '.nia.cache']:
                self.assertEqual(sha(R / p), h, p)
        project = (R / '_CoqProject').read_text().splitlines()
        self.assertEqual(project.count(PROD), 1)
        self.assertNotIn(PROBE, project)
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h, p)
        lines = (R / 'csrc/upstream/v2.93.01/checkout/Source/os_core.c').read_text().splitlines()
        for n, anchor in read('source-identity.json')['line_anchors'].items():
            self.assertEqual(lines[int(n) - 1].strip(), anchor)
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])

    def test_public_resource_interface(self):
        s = (R / PROD).read_text()
        self.assertNotIn('CertiOS.audit', s)
        self.assertEqual(re.findall(r'^Theorem (\w+)\s*:', s, re.M), ['V293_exit_target_TaskSim'])
        main = body(s, 'V293_exit_target_TaskSim')
        stmt = main.split('Proof.', 1)[0]
        self.assertEqual(stmt.count('TaskSim('), 1)
        for bad in ['store(', 'ProgSim', 'cstepstar', 'evalval', 'V293_current_guard']:
            self.assertNotIn(bad, stmt)
        for term in ['V293_current_task tasks next nh', '|=TargetOwned oldtarget c',
                     'V293_highest_ready tasks next', 'RDYINV G t **LINV V293_shared_li t nil',
                     'V293_target_owned_pointer', 'V293_owned_record_cell_update (bo,0%Z)',
                     'V293_target_owned_local;exact Held', 'V293_target_owned_local;exact AfterOwned',
                     'V293_exit_changed_TaskSim']:
            self.assertIn(term, main)

    def test_real_array_read_and_frame_safe_store(self):
        s = (R / PROD).read_text()
        pointer = body(s, 'V293_target_owned_pointer')
        for term in ['V293_ready_switch_sound', 'V293_priority_repr_injective',
                     'assert(ts=tasks)', 'subst p', '4*Z.of_nat nh']:
            self.assertIn(term, pointer)
        store = body(s, 'V293_target_assignment_TaskSim')
        for term in ['V293_eval_pointer_array', 'V293_changed_expr_TaskSim',
                     'V293_changed_pure_TaskSim', 'V293_invariant_cstep_TaskSim',
                     'store_mono', 'join_store_join', 'V293_store_cstep_unique',
                     'forall', 'CurLINV li t', 'sassignend_step']:
            self.assertIn(term, store)

    def test_actual_predecessor_same_heap_ablation_and_limits(self):
        s = (R / PROBE).read_text()
        prefix = body(s, 'ETboundary_prefix')
        self.assertIn('exact Call', prefix)
        self.assertNotIn('exact Exec', prefix)
        self.assertIn('exists Mskip', prefix)
        actual = body(s, 'ETactual_target')
        for term in ['ETfixed_prefix', 'V293_local_steps_global', 'FTenter', 'ETpartition', 'Int.mone']:
            self.assertIn(term, actual)
        for term in ['sat_split', 'V293_shared_no_abstract_frame', 'V293_exit_target_TaskSim', 'exact Owned']:
            self.assertIn(term, body(s, 'ETpartition'))
        self.assertEqual(body(s, 'ETnonvacuous').count('memory_has_fresh_block'), 2)
        control = body(s, 'ETactual_target_ablation')
        for term in ['ETfixed_prefix', 'V293_assign_pointer_execution', 'curs ETassign',
                     'curs ECbranch', 'OwnershipWaiting<>OwnershipReady',
                     'load(Tptr V293_tcb_type)M(93%positive',
                     'load(Tptr V293_tcb_type)Mf(93%positive',
                     'load Tint32 M(95%positive', 'load Tint32 Mf(95%positive',
                     'V293_storebytes_outside']:
            self.assertIn(term, control)
        stmt = control.split('Proof.', 1)[0]
        self.assertIn('(SKIP,(kenil,kseq ECbranch', stmt)
        self.assertIn('(QPge br,V293_cpu_lenv 120%Z bs,M)', stmt)
        doc = (R / 'audit/STAGE281_TARGET_TASKSIM.md').read_text()
        for term in ['不是完整调用入口 TaskSim', 'GOOD_OS 未闭合', 'uCOS3 未开始',
                     'saved(bs) 私有', 'saved98 与 RCframe 外部', '局部后缀消融',
                     '没有证明列表置换下 Inv 的等价', 'cache=4', 'ADR-0010', 'si=nil']:
            self.assertIn(term, doc)

    def test_stable_compiles_and_recursive_kernel(self):
        roots = []
        stable = read('stable-compiles.json')
        self.assertEqual(list(stable), SOURCES)
        for p in SOURCES:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            names = re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', s, re.M)
            roots += [Path(p).stem + '.' + n for n in names]
            self.assertEqual(stable[p]['roots'], names)
            self.assertEqual(stable[p]['sha256'], sha(R / p))
            self.assertEqual(len(stable[p]['runs']), 2)
            for row in stable[p]['runs']:
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
                self.assertEqual(row['source_sha256'], sha(R / p))
        self.assertEqual(len(roots), 11)
        t = read('trust.json')
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 11)
        self.assertEqual(list(read('assumptions-by-root.json')), roots)
        self.assertTrue(all(row['exit'] == 0 for row in t['commands']))
        self.assertLessEqual(set(t['assumptions']), {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
