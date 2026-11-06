"""局部模拟与证据回归；这些静态断言不替代 Coq 内核检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage280-exit-changed-tasksim'
PROD = 'certiucos/v293/proofs/V293ExitChangedTaskSim.v'
PROBE = 'audit/probes/V293ExitChangedTaskSimProbe.v'
SOURCES = [PROD, PROBE]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def body(s, name):
    return s.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class ExitChangedTaskSimTests(unittest.TestCase):
    def test_identity_and_registration(self):
        baseline = read('baseline.json')['files']
        self.assertEqual(len(baseline), 1639)
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
        self.assertNotRegex(s, r'(?m)^Definition ')
        self.assertEqual(re.findall(r'^Theorem (\w+)\s*:', s, re.M), ['V293_exit_changed_TaskSim'])
        main = body(s, 'V293_exit_changed_TaskSim')
        stmt = main.split('Proof.', 1)[0]
        self.assertEqual(stmt.count('TaskSim('), 1)
        for bad in ['store Tint32', 'ProgSim', 'V293_global_steps', 'Int.max_unsigned', 'evalval', 'V293_current_guard']:
            self.assertNotIn(bad, stmt)
        for term in ['nh<256 ->nc<256 ->nh<>nc', '|=Owned c', 'top::ci',
                     'V293_highest_ready tasks next', 'RDYINV G t **LINV V293_shared_li t nil',
                     'V293_owned_record_cell_update (bk,0%Z) Tint32',
                     'V293_changed_owned_local;exact Held', 'V293_changed_owned_local;exact AfterOwned',
                     'V293_handoff_TaskSim', 'CounterStorage', 'Int.add c Int.one']:
            self.assertIn(term, main)

    def test_stepwise_frame_and_store_chain(self):
        s = (R / PROD).read_text()
        frame = body(s, 'V293_changed_estep_frame')
        for term in ['join M Mframe Mall', 'inversion Step', 'evaltype_mono', 'evalval_mono', 'load_mono']:
            self.assertIn(term, frame)
        expr = body(s, 'V293_changed_expr_TaskSim')
        for term in ['induction Steps', 'estep_mem_same', 'V293_changed_pure_TaskSim', 'V293_changed_estep_frame']:
            self.assertIn(term, expr)
        pure = body(s, 'V293_changed_pure_TaskSim')
        for term in ['forall Mf Mall', 'V293_invariant_cstep_TaskSim', 'cstep_idmove_deter']:
            self.assertIn(term, pure)
        count = body(s, 'V293_changed_increment_TaskSim')
        for term in ['V293_ready_counter_eval', 'V293_changed_expr_TaskSim', 'sassignend_step',
                     'store_mono', 'join_store_join', 'V293_store_cstep_unique', 'exact After']:
            self.assertIn(term, count)
        tail = body(s, 'V293_changed_tail_TaskSim')
        for term in ['V293_changed_if_TaskSim', 'V293_changed_increment_TaskSim', 'sseq_step', 'sskip_step']:
            self.assertIn(term, tail)

    def test_same_call_partition_controls_and_limits(self):
        s = (R / PROBE).read_text()
        actual = body(s, 'ECactual_changed')
        for term in ['ECfixed_prefix', 'V293_local_steps_global', 'FTenter', 'ECpartition', 'Int.mone']:
            self.assertIn(term, actual)
        partition = body(s, 'ECpartition')
        for term in ['sat_split', 'V293_shared_no_abstract_frame', 'V293_exit_changed_TaskSim', 'exact Owned']:
            self.assertIn(term, partition)
        self.assertEqual(body(s, 'ECnonvacuous').count('memory_has_fresh_block'), 2)
        control = body(s, 'ECactual_wrap_and_ablation')
        for term in ['ECfixed_prefix', 'V293_exit_boundary_tail', 'ECwithout_increment',
                     'Int.add Int.mone Int.one=Int.zero', 'load Tint32 Mf', 'load Tint32 M']:
            self.assertIn(term, control)
        self.assertIn('V293_OSSched_byte_comparison_eval', body(s, 'ECequal_priorities'))
        self.assertIn('Nat.eqb_refl', body(s, 'ECequal_priorities'))
        self.assertIn('sviff_step', body(s, 'ECequal_no_count'))
        doc = (R / 'audit/STAGE280_EXIT_CHANGED_TASKSIM.md').read_text()
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
        self.assertEqual(len(roots), 17)
        t = read('trust.json')
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 17)
        self.assertEqual(list(read('assumptions-by-root.json')), roots)
        self.assertTrue(all(row['exit'] == 0 for row in t['commands']))
        self.assertLessEqual(set(t['assumptions']), {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
