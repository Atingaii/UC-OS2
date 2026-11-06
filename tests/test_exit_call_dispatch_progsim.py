"""源码契约及冻结证据回归；证明有效性由 Coq 和递归 coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage259-exit-call-dispatch-progsim'
PROD = 'certiucos/v293/proofs/V293ExitCallDispatchProgSim.v'
PROBE = 'audit/probes/V293ExitCallDispatchProgSimProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class ExitCallDispatchProgSimTests(unittest.TestCase):
    def test_original_dispatch_and_only_final_simulation_post(self):
        self.assertEqual(sha(D / 'protocol.json'), (D / 'protocol.sha256').read_text().strip())
        src = (R / PROD).read_text()
        common = src.split('Section CallDispatch.', 1)[1].split('Theorem ', 1)[0]
        self.assertNotIn('ProgSim', common)
        for term in ['Some((false,si,cs):localst)', 'V293_sched_read_memory M',
                     'get M(bh,0%Z)=Some(true,oldhigh)', 'V293_ready_select lo hi g<13',
                     'store(Tptr tp)Mh(bo,0%Z)value=Some Mt']:
            self.assertIn(term, common)
        for name in ['V293_exit_call_dispatch_progsim', 'V293_exit_call_same_progsim']:
            body = theorem(src, name)
            self.assertEqual(body.split('Proof.', 1)[0].count('ProgSim'), 2)
            self.assertIn('V293_exit_boundary_dispatch', body)
            self.assertIn('V293_sched_target_then_progsim', body)
        changed = theorem(src, 'V293_exit_call_dispatch_progsim')
        self.assertIn('V293_exit_dispatch_progsim', changed)
        self.assertIn('hpstepstar ph Th cst O Thf cst Of', changed)
        self.assertIn('Some(Vint32 Int.one)', changed)
        self.assertIn('V293_exit_same_progsim', theorem(src, 'V293_exit_call_same_progsim'))
        self.assertNotIn('cstepstar', changed)

    def test_real_pointer_store_and_actual_call_composition(self):
        src = (R / PROD).read_text()
        assign = theorem(src, 'V293_assign_pointer_progsim')
        for term in ['evaladdr e1', 'evalval e2', 'store (Tptr tp)', 'eq_vptr',
                     'V293_store_cstep_unique', 'V293_exit_expr_progsim']:
            self.assertIn(term, assign)
        prefix = theorem(src, 'V293_sched_target_then_progsim')
        for term in ['V293_write_byte_load', 'V293_eval_pointer_array',
                     'V293_sched_call_progsim', 'V293_assign_pointer_progsim',
                     'V293_OSSched_unlocked_prefix', 'V293_OSSched_target_update']:
            self.assertIn(term, prefix)
        self.assertEqual(prefix.split('Proof.', 1)[0].count('ProgSim'), 2)

    def test_independent_same_heap_instance_and_bounded_control(self):
        src = (R / PROBE).read_text()
        table = theorem(src, 'XPtable')
        self.assertIn('RTliteral_loads', table)
        self.assertIn('V293_write_byte_other', table)
        canonical = theorem(src, 'XPscheduled_canonical')
        for term in ['V293_ready_dispatch_call', 'Mskip=CFfinal', 'HalfPermMap.extensionality',
                     'CallFrame', 'V293_full_byte_load_encoding', 'rewrite Canonical in Store']:
            self.assertIn(term, canonical)
        execution = theorem(src, 'XPactual_call_dispatch_simulation')
        self.assertEqual(execution.split('Proof.', 1)[0].count('ProgSim'), 1)
        for term in ['XPscheduled_canonical', 'XPbridge', 'GHrejected',
                     'Int.add Int.mone Int.one=Int.zero', 'V293_ready_storage_switch_step']:
            self.assertIn(term, execution)
        bridge = theorem(src, 'XPbridge')
        for term in ['V293_exit_call_dispatch_progsim', 'SPS CEM enabled ci',
                     'exact XPtable', 'CFinput', 'apply HPschedule', 'apply HPpost']:
            self.assertIn(term, bridge)
        control = theorem(src, 'XPomit_target_rejected')
        for term in ['load Tint8 CFfinal', 'V293_byteval 4', 'Vptr OwnershipWaiting',
                     '~load(Tptr V293_tcb_type)CFfinal', 'Vptr OwnershipReady']:
            self.assertIn(term, control)

    def test_stable_compiles_recursive_trust_and_registration(self):
        roots = []
        stable = read('stable-compiles.json')
        for key, p in [('production', PROD), ('probe', PROBE)]:
            src = (R / p).read_text()
            self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
            result = read(stable[key] + '.json')
            self.assertEqual(result['exit'], 0)
            self.assertEqual(result['initial_source_sha256'], sha(R / p))
            self.assertEqual(result['source_sha256'], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        self.assertNotIn('CertiOS.audit.', (R / PROD).read_text())
        for label in stable['repeat_passes']:
            self.assertEqual(read(label + '.json')['exit'], 0)
        self.assertEqual(len(roots), 9)
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(trust['roots_printed'], 9)
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertEqual(read('build.json')['exit'], 0)
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(PROD), 1)

    def test_chinese_scope_and_unchanged_old_document_tails(self):
        doc = (R / 'audit/STAGE259_EXIT_CALL_DISPATCH_PROGSIM.md').read_text()
        for term in ['不是 `GOOD_OS`', '不是 `WFInt`', 'IE=false', 'ADR-0010',
                     '不是完整 `OS_Sched`', 'K1–K4 未闭合', 'uCOS3 未开始', '未提交／推送',
                     '不是修改后程序的完整执行消融', '整个堆', 'high=88', '最终高层端点及其模拟']:
            self.assertIn(term, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- exit-call-dispatch-progsim-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
        identity = read('source-identity.json')
        self.assertTrue(identity['passed'])
        for p, h in identity['files'].items():
            self.assertEqual(sha(R / p), h)
