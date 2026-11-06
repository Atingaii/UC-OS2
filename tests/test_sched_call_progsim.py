"""源码契约与证据回归；逻辑检查由 Coq 和递归 coqchk 完成。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage258-sched-call-progsim'
PROD = 'certiucos/v293/proofs/V293SchedCallProgSim.v'
PROBE = 'audit/probes/V293SchedCallProgSimProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class SchedCallProgSimTests(unittest.TestCase):
    def test_original_relation_and_caller_only_post(self):
        self.assertEqual(sha(D / 'protocol.json'), (D / 'protocol.sha256').read_text().strip())
        src = (R / PROD).read_text()
        self.assertNotIn('CertiOS.audit.', src)
        main = theorem(src, 'V293_sched_call_progsim')
        statement = main.split('Proof.', 1)[0]
        self.assertEqual(statement.count('ProgSim'), 2)
        self.assertNotIn('forall b', statement)
        for term in ['Some((false,si,cs):localst)', 'get les t=Some caller',
                     'InOS(SKIP,(kenil,ks))', 'V293_write_byte M bh(V293_ready_select lo hi g)',
                     'get T t=Some(curs(scall f nil)', 'get O curtid=Some(oscurt t)']:
            self.assertIn(term, statement)
        self.assertIn('V293_sched_call_entry_progsim', main)
        self.assertIn('intros b Fresh;eapply V293_sched_body_progsim', main)
        self.assertNotIn('cstepstar', main)

    def test_real_stores_free_successors_and_restore(self):
        src = (R / PROD).read_text()
        assign = theorem(src, 'V293_assign_byte_progsim')
        for term in ['evaladdr e1', 'evalval e2', 'store Tint8',
                     'V293_store_cstep_unique', 'V293_exit_expr_progsim']:
            self.assertIn(term, assign)
        updates = theorem(src, 'V293_sched_updates_progsim')
        self.assertIn('V293_OSSchedNew_row_eval', updates)
        self.assertIn('V293_OSSchedNew_priority_eval', updates)
        self.assertEqual(updates.count('eapply V293_assign_byte_progsim'), 2)
        storage = theorem(src, 'V293_sched_storage')
        for term in ['fresh M b', 'free Tint8 b', 'Some(V293_write_byte M bh priority)',
                     'HalfPermMap.extensionality', 'V293_freeb_removed', 'V293_freeb_outside']:
            self.assertIn(term, storage)
        ret = theorem(src, 'V293_sched_return_progsim')
        self.assertEqual(ret.count('eapply V293_os_family_progsim'), 2)
        for term in ['V293_free_one_successor', 'V293_free_end_successor',
                     'set les t caller', 'sret_step', 'sfreeend_step']:
            self.assertIn(term, ret)
        body = theorem(src, 'V293_sched_body_progsim')
        for term in ['V293_sched_updates_progsim', 'V293_sched_return_progsim',
                     'V293_sched_storage', 'CltEnvMod.get_set_same', 'allocb M b 0%Z 1']:
            self.assertIn(term, body)

    def test_typed_full_execution_and_single_factor_controls(self):
        src = (R / PROBE).read_text()
        self.assertIn('CEtyped_heap nil', theorem(src, 'CFhigh'))
        self.assertIn('V293_ready_loads_sub', theorem(src, 'CFinput'))
        execution = theorem(src, 'CFall_fresh_complete_execution')
        self.assertNotIn('ProgSim', execution)
        for term in ['forall b,fresh CEM b ->', 'cstepstar CGprogram', 'CEactual_prefix_all_fresh',
                     'V293_OSSchedNew_updates_execution', 'CFall_fresh_return']:
            self.assertIn(term, execution)
        self.assertIn('V293_sched_call_progsim', theorem(src, 'CFactual_call'))
        self.assertIn('CFall_fresh_storage', theorem(src, 'CFfresh_choices_same_return'))
        high = theorem(src, 'CFomit_high_rejected')
        self.assertIn('CEM<>CFfinal', high)
        free = theorem(src, 'CFomit_free_rejected')
        for term in ['load Tint8(CFstored b)', 'Some(V293_byteval 4)',
                     'get(CFstored b)(b,0%Z)', 'CFstored b<>CFfinal']:
            self.assertIn(term, free)
        self.assertIn('get CGle 104%Z=None', theorem(src, 'CFall_fresh_return'))

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
        for label in stable['repeat_passes']:
            self.assertEqual(read(label + '.json')['exit'], 0)
        self.assertEqual(len(roots), 17)
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(trust['roots_printed'], 17)
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertEqual(read('build.json')['exit'], 0)
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(PROD), 1)

    def test_chinese_scope_original_inputs_and_document_tails(self):
        doc = (R / 'audit/STAGE258_SCHED_CALL_PROGSIM.md').read_text()
        for term in ['不是 `GOOD_OS`', '不是 `WFInt`', 'IE=false', 'caller 后续模拟',
                     '不是完整 `OS_Sched`', 'ADR-0010', 'K1–K4 未闭合', 'uCOS3 未开始',
                     '未提交／推送', '所有合法新鲜块', '不是修改后程序的完整执行消融']:
            self.assertIn(term, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- sched-call-progsim-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
        identity = read('source-identity.json')
        self.assertTrue(identity['passed'])
        for p, h in identity['files'].items():
            self.assertEqual(sha(R / p), h)
