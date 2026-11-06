"""本步接口与证据回归；数学结论由 Coq/coqchk 独立检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage256-exit-dispatch-progsim'
PROD = 'certiucos/v293/proofs/V293ExitDispatchProgSim.v'
PROBE = 'audit/probes/V293ExitDispatchProgSimProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class ExitDispatchProgSimTests(unittest.TestCase):
    def test_original_relation_and_explicit_boundaries(self):
        self.assertEqual(sha(D / 'protocol.json'), (D / 'protocol.sha256').read_text().strip())
        src = (R / PROD).read_text()
        self.assertNotIn('CertiOS.audit.', src)
        self.assertIn('V293_os_silent_progsim', theorem(src, 'V293_exit_pure_progsim'))
        self.assertIn('cstep_idmove_deter', theorem(src, 'V293_exit_pure_progsim'))
        inc = theorem(src, 'V293_exit_increment_progsim')
        self.assertIn('V293_store_cstep_unique', inc)
        self.assertIn('V293_ready_counter_eval', inc)
        main = theorem(src, 'V293_exit_dispatch_progsim')
        statement = main.split('Proof.', 1)[0]
        for term in ['Some((false,si,cs):localst)', 'Int.add c Int.one',
                     'hpstepstar ph Th cst O Thf cst Of ->', 'V293_interrupt_handoff']:
            self.assertIn(term, statement)
        self.assertEqual(statement.count('ProgSim'), 2)
        for term in ['V293_exit_changed_prefix_progsim', 'V293_handoff_progsim']:
            self.assertIn(term, main)
        self.assertNotIn('cstepstar', main)

    def test_real_preincrement_scheduler_and_nonterminal_witness(self):
        src = (R / PROBE).read_text()
        scheduled = theorem(src, 'EPscheduled')
        for term in ['V293_ready_dispatch_call', 'CGmemory OwnershipWaiting true 0 0', 'Int.mone']:
            self.assertIn(term, scheduled)
        actual = theorem(src, 'EPactual_dispatch_simulation')
        self.assertNotIn('ProgSim', actual.split('exists M M1 Mc Mf,', 1)[0])
        self.assertNotIn('CGlocal_ready', actual)
        for term in ['EPscheduled', 'V293_exit_boundary_tail', 'V293_handoff_copy_execution',
                     'V293_ready_storage_switch_step', 'apply GHrejected', 'eapply EPbridge']:
            self.assertIn(term, actual)
        bridge = theorem(src, 'EPbridge')
        self.assertIn('apply HPpost', bridge)
        self.assertIn('apply HPschedule', bridge)
        self.assertIn('(ks:=HPpending)', bridge)

    def test_single_factor_controls_are_separate(self):
        src = (R / PROBE).read_text()
        counter = theorem(src, 'EPcounter_omission_rejected')
        self.assertIn('Int.mone', counter)
        self.assertIn('~load Tint32', counter)
        same = theorem(src, 'EPsame_single_byte_control')
        for term in ['store Tint8 M(94%positive,0%Z)', 'get Ms(b,i)=get M(b,i)',
                     'load Tint32 Ms(95%positive,0%Z)=Some(Vint32 Int.mone)',
                     'Some(Vint32 Int.zero)', 'V293_exit_same_priority_skip']:
            self.assertIn(term, same)
        self.assertIn('V293_exit_if_progsim', theorem((R / PROD).read_text(), 'V293_exit_same_progsim'))

    def test_stable_compiles_and_recursive_trust(self):
        roots = []
        for key, p in [('production', PROD), ('probe', PROBE)]:
            src = (R / p).read_text()
            self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
            compile_result = read(read('stable-compiles.json')[key] + '.json')
            self.assertEqual(compile_result['exit'], 0)
            self.assertEqual(compile_result['initial_source_sha256'], sha(R / p))
            self.assertEqual(compile_result['source_sha256'], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        for label in read('stable-compiles.json')['repeat_passes']:
            self.assertEqual(read(label + '.json')['exit'], 0)
        self.assertEqual(len(roots), 12)
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertEqual(read('build.json')['exit'], 0)

    def test_chinese_scope_and_historical_document_tails(self):
        doc = (R / 'audit/STAGE256_EXIT_DISPATCH_PROGSIM.md').read_text()
        for term in ['不是 `GOOD_OS`', '不是 `WFInt`', '不是任意 client', 'IE=false',
                     '高层匹配', '后续模拟', 'ADR-0010', 'K1–K4 未闭合',
                     'uCOS3 未开始', '未提交／推送', '存储后置条件']:
            self.assertIn(term, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- exit-dispatch-progsim-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
