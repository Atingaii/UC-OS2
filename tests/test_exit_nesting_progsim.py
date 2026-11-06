"""语句契约回归；实际证明有效性另由 Coq / coqchk 验证。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage260-exit-nesting-progsim'
PROD = 'certiucos/v293/proofs/V293ExitNestingProgSim.v'
PROBE = 'audit/probes/V293ExitNestingProgSimProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class ExitNestingProgSimTests(unittest.TestCase):
    def test_actual_saturating_store_and_updated_guards(self):
        self.assertEqual(sha(D / 'protocol.json'), (D / 'protocol.sha256').read_text().strip())
        src = (R / PROD).read_text()
        self.assertIn('if Nat.eqb n 0 then M else V293_write_byte M bn (Nat.pred n)', src)
        decr = theorem(src, 'V293_exit_decrement_progsim')
        for term in ['V293_exit_ifthen_progsim', 'V293_assign_byte_progsim',
                     'V293_write_byte_store', 'destruct n.', 'Some(true,raw)']:
            self.assertIn(term, decr)
        guards = theorem(src, 'V293_exit_nesting_progsim')
        for term in ['n<256', 'locked<256', 'Nat.pred n=0 ->', 'V293_exit_decrement_load',
                     'V293_success_global_byte_eq', 'V293_OSIntExit_nesting_dispatch',
                     'V293_exit_if_progsim', 'V293_exit_decrement_progsim']:
            self.assertIn(term, guards)
        self.assertIn('sifthen_step', theorem(src, 'V293_exit_ifthen_progsim'))

    def test_vertical_connection_has_only_final_simulation_post(self):
        src = (R / PROD).read_text()
        common = src.split('Section NestingDispatch.', 1)[1].split('Theorem ', 1)[0]
        self.assertNotIn('ProgSim', common)
        self.assertIn('Some((false,si,cs):localst)', common)
        self.assertIn('Hypothesis Active:n<=1.', common)
        body = theorem(src, 'V293_exit_nesting_dispatch_progsim')
        self.assertEqual(body.split('Proof.', 1)[0].count('ProgSim'), 2)
        for term in ['V293_OSIntExit_nesting_dispatch', 'V293_exit_nesting_progsim',
                     'V293_exit_call_dispatch_progsim', 'hpstepstar ph Th cst O Thf cst Of']:
            self.assertIn(term, body)
        disabled = theorem(src, 'V293_exit_nesting_disabled_progsim')
        self.assertIn('(2<=n \/ 0<locked)', disabled)
        self.assertNotIn('get ge dispatch', disabled)

    def test_same_heap_independent_instance_and_single_factor_controls(self):
        src = (R / PROBE).read_text()
        canonical = theorem(src, 'NPdecrement_canonical')
        for term in ['NPinitial 1', '=CEM', 'HalfPermMap.extensionality', 'NPzero_cells']:
            self.assertIn(term, canonical)
        bridge = theorem(src, 'NPbridge')
        self.assertIn('V293_exit_nesting_dispatch_progsim', bridge)
        self.assertIn('NPdecrement_canonical', bridge)
        self.assertIn('apply HPpost', bridge)
        instance = theorem(src, 'NPactual_nesting_dispatch_simulation')
        self.assertEqual(instance.split('Proof.', 1)[0].count('ProgSim'), 1)
        for term in ['NPbridge', 'XPscheduled_canonical', 'GHrejected',
                     'V293_ready_storage_switch_step', 'Int.add Int.mone Int.one=Int.zero']:
            self.assertIn(term, instance)
        for name in ['NPguard_controls', 'NPzero_no_wrap', 'NPnested_unbound_lock']:
            self.assertIn(name + ' :', src)
        control = theorem(src, 'NPguard_controls')
        for term in ['NPinitial 1', 'V293_OSSched_zero', 'V293_write_byte CEM 97%positive 1',
                     'Int.zero', 'Int.one']:
            self.assertIn(term, control)

    def test_compiles_trust_and_project_registration(self):
        roots = []
        stable = read('stable-compiles.json')
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
        self.assertEqual(len(roots), 14)
        self.assertEqual(trust['roots_printed'], 14)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertEqual(read('build.json')['exit'], 0)
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(PROD), 1)

    def test_scope_provenance_and_old_tails(self):
        doc = (R / 'audit/STAGE260_EXIT_NESTING_PROGSIM.md').read_text()
        for term in ['不是 `GOOD_OS`', '不是 `WFInt`', 'IE=false', 'ADR-0010',
                     'K1–K4 未闭合', 'uCOS3 未开始', '未提交／推送', 'high=88',
                     '不是完整变异程序的执行消融', '最终端点模拟与高层匹配']:
            self.assertIn(term, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- exit-nesting-progsim-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
        self.assertTrue(read('source-identity.json')['passed'])
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h)
