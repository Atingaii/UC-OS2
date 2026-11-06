"""接口与证据回归；证明有效性由实际 Coq/coqchk 验证。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage261-critical-return-progsim'
PROD = 'certiucos/v293/proofs/V293CriticalReturnProgSim.v'
PROBE = 'audit/probes/V293CriticalReturnProgSimProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class CriticalReturnProgSimTests(unittest.TestCase):
    def test_only_final_caller_simulation_is_public(self):
        src = (R / PROD).read_text()
        body = theorem(src, 'V293_exit_quiet_return_progsim')
        self.assertEqual(body.split('Proof.', 1)[0].count('ProgSim'), 2)
        for term in ['kseq sret(kcall f body caller ks)', 'getaddr le=((bs,Tint32)::nil)',
                     'free Tint32 bs', '(2<=n \/ 0<locked)',
                     'V293_exit_quiet_critical_progsim', 'V293_one_local_return_progsim']:
            self.assertIn(term, body)
        critical = theorem(src, 'V293_exit_quiet_critical_progsim')
        self.assertEqual(critical.split('Proof.', 1)[0].count('ProgSim'), 2)
        for term in ['V293_encrit_progsim', 'V293_excrit_progsim',
                     'V293_exit_nesting_disabled_progsim', 'V293_critical_aux_roundtrip']:
            self.assertIn(term, critical)

    def test_original_step_all_successors_output_abort(self):
        src = (R / PROD).read_text()
        for name in ['V293_critical_progress', 'V293_critical_all_successors',
                     'V293_critical_no_output', 'V293_critical_no_abort']:
            self.assertIn(name + ' :', src)
        sim = theorem(src, 'V293_critical_progsim')
        for term in ['simulation.prog_sim', 'V293_critical_all_successors',
                     'V293_critical_no_output', 'V293_critical_no_abort']:
            self.assertIn(term, sim)
        excrit = theorem(src, 'V293_excrit_progsim')
        self.assertIn('Some((false,si,saved::cs):localst)', excrit)
        self.assertIn('set aus t(saved,si,cs)', excrit)
        self.assertIn('apply excrit_step', excrit)
        ret = theorem(src, 'V293_one_local_return_progsim')
        for term in ['sret_step', 'sfree_step', 'sfreeend_step', 'V293_os_family_progsim']:
            self.assertIn(term, ret)

    def test_typed_actual_heap_and_non_circular_return_instance(self):
        src = (R / PROBE).read_text()
        typed = theorem(src, 'CPtyped_updated')
        for term in ['NPinitial n', 'CEtyped_heap', 'V293_owned_byte_update', 'CPother']:
            self.assertIn(term, typed)
        self.assertIn('CPdecr=NPinitial 1', theorem(src, 'CPdecrement'))
        instance = theorem(src, 'CPquiet_return_simulation')
        self.assertEqual(instance.split('Proof.', 1)[0].count('ProgSim'), 1)
        for term in ['CPsaved_release', 'V293_exit_quiet_return_progsim', 'SPterminal',
                     'V293_freeb_removed', 'V293_freeb_outside', '(n:=2)', '(Mf:=Mf)']:
            self.assertIn(term, instance)
        self.assertIn('V293_cpu_release', theorem(src, 'CPsaved_release'))
        self.assertIn('V293_exit_boundary_function', src)

    def test_real_primitive_stack_single_factor_controls(self):
        src = (R / PROBE).read_text()
        control = theorem(src, 'CPexcrit_stack_control')
        self.assertEqual(control.split('Proof.', 1)[0].count('loststep'), 3)
        for term in ['false::cs', 'true::cs', '(m,ir,(true,si,cs))', 'V293_excrit_successor']:
            self.assertIn(term, control)
        empty = theorem(src, 'CPempty_stack_no_step')
        self.assertIn('~loststep', empty)
        self.assertIn('(false,si,nil)', empty)
        abort = theorem(src, 'CPempty_stack_aborts')
        for term in ['lpstepabt', 'progabort', 'taskabort', 'CPempty_stack_no_step']:
            self.assertIn(term, abort)

    def test_compiles_trust_identity_and_bounded_documentation(self):
        self.assertEqual(sha(D / 'protocol.json'), (D / 'protocol.sha256').read_text().strip())
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
        self.assertEqual(read('build.json')['exit'], 0)
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(PROD), 1)
        doc = (R / 'audit/STAGE261_CRITICAL_RETURN_PROGSIM.md').read_text()
        for term in ['不是 `GOOD_OS`', '不是 `WFInt`', 'IE=false', 'ADR-0010',
                     'K1–K4 未闭合', 'uCOS3 未开始', '未提交／推送', 'high=88',
                     '不是完整变异程序的执行消融', '最终 caller 端点模拟']:
            self.assertIn(term, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- critical-return-progsim-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h)
