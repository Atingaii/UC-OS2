"""原 OSIntExit 的真实调度／计数／守卫连接；仅剩实际中断调用残余。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage185-interrupt-exit-dispatch'
PROD = 'certiucos/v293/proofs/V293OSIntExitDispatch.v'
PROBE = 'audit/probes/V293OSIntExitDispatchProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]


class InterruptExitDispatchTests(unittest.TestCase):
    def test_fixed_configured_source_and_prospective_protocol(self):
        src = read('source-check.json')
        self.assertTrue(src['passed'])
        for path, digest in src['files'].items():
            self.assertEqual(hashlib.sha256((R / path).read_bytes()).hexdigest(), digest)
            self.assertEqual(digest, read('baseline.json')['files'][path])
        entry = src['function']
        self.assertEqual((entry['name'], entry['first_line'], entry['last_line']), ('OSIntExit', 693, 736))
        self.assertEqual(entry['direct_calls'], ['OSIntCtxSw', 'OS_SchedNew', 'V293_EnterCritical', 'V293_ExitCritical'])
        self.assertEqual(hashlib.sha256((D / 'OSIntExit.configured.c.txt').read_bytes()).hexdigest(), entry['preprocessed_definition_sha256'])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(), read('protocol-identity.json')['protocol.json'])
        previous = R / 'audit/logs/stage184-interrupt-exit/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(previous.read_bytes()).hexdigest(), src['previous_manifest_sha256'])

    def test_actual_dispatch_has_only_real_interrupt_call_residual(self):
        src = (R / PROD).read_text()
        tail = statement(src, 'V293_OSIntExit_dispatch_tail')
        for token in ('scall int_switch nil', 'sif (V293_OSSched_different',
                      'V293_OSSched_increment counter', 'sseq(sskip None)', 'else q'):
            self.assertIn(token, tail)
        main = statement(src, 'V293_OSIntExit_ready_dispatch')
        self.assertIn('posttail(Int.add c Int.one))(scall int_switch nil)q tid', main)
        self.assertIn('V293_OSIntExit_nesting_dispatch', main)
        self.assertNotIn('dispatch q tid', main)
        self.assertNotIn('sprim', src)
        self.assertNotIn('CertiOS.audit.', src)
        for path in (PROD, PROBE):
            self.assertNotRegex((R / path).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')

    def test_joint_count_resources_and_disabled_interface(self):
        src = (R / PROD).read_text()
        for token in ('V293_exit_ready_reorder', 'V293_exit_ready_restore',
                      'V293_OSIntExit_decrement_hoare', 'V293_exit_ready_guard_eval',
                      'V293_OSSched_unlocked_prefix_hoare', 'V293_OSSched_tail_increment',
                      'V293_exit_known_if', 'V293_rdy_raw_cells'):
            self.assertIn(token, src)
        disabled = statement(src, 'V293_OSIntExit_ready_disabled')
        self.assertIn(r'(2<=nest \/ 0<locked)', disabled)
        self.assertNotIn('Spec sched_id', disabled)
        self.assertNotIn('InfRules Spec sd li I r ri(posttail', disabled)

    def test_physical_priority_counter_controls_and_wrong_post(self):
        src = (R / PROBE).read_text()
        for token in ('JDnonempty', 'JDtail_nonempty', 'JDactual_comparison',
                      'JDpriority_control', 'JDpriority_frame', 'JDcounter_frame',
                      'JDcounter_boundary_control', 'JDincrement_ablation',
                      'JDsame_checked', 'JDdisabled_checked', 'JDtail_counter_load'):
            self.assertIn(token, src)
        wrong = statement(src, 'JDwrong_post_control')
        self.assertIn('eq_dom_env', wrong)
        self.assertIn('JDtail 0 0 0 Int.one', wrong)
        self.assertIn('JDtail 0 0 0 Int.zero', wrong)
        self.assertIn('rewrite Actual in Wrong', src)
        bounds = statement(src, 'JDcounter_boundary_control')
        self.assertIn('Int.max_unsigned', bounds)
        self.assertIn('evalval JDincrement_expr', bounds)
        priority = statement(src, 'JDpriority_control')
        self.assertIn('0 0 12 Int.zero', priority)
        self.assertIn('0 0 0 Int.zero', priority)

    def test_actual_stable_compiles_and_recursive_trust(self):
        stable = read('stable-compiles.json')
        for kind, path in (('body', PROD), ('probe', PROBE)):
            row = read(stable[kind] + '.json')
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['source_sha256'], row['initial_source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256((R / path).read_bytes()).hexdigest())
        trust = read('trust.json')
        self.assertTrue(trust['passed'])
        self.assertTrue(trust['recursive'])
        self.assertEqual(len(trust['entry_modules']), 2)
        self.assertEqual(trust['roots_printed'], len(trust['roots']))
        self.assertTrue(set(trust['assumptions']) <= set(trust['allowed']))
        for row in trust['commands']:
            self.assertEqual(row['exit'], 0)


if __name__ == '__main__':
    unittest.main()
