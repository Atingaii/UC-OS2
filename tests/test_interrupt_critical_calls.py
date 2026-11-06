"""原 OSIntExit 的实际 saved 指针调用边界；不验证外部 port body。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage186-interrupt-critical-calls'
PROD = 'certiucos/v293/proofs/V293OSIntExitCriticalCalls.v'
PROBE = 'audit/probes/V293OSIntExitCriticalCallsProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]


class InterruptCriticalCallsTests(unittest.TestCase):
    def test_fixed_source_and_prospective_protocol(self):
        src = read('source-check.json')
        self.assertTrue(src['passed'])
        for path, digest in src['files'].items():
            self.assertEqual(hashlib.sha256((R / path).read_bytes()).hexdigest(), digest)
            self.assertEqual(digest, read('baseline.json')['files'][path])
        self.assertEqual(src['function']['name'], 'OSIntExit')
        self.assertEqual(src['function']['direct_calls'], ['OSIntCtxSw', 'OS_SchedNew', 'V293_EnterCritical', 'V293_ExitCritical'])
        self.assertEqual(hashlib.sha256((D / 'OSIntExit.configured.c.txt').read_bytes()).hexdigest(), src['function']['preprocessed_definition_sha256'])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(), read('protocol-identity.json')['protocol.json'])
        prev = R / 'audit/logs/stage185-interrupt-exit-dispatch/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(prev.read_bytes()).hexdigest(), src['previous_manifest_sha256'])

    def test_actual_pointer_call_and_nonidentity_resources(self):
        src = (R / PROD).read_text()
        call = statement(src, 'V293_saved_pointer_call')
        for token in ('GoodFrm frame', 'before_good:forall address', 'after_good:forall address',
                      'before(bs,Int.zero)', 'after(bs,Int.zero)',
                      'Alvarenv saved Tint32(bs,0%Z)', 'scall callee [eaddrof(evar saved)]',
                      '(Tvoid,[Tptr Tint32])'):
            self.assertIn(token, call)
        self.assertNotIn('evalval', call)
        self.assertNotIn('evaltype', call)
        self.assertIn('eapply call_rule', src)
        self.assertIn('V293_time_binding_star true saved bs R s Held', src)
        self.assertNotIn('sprim', src)
        for path in (PROD, PROBE):
            self.assertNotRegex((R / path).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
        self.assertNotIn('CertiOS.audit.', src)

    def test_local_initialization_and_exact_middle_residual(self):
        src = (R / PROD).read_text()
        self.assertIn('~GoodFunAsrt(Alvarenv saved Tint32(bs,0%Z))', src)
        init = statement(src, 'V293_OSIntExit_saved_initialize')
        self.assertIn('V293_time_cell true saved bs old', init)
        self.assertIn('sassign(evar saved)(econst32 Int.zero)', init)
        self.assertIn('V293_saved_pointer_resource aop(Vint32 Int.zero)', init)
        main = statement(src, 'V293_OSIntExit_critical_calls')
        self.assertEqual(main.count('V293_OSIntExit_nesting_dispatch'), 2)
        for token in ('scall enter [eaddrof(evar saved)]', 'scall exit [eaddrof(evar saved)]',
                      'Spec enter=Some', 'Spec exit=Some', 'acquired(bs,Int.zero)', 'leaving(bs,Int.zero)'):
            self.assertIn(token, main)
        self.assertNotIn('V293_OSIntExit_body', main)

    def test_same_heap_pointer_and_saved_load_controls(self):
        src = (R / PROBE).read_text()
        for name in ('SCnonempty', 'SCalternate_nonempty', 'SCbinding_control', 'SCsaved_load',
                     'SCsaved_value_control', 'SCsaved_frame', 'SCcallee_snapshots_nonempty',
                     'SCcall_checked', 'SCinitialize_checked', 'SClookup_ablation', 'SClocal_boundary'):
            self.assertIn(name, src)
        binding = statement(src, 'SCbinding_control')
        self.assertEqual(binding.count('SCmemory(Vint32 Int.zero)'), 3)
        self.assertIn('SCle 751%positive', binding)
        self.assertIn('SCle 752%positive', binding)
        self.assertIn('eq_dom_env', binding)
        saved = statement(src, 'SCsaved_value_control')
        self.assertEqual(saved.count('SCmemory(Vint32 Int.one)'), 3)
        self.assertIn('rewrite Actual in Wrong', src)
        self.assertIn('b<>751%positive', src)
        lookup = statement(src, 'SClookup_ablation')
        self.assertIn('SCspec 9401%Z=Some', lookup)
        self.assertNotIn('InfRules', lookup)

    def test_stable_compiles_and_recursive_trust(self):
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
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))


if __name__ == '__main__':
    unittest.main()
