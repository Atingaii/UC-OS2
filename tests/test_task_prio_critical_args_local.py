"""Regression for actual address-vs-value calls, including each call separately."""
import hashlib
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage26-task-prio-critical-args'
spec = importlib.util.spec_from_file_location('critical_args', ROOT / 'scripts/check-v293-critical-args.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


class CriticalArgumentTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.code = (ROOT / CHECK.CODE).read_text()
        cls.actual = CHECK.configured_calls()

    def test_fresh_configured_calls_pass_local_address(self):
        self.assertEqual([x['target'] for x in self.actual['calls']],
                         ['V293_EnterCritical'] + ['V293_ExitCritical'] * 4)
        self.assertEqual(CHECK.check_model(self.code),
                         [(n, '(eaddrof (evar cpu_sr) :: nil)') for n in [40, 41, 67]])

    def test_each_single_call_value_regression_is_rejected(self):
        for n in [40, 41, 67]:
            with self.subTest(error=n):
                good = f'(scall exit_id (eaddrof (evar cpu_sr) :: nil)) (srete (econst32 (Int.repr {n})))'
                self.assertEqual(self.code.count(good), 1)
                mutant = self.code.replace(good, good.replace('eaddrof (evar cpu_sr)', 'evar cpu_sr'))
                with self.assertRaisesRegex(AssertionError, 'error-call argument mismatch'):
                    CHECK.check_model(mutant)

    def test_comments_cannot_supply_missing_call(self):
        bad = self.code.replace('(scall exit_id (eaddrof (evar cpu_sr) :: nil))',
                                '(scall exit_id (evar cpu_sr :: nil))', 1)
        with self.assertRaises(AssertionError):
            CHECK.check_model(bad + '\n(* ' + self.code + ' *)\n')

    def test_only_three_call_arguments_and_comment_changed_in_program(self):
        old = (LOG / 'V293OSTaskChangePrio.v.before.txt').read_text()
        expected = old.replace('ExitCritical(cpu_sr)', 'ExitCritical(&cpu_sr)').replace(
            '(scall exit_id (evar cpu_sr :: nil))', '(scall exit_id (eaddrof (evar cpu_sr) :: nil))')
        self.assertEqual(self.code, expected)

    def test_existing_proofs_preserved_other_sources_and_fixed_inputs_unchanged(self):
        base = json.loads((LOG / 'baseline.json').read_text())
        proof = 'certiucos/v293/proofs/V293TaskPrioRekey.v'
        self.assertTrue((ROOT / proof).read_bytes().startswith((LOG / 'V293TaskPrioRekey.v.before.txt').read_bytes()))
        for name, digest in {**base['sources'], **base['protected']}.items():
            if name not in [CHECK.CODE, proof]:
                self.assertEqual(hashlib.sha256((ROOT / name).read_bytes()).hexdigest(), digest, name)

    def test_closed_unreadable_counterexample_and_no_port_oracle(self):
        proof = (ROOT / 'certiucos/v293/proofs/V293TaskPrioRekey.v').read_text()
        header = proof.split('Theorem V293_task_prio_error_exit_arguments :', 1)[1].split('Proof.', 1)[0]
        pre = header.split('  exists occupied absent,', 1)[0]
        self.assertNotIn('load ', pre)
        self.assertNotIn('P exit_id', header)
        self.assertNotIn('loststep', header)
        self.assertIn('Theorem V293_cpu_sr_unreadable_witness :', proof)


if __name__ == '__main__':
    unittest.main()
