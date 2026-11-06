"""原 OSIntExit 真实函数 builder 的条件连接，不代表全函数环境。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage189-interrupt-function-builders'
PROD = 'certiucos/v293/proofs/V293OSIntExitBuilders.v'
PROBE = 'audit/probes/V293OSIntExitBuildersProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]


class InterruptFunctionBuildersTests(unittest.TestCase):
    def test_source_and_prospective_protocol_identity(self):
        src = read('source-check.json')
        self.assertTrue(src['passed'])
        for path, digest in src['files'].items():
            self.assertEqual(hashlib.sha256((R / path).read_bytes()).hexdigest(), digest)
            self.assertEqual(digest, read('baseline.json')['files'][path])
        self.assertEqual(src['function']['name'], 'OSIntExit')
        self.assertEqual(src['function']['direct_calls'], ['OSIntCtxSw', 'OS_SchedNew', 'V293_EnterCritical', 'V293_ExitCritical'])
        self.assertEqual(hashlib.sha256((D / 'OSIntExit.configured.c.txt').read_bytes()).hexdigest(), src['function']['preprocessed_definition_sha256'])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(), read('protocol-identity.json')['protocol.json'])
        prev = R / 'audit/logs/stage188-interrupt-full-body/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(prev.read_bytes()).hexdigest(), src['previous_manifest_sha256'])

    def test_actual_builder_contract_directly_uses_body_with_only_switch_residual(self):
        src = (R / PROD).read_text()
        main = statement(src, 'V293_OSIntExit_builder_contract')
        self.assertEqual(main.count('InfRules'), 2)
        self.assertEqual(main.count('V293_OSIntExit_body running'), 1)
        self.assertEqual(main.count('(scall int_switch nil)'), 1)
        self.assertIn('(forall bs,run=1 -> V293_exit_depth nest=0', main)
        self.assertIn('Int.add c Int.one', main)
        for token in ('BuildPreI P f vl lg', 'BuildRetI P f vl lg', 'V293_OSIntExit_function',
                      'run=1 -> Spec sched_id=Some', 'run=1 -> Spec enter=Some',
                      'run=1 -> Spec exit=Some'):
            self.assertIn(token, main)
        self.assertNotIn('oldsave', main)
        self.assertNotIn('saved bs oldsave', main)
        self.assertIn('eapply (V293_OSIntExit_body_hoare', src)
        self.assertIn('apply ex_intro_rule;intro oldsave;apply ex_intro_rule;intro bs', src)
        for path in (PROD, PROBE):
            text = (R / path).read_text()
            self.assertNotRegex(text, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            self.assertNotIn('CertiOS.audit.', text)
            self.assertNotIn('sprim', text)

    def test_nonrunning_contract_does_not_require_any_callee_lookup(self):
        src = (R / PROD).read_text()
        off = statement(src, 'V293_OSIntExit_not_running_builder_contract')
        self.assertEqual(off.count('InfRules'), 1)
        for token in ('Spec sched_id=', 'Spec enter=', 'Spec exit='):
            self.assertNotIn(token, off)
        self.assertIn('run<>1', off)
        self.assertIn('BuildPreI', off)
        self.assertIn('BuildRetI', off)
        probe = (R / PROBE).read_text()
        self.assertIn('InfRules(fun _=>None)', statement(probe, 'BLno_lookup_builder'))
        for name in ('BLactual_builders', 'BLnonempty_arguments_rejected'):
            self.assertIn('BuildPreI BLprogram', statement(probe, name))
        self.assertIn('BuildRetI BLprogram', statement(probe, 'BLactual_builders'))

    def test_nonempty_raw_locals_addresses_and_retained_local_domain(self):
        src = (R / PROBE).read_text()
        for name in ('BLbuilder_nonempty', 'BMbuilder_nonempty', 'BLold_value_control',
                     'BLlocal_address_control', 'BLold_value_frame', 'BLbinding_domain_same', 'BLpost_nonempty'):
            self.assertIn('Theorem ' + name + ' :', src)
        control = statement(src, 'BLold_value_control')
        self.assertIn('BLfullstate 0 Vundef', control)
        self.assertIn('BLfullstate 0(Vint32 Int.one)', control)
        address = statement(src, 'BLlocal_address_control')
        for token in ('BLfullstate 1 Vundef', 'BMfullstate 1 Vundef',
                      'eaddrof(evar 120%Z)', '15%positive', '17%positive'):
            self.assertIn(token, address)
        self.assertIn('b<>15%positive', statement(src, 'BLold_value_frame'))
        self.assertIn('BLbuilderpost run None', statement(src, 'BLpost_nonempty'))
        prod = (R / PROD).read_text()
        self.assertIn('V293_exit_builder_cells saved ** V293_exit_builder_external_post result ** V293_exit_builder_domain saved', prod)
        self.assertIn('EX old:val,LV saved @Tint32|->old', prod)
        self.assertIn('apply V293_exit_builder_names', prod)
        self.assertIn('GoodFunAsrt V293_exit_builder_external_pre', prod)
        self.assertIn('GoodFunAsrt(V293_exit_builder_external_post result)', prod)

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
