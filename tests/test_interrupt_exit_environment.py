"""静态调用闭合不是函数正确；Coq 核验独立于这些结构检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest
R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage204-interrupt-exit-environment'
PROD = 'certiucos/v293/proofs/V293InterruptExitEnvironment.v'
PROBE = 'audit/probes/V293InterruptExitEnvironmentProbe.v'
def read(name):
    return json.loads((D / name).read_text())
def statement(src, name):
    return src.split(name + ' :', 1)[1].split('Proof.', 1)[0]
class InterruptExitEnvironmentTests(unittest.TestCase):
    def test_exact_source_and_prospective_protocol(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        self.assertEqual([x['function']['name'] for x in source['functions']],
                         ['OSIntEnter', 'OSIntExit', 'OS_SchedNew'])
        for x in source['functions']:
            self.assertTrue(x['reconstructed_repaired_source_matches'])
            self.assertTrue(x['temporary_source_removed_on_context_exit'])
            self.assertEqual(hashlib.sha256((D / (x['function']['name'] + '.configured.c.txt')).read_bytes()).hexdigest(),
                             x['function']['preprocessed_definition_sha256'])
        for p, h in source['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
            self.assertEqual(h, read('baseline.json')['files'][p])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])
        old = R / 'audit/logs/stage203-interrupt-function-environment/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_exact_remaining_obligation_not_unconditional_body_claim(self):
        src = (R / PROD).read_text()
        stmt = statement(src, 'V293_exit_env_remaining_body')
        for token in ('WFFunEnv P Spec sd li inv <->', 'forall vl pre post lg tid',
                      'Some pre=BuildPreI P exit vl lg xp tid', 'Some post=BuildRetI P exit vl lg xq tid',
                      'InfRules Spec sd li inv post Afalse pre body Afalse tid'):
            self.assertIn(token, stmt)
        for token in ('eapply V293_OSIntEnter_internal_contract',
                      'eapply V293_OSSchedNew_internal_contract', 'exact Remaining'):
            self.assertIn(token, src)
        self.assertNotIn('CertiOS.audit.', src)
        self.assertIn('WFFunEnv XEP XESpec sd V293_witness_li inv <->',
                      statement((R / PROBE).read_text(), 'XEremaining_exact'))

    def test_normalization_and_all_actual_internal_calls(self):
        src = (R / PROBE).read_text()
        for name in ('XEnormalized', 'XEcritical_normalized', 'XEswitch_only_mapping',
                     'XEthree_entries', 'XEdomain', 'XEclosed_calls'):
            self.assertIn('Theorem ' + name + ' :', src)
        for token in ('[201%Z;200%Z;203%Z;202%Z]', '[200%Z;203%Z]', '[200%Z]'):
            self.assertIn(token, statement(src, 'XEexact_calls'))
        prod = (R / PROD).read_text()
        self.assertIn('forall f t d1 d2 s,P f=Some(t,d1,d2,s)', prod)
        self.assertIn('forall callee,In callee(V293_direct_calls s)', prod)
        self.assertIn('V293_exit_env_syntax', prod)
        self.assertNotIn('cstepstar', src)

    def test_nonempty_original_builders_and_single_factor_controls(self):
        src = (R / PROBE).read_text()
        for token in ('BuildPreI XEP 300%Z', 'BuildRetI XEP 300%Z',
                      'BuildPreI BLprogram 300%Z', 'BuildRetI BLprogram 300%Z',
                      'RCbigstate nc nest c run value |= pre', 'apply UIpre_nonempty_all_running'):
            self.assertIn(token, src)
        self.assertIn('UIfp UIfq', src)
        self.assertIn('EqDom(XEP_with XEcritical)XESpec', statement(src, 'XEcritical_only_same_domain'))
        self.assertIn('f<>300%Z ->XEP_with XEcritical f=XEP f', src)
        self.assertIn('~V293_direct_calls_defined(XEP_with XEcritical)', statement(src, 'XEcritical_only_rejected'))
        self.assertIn('if Z.eq_dec f 200%Z then None else XEP f', src)
        self.assertIn('f<>200%Z ->XEmissing f=XEP f', src)
        self.assertIn('XEmissing 300%Z=XEP 300%Z', src)
        self.assertIn('~V293_direct_calls_defined XEmissing', statement(src, 'XEmissing_calls_rejected'))
        self.assertIn('~WFFunEnv XEmissing XESpec sd V293_witness_li inv', statement(src, 'XEmissing_WFFunEnv_rejected'))

    def test_stable_compiles_dynamic_recursive_trust_and_no_new_holes(self):
        roots = []
        for kind, p in (('body', PROD), ('probe', PROBE)):
            src = (R / p).read_text()
            label = read('stable-compiles.json')[kind]
            row = read(label + '.json')
            h = hashlib.sha256((R / p).read_bytes()).hexdigest()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(h, row['initial_source_sha256'])
            self.assertEqual(h, row['source_sha256'])
            self.assertEqual(h, hashlib.sha256((D / (label + '.v.snapshot.txt')).read_bytes()).hexdigest())
            self.assertNotRegex(src, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', src, re.M)]
        trust = read('trust.json')
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertEqual(list(read('assumptions-by-root.json')), roots)
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
        self.assertTrue(all(x['exit'] == 0 for x in trust['commands']))
