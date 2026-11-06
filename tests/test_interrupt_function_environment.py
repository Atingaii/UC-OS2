"""共同中断函数环境的结构回归；证明有效性由 coqc/递归 coqchk 独立核验。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage203-interrupt-function-environment'
PROD = 'certiucos/v293/proofs/V293InterruptFunctionEnvironment.v'
PROBE = 'audit/probes/V293InterruptFunctionEnvironmentProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return src.split(name + ' :', 1)[1].split('Proof.', 1)[0]


class InterruptFunctionEnvironmentTests(unittest.TestCase):
    def test_exact_five_sources_and_frozen_protocol(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        self.assertEqual([x['function']['name'] for x in source['functions']],
                         ['OSVersion', 'OSTimeSet', 'OSTimeGet', 'OSIntEnter', 'OS_SchedNew'])
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
        old = R / 'audit/logs/stage202-interrupt-source-roundtrip/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_universal_real_builders_in_exact_merged_environment(self):
        src = (R / PROD).read_text()
        stmt = statement(src, 'V293_irq_internal_WFFunEnv')
        self.assertEqual(stmt.count('WFFunEnv'), 1)
        self.assertNotIn('InfRules', stmt)
        self.assertIn('WFFunEnv(V293_irq_internal_unit', stmt)
        self.assertIn('(V293_irq_internal_spec', stmt)
        self.assertIn('intros vl p r lg tid Pre Post', src)
        self.assertIn('eapply V293_OSIntEnter_internal_contract', src)
        self.assertIn('eapply V293_OSSchedNew_internal_contract', src)
        self.assertIn('V293_irq_internal_domains', src)
        self.assertIn('V293_irq_internal_WFIFun', src)
        self.assertIn('V293_irq_internal_syntax', src)
        self.assertNotIn('CertiOS.audit.', src)

    def test_same_canonical_local_and_shared_invariant_and_actual_five_bindings(self):
        src = (R / PROD).read_text()
        stmt = statement(src, 'V293_irq_clock_components_checked')
        for token in ('V293_time_names_li now btime', 'V293_time_shared_inv btime',
                      'GoodI', 'WFAPI', 'WFFunEnv', 'WFIFun', 'no_fun_same'):
            self.assertIn(token, stmt)
        for token in ('apply V293_clock_WFAPI', 'apply V293_time_names_good',
                      'apply V293_irq_internal_WFFunEnv', 'apply V293_irq_clock_disjoint'):
            self.assertIn(token, src)
        probe = (R / PROBE).read_text()
        stmt = statement(probe, 'FEfive_entries')
        for token in ('pumerge FEAPI FEP', 'P 201%Z=', 'P 202%Z=', 'P 203%Z=',
                      'P 301%Z=', 'P 200%Z=', 'V293_OSIntEnter_function'):
            self.assertIn(token, stmt)
        self.assertIn('apply V293_irq_clock_components_checked;discriminate', probe)

    def test_two_nonempty_real_builders_and_single_factor_boundary_controls(self):
        src = (R / PROBE).read_text()
        for name, fid in [('FEsched_nonvacuous', '200'), ('FEenter_nonvacuous', '301')]:
            stmt = statement(src, name)
            for token in ('FESpec ' + fid + '%Z', 'BuildPreI FEP ' + fid + '%Z',
                          'BuildRetI FEP ' + fid + '%Z', 's |= pre'):
                self.assertIn(token, stmt)
        self.assertIn('V293_wstate FEGE V293_witness_le V293_witness_memory', src)
        self.assertIn('V293_wstate FEGE emp M', src)
        self.assertIn('merge(IEbyte 701%positive run)', src)
        self.assertIn('V293_witness_current', src)
        self.assertIn('forall f,f<>301%Z ->FEvariant replacement f=FEP f', src)
        self.assertIn('Some(Tint32,dnil,dnil,V293_OSIntEnter_body', src)
        self.assertIn('~WFFunEnv(FEvariant None)FESpec sd FELI inv', statement(src, 'FEmissing_rejected'))
        self.assertIn('EqDom(FEvariant FEwrong)FESpec', statement(src, 'FEwrong_domain_still_matches'))
        self.assertIn('~WFFunEnv(FEvariant FEwrong)FESpec sd FELI inv', statement(src, 'FEwrong_type_rejected'))
        self.assertIn('distinct calls', src)
        self.assertNotIn('cstepstar', src)

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
