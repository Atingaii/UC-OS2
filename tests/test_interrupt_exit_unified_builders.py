"""结构回归只约束本步证据；实际 Hoare 证明由 Coq 核验。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage209-interrupt-exit-unified-builders'
PROD = 'certiucos/v293/proofs/V293OSIntExitUnifiedInternal.v'
PROBE = 'audit/probes/V293OSIntExitUnifiedInternalProbe.v'

def read(n):
    return json.loads((D / n).read_text())

def statement(src, name):
    return src.split(name + ' :', 1)[1].split('Proof.', 1)[0]

class InterruptExitUnifiedBuildersTests(unittest.TestCase):
    def test_source_identity_and_prospective_protocol(self):
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
        old = R / 'audit/logs/stage208-interrupt-exit-same-builders/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_quiet_actual_builders_and_no_external_locals(self):
        src = (R / PROD).read_text()
        stmt = statement(src, 'V293_OSIntExit_quiet_builder_contract')
        self.assertEqual(stmt.count('InfRules'), 1)
        for token in ('BuildPreI', 'BuildRetI', 'V293_exit_boundary_function',
                      'V293_quiet_exit_fpre', 'V293_quiet_exit_fpost'):
            self.assertIn(token, stmt)
        self.assertIn('apply V293_OSIntExit_nondispatch_body', src)
        self.assertIn('V293_exit_builder_not_shadow', src)
        external = src.split('Definition V293_quiet_external', 1)[1].split('Let frame', 1)[0]
        for token in ('Alvarenv', 'A_dom_lenv', 'A_notin_lenv', ' saved'):
            self.assertNotIn(token, external)
        valid = src.split('Definition V293_quiet_exit_valid', 1)[1].split('Section QuietBuilders', 1)[0]
        for token in ('run<256', 'nest<256', 'locked<256', '2<=nest', '0<locked', 'gettopis si<=INUM'):
            self.assertIn(token, valid)
        self.assertNotIn('CertiOS.audit.', src)

    def test_union_uses_same_real_function_and_enhanced_environment(self):
        src = (R / PROD).read_text()
        stmt = statement(src, 'V293_OSIntExit_unified_builder_contract')
        self.assertEqual(stmt.count('InfRules'), 1)
        for token in ('BuildPreI', 'BuildRetI', 'V293_exit_boundary_function', 'V293_ISR_sched_fpre'):
            self.assertIn(token, stmt)
        for token in ('eapply (V293_OSIntExit_quiet_builder_contract',
                      'eapply (V293_OSIntExit_same_builder_contract',
                      'eapply V293_OSIntExit_unified_builder_contract',
                      'eapply V293_OSIntEnter_internal_contract',
                      'eapply V293_OSSchedNew_ISR_contract'):
            self.assertIn(token, src)
        self.assertIn('logic_ie true::lg', src)
        self.assertIn('logic_ie false::lg', src)
        for name, predicate in [('V293_unified_exit_env_WFFunEnv', 'WFFunEnv'),
                                ('V293_unified_exit_env_WFIFun', 'WFIFun')]:
            stmt = statement(src, name)
            self.assertEqual(stmt.count(predicate), 1)
            self.assertNotIn('InfRules', stmt)

    def test_three_nonempty_quiet_causes_and_valid_IE_identity_control(self):
        src = (R / PROBE).read_text()
        for name in ('UBbuilders', 'UBenvironment', 'UBbig_owned', 'UBowned',
                     'UBquiet_pre_nonempty', 'UBquiet_three_causes', 'UBquiet_decode',
                     'UBquiet_valid', 'UBquiet_IE_control', 'UBsame_pre_nonempty', 'UBsame_actual_program'):
            self.assertRegex(src, r'(?:Theorem|Lemma) ' + name + ' :')
        cases = statement(src, 'UBquiet_three_causes')
        for token in ('UBstate enabled 1 2 0', 'UBstate enabled 1 1 1', 'UBstate enabled 0 1 0'):
            self.assertIn(token, cases)
        self.assertIn('apply BLphysical_owned', src)
        self.assertIn('pose proof(BIpre_nonempty enabled)', src)
        ctl = statement(src, 'UBquiet_IE_control')
        self.assertIn('UBlogic true 1 2 0', ctl)
        self.assertIn('UBlogic false 1 2 0', ctl)
        self.assertEqual(ctl.count('UBstate true 1 2 0'), 2)
        self.assertIn('apply astar_l_aie_elim in IE as[E _];discriminate.', src)
        self.assertIn('not two complete program executions', src)
        self.assertNotIn('cstepstar', src)
        self.assertNotIn('loststep', src)

    def test_stable_compiles_recursive_trust_and_no_new_holes(self):
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
