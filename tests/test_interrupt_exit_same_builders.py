"""结构回归只约束本步证据；实际 Hoare 证明由 Coq 核验。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage208-interrupt-exit-same-builders'
PROD = 'certiucos/v293/proofs/V293OSIntExitSameInternal.v'
PROBE = 'audit/probes/V293OSIntExitSameInternalProbe.v'

def read(n):
    return json.loads((D / n).read_text())

def statement(src, name):
    return src.split(name + ' :', 1)[1].split('Proof.', 1)[0]

class InterruptExitSameBuildersTests(unittest.TestCase):
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
        old = R / 'audit/logs/stage207-interrupt-exit-same-priority/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_actual_builders_and_closed_three_function_environment(self):
        src = (R / PROD).read_text()
        stmt = statement(src, 'V293_OSIntExit_same_builder_contract')
        self.assertEqual(stmt.count('InfRules'), 1)
        for token in ('BuildPreI', 'BuildRetI', 'V293_exit_boundary_function',
                      'V293_ISR_sched_fpre', 'V293_same_exit_fpre', 'V293_same_exit_fpost'):
            self.assertIn(token, stmt)
        for token in ('apply V293_OSIntExit_same_priority_body',
                      'eapply V293_OSIntExit_same_builder_contract',
                      'eapply V293_OSIntEnter_internal_contract',
                      'eapply V293_OSSchedNew_ISR_contract'):
            self.assertIn(token, src)
        for name, predicate in [('V293_same_exit_env_WFFunEnv', 'WFFunEnv'),
                                ('V293_same_exit_env_WFIFun', 'WFIFun')]:
            stmt = statement(src, name)
            self.assertEqual(stmt.count(predicate), 1)
            self.assertNotIn('InfRules', stmt)
        self.assertNotIn('CertiOS.audit.', src)

    def test_external_contract_does_not_supply_local_bindings(self):
        src = (R / PROD).read_text()
        memory = src.split('Definition V293_same_exit_memory', 1)[1].split('Lemma V293_same_exit_memory_good', 1)[0]
        for token in ('Aie', 'Aisr', 'Ais ', 'Acs ', 'invlth_isr', '<||aop||>', 'Alvarenv', 'A_notin_lenv'):
            self.assertNotIn(token, memory)
        external = src.split('Definition V293_same_exit_external', 1)[1].split('Let data', 1)[0]
        for token in ('Alvarenv', 'A_dom_lenv', 'A_notin_lenv', ' saved'):
            self.assertNotIn(token, external)
        for token in ('V293_exit_builder_names with(high:=high)',
                      'V293_exit_builder_domain saved',
                      'V293_same_exit_memory_good', 'V293_same_exit_external_good'):
            self.assertIn(token, src)
        valid = src.split('Definition V293_same_exit_valid', 1)[1].split('Section SameBuilders', 1)[0]
        for token in ('V293_xnest x<=1', 'V293_xlocked x=0', 'V293_exit_snapshot_bounded',
                      'V293_bitmap_tasks', 'V293_priority_table', '=V293_xcurrent x'):
            self.assertIn(token, valid)

    def test_nonempty_valid_IE_control_and_asymmetric_arity(self):
        src = (R / PROBE).read_text()
        for name in ('BIbuilders', 'BIenvironment', 'BIvalid', 'BIdecode', 'BIowned',
                     'BIpre_nonempty', 'BIie_control', 'BIarity_control', 'BIreturn_arity_observation'):
            self.assertRegex(src, r'(?:Theorem|Lemma) ' + name + ' :')
        self.assertIn('pose proof(QPpre_nonempty enabled si ci nest c old)', src)
        self.assertIn('exact(proj1(proj2 BIvalid))', src)
        ctl = statement(src, 'BIie_control')
        self.assertIn('BIlogic true', ctl)
        self.assertIn('BIlogic false', ctl)
        self.assertIn('apply astar_l_aie_elim in IE as[E _]. discriminate.', src)
        self.assertIn('BuildPreI', statement(src, 'BIarity_control'))
        self.assertIn('=None', statement(src, 'BIarity_control'))
        self.assertIn('=Some(BIpost lg t)', statement(src, 'BIreturn_arity_observation'))
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
