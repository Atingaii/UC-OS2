"""结构回归只约束本步证据；实际 Hoare 证明由 Coq 核验。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage213-interrupt-exit-changed-builders'
PROD = 'certiucos/v293/proofs/V293OSIntExitChangedInternal.v'
PROBE = 'audit/probes/V293OSIntExitChangedInternalProbe.v'

def read(n):
    return json.loads((D / n).read_text())

def statement(src, name):
    return src.split(name + ' :', 1)[1].split('Proof.', 1)[0]

class InterruptExitChangedBuildersTests(unittest.TestCase):
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
        old = R / 'audit/logs/stage212-interrupt-exit-changed-body/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_actual_builders_one_body_no_oracle(self):
        src = (R / PROD).read_text()
        stmt = statement(src, 'V293_OSIntExit_changed_builder_contract')
        self.assertEqual(stmt.count('InfRules'), 1)
        for token in ('BuildPreI P f vl lg', 'BuildRetI P f vl lg',
                      'V293_exit_boundary_function running nesting lock saved',
                      'V293_exit_boundary_body running nesting lock saved', 'GoodFrm extra'):
            self.assertIn(token, stmt)
        for token in ('evalval', 'evaltype'):
            self.assertNotIn(token, stmt)
        for token in ('apply V293_OSIntExit_changed_body', 'V293_changed_builder_unpack',
                      'apply V293_changed_builder_pack', 'apply V293_exit_builder_names',
                      'apply V293_changed_builder_high_binding'):
            self.assertIn(token, src)
        self.assertNotIn('CertiOS.audit.', src)

    def test_good_external_assertions_post_without_shared_snapshot(self):
        src = (R / PROD).read_text()
        memory = src.split('Definition V293_changed_builder_memory t:=', 1)[1].split('Lemma V293_changed_builder_memory_good', 1)[0]
        for token in ('A_notin_lenv', 'Alvarenv', 'V293_exit_builder_domain'):
            self.assertNotIn(token, memory)
        for token in ('V293_changed_builder_memory_good', 'V293_changed_builder_external_good',
                      'V293_changed_builder_post_good', '@mkfunasrt'):
            self.assertIn(token, src)
        post = src.split('Definition V293_changed_builder_post t(result:option val):=', 1)[1].split('Lemma', 1)[0]
        self.assertIn('SWINVt V293_changed_builder_inv t', post)
        self.assertNotRegex(post, r'\b(?:tasks|events|now|nc|hv|out|lo|hi|c)\b')
        self.assertIn('length entries', src.split('Definition V293_changed_builder_inv:=', 1)[1].split('Definition V293_changed_builder_valid', 1)[0])
        self.assertIn('OS[(fun _:hid=>false),false,si,ci]', memory)

    def test_independent_nonempty_actual_instance_arity_and_shadow_control(self):
        src = (R / PROBE).read_text()
        for name in ('CBbuilders', 'CBenv_owned', 'CBresources_owned', 'CBpre_owned',
                     'CBentry_nonempty', 'CBzero_max_entry', 'CBactual_contract',
                     'CBarity_control', 'CBreturn_arity_observation', 'CBrenamed_pre', 'CBshadow_control'):
            self.assertRegex(src, r'(?:Theorem|Lemma) ' + name + ' :')
        pre = src.split('Theorem CBpre_owned :', 1)[1].split('Theorem CBentry_nonempty', 1)[0]
        self.assertIn('CBresources_owned nest c old', pre)
        self.assertNotIn('V293_OSIntExit_changed_builder_contract', pre)
        self.assertIn('eapply V293_OSIntExit_changed_builder_contract', src)
        self.assertEqual(statement(src, 'CBactual_contract').count('InfRules'), 1)
        arity = statement(src, 'CBarity_control')
        self.assertIn('BuildPreI', arity)
        self.assertIn('=None', arity)
        self.assertIn('=Some(CBpost saved aop)', statement(src, 'CBreturn_arity_observation'))
        control = statement(src, 'CBshadow_control')
        for token in ('BuildPreI(CBprogram 114%Z', 'CBpre 117%Z', 'CBpre 114%Z',
                      'getmem(CXstate', 'Some(13%positive,Tint8)', 'Some(16%positive,Tint32)',
                      '~(CBrenamed_state', 'V293_handoff_binding 114%Z 13%positive'):
            self.assertIn(token, control)
        self.assertIn('good_fun_asrt_absop', src)
        self.assertIn('Int.repr Int.max_unsigned', src)
        for token in ('V293_global_steps', 'cstepstar'):
            self.assertNotIn(token, src)

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
