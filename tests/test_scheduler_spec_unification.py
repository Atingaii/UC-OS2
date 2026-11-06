"""结构回归；语义结论只依赖实际 Coq 内核核验，不冒充语义 TDD。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage214-scheduler-spec-unification'
SOURCES = {
    'embedding': 'certiucos/v293/proofs/V293SpecEmbedding.v',
    'joint': 'certiucos/v293/proofs/V293OSSchedJoint.v',
    'body': 'certiucos/v293/proofs/V293OSIntExitAllInternal.v',
    'probe': 'audit/probes/V293OSIntExitAllInternalProbe.v',
}

def read(name):
    return json.loads((D / name).read_text())

def statement(src, name):
    return src.split(name + ' :', 1)[1].split('Proof.', 1)[0]

class SchedulerSpecUnificationTests(unittest.TestCase):
    def test_frozen_source_and_prospective_protocol(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        self.assertEqual([x['function']['name'] for x in source['functions']],
                         ['OSIntEnter', 'OSIntExit', 'OS_SchedNew'])
        for row in source['functions']:
            self.assertTrue(row['reconstructed_repaired_source_matches'])
            self.assertEqual(hashlib.sha256((D / (row['function']['name'] + '.configured.c.txt')).read_bytes()).hexdigest(),
                             row['function']['preprocessed_definition_sha256'])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])
        for p, h in source['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
        old = R / 'audit/logs/stage213-interrupt-exit-changed-builders/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_exact_embedding_bounded_to_void_calls(self):
        src = (R / SOURCES['embedding']).read_text()
        stmt = statement(src, 'V293_InfRules_spec_embedding')
        self.assertIn('V293_void_calls body', stmt)
        self.assertIn('InfRules source sd li Inv r ri p body q t', stmt)
        self.assertIn('InfRules target sd li Inv r ri p body q t', stmt)
        self.assertIn('| scalle _ _ _ => False', src)
        self.assertIn('induction H;', src)
        self.assertIn('getasrt(pre\' vl (embed lg) t)=getasrt(pre vl lg t)', src)
        self.assertIn('getasrt(post\' vl result (embed lg) t)=getasrt(post vl result lg t)', src)
        self.assertIn('eapply call_rule', src)
        self.assertNotIn('retpost', src.split('Definition V293_spec_embedding', 1)[1])

    def test_common_actual_body_builders_and_one_environment(self):
        src = (R / SOURCES['body']).read_text()
        stmt = statement(src, 'V293_OSIntExit_all_builder_contract')
        self.assertEqual(stmt.count('InfRules'), 1)
        for token in ('Spec sched_id=Some(jfp,jfq,(Tvoid,nil))', 'BuildPreI P f vl lg',
                      'BuildRetI P f vl lg', 'V293_scheduler V293_shared_li Inv0',
                      'V293_interrupt_handoff high current target'):
            self.assertIn(token, stmt)
        for token in ('V293_InfRules_spec_embedding', 'V293_critical_to_joint', 'V293_ISR_to_joint',
                      'V293_OSIntExit_changed_builder_contract', 'V293_OSIntExit_unified_builder_contract',
                      'V293_all_exit_env_WFFunEnv', 'V293_all_exit_env_WFIFun',
                      'V293_OSSchedNew_joint_contract', 'V293_OSIntEnter_internal_contract'):
            self.assertIn(token, src)
        self.assertNotIn('CertiOS.audit.', src)
        joint = (R / SOURCES['joint']).read_text()
        stmt = statement(joint, 'V293_OSSchedNew_joint_contract')
        self.assertEqual(stmt.count('InfRules'), 1)
        self.assertIn('BuildPreI', stmt)
        self.assertIn('BuildRetI', stmt)
        self.assertIn('V293_resource_OSSchedNew_critical_contract', joint)
        self.assertIn('V293_OSSchedNew_ISR_contract', joint)

    def test_independent_nonempty_entries_and_single_tag_control(self):
        src = (R / SOURCES['probe']).read_text()
        for name in ('ACenvironment', 'ACbuilders', 'ACchanged_nonempty', 'ACactual_contract',
                     'AQquiet_nonempty', 'AQsame_nonempty', 'AJcritical_exact', 'AJISR_nonempty',
                     'AJtag_control', 'AJtag_rejects_same_state', 'AJvalue_call_excluded', 'AJactual_body_accepted'):
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r' :')
        for token in ('apply CBpre_owned', 'apply UBquiet_pre_nonempty', 'apply UBsame_pre_nonempty',
                      'apply QSselector_nonempty'):
            self.assertIn(token, src)
        self.assertIn('Some(false,QSlg nil)', statement(src, 'AJtag_control'))
        self.assertIn('Some(true,QSlg nil)', statement(src, 'AJtag_control'))
        self.assertIn('=Afalse', statement(src, 'AJtag_control'))
        self.assertNotIn('cstepstar', src)

    def test_stable_compiles_and_recursive_kernel_check(self):
        roots = []
        for kind, p in SOURCES.items():
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
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
