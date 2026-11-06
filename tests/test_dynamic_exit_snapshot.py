"""结构回归；语义结论来自 Coq 内核，不冒充语义 TDD。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage215-dynamic-exit-snapshot'
SOURCES = {'body': 'certiucos/v293/proofs/V293OSIntExitDynamic.v',
           'probe': 'audit/probes/V293OSIntExitDynamicProbe.v'}

def read(name):
    return json.loads((D / name).read_text())

def statement(src, name):
    return src.split(name + ' :', 1)[1].split('Proof.', 1)[0]

class DynamicExitSnapshotTests(unittest.TestCase):
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
        old = R / 'audit/logs/stage214-scheduler-spec-unification/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_dynamic_codec_and_static_layout(self):
        src = (R / SOURCES['body']).read_text()
        for token in ('V293_clo', 'V293_chi', 'V293_ccurrent', 'V293_cnest', 'V293_centries',
                      'V293_ctasks', 'V293_cevents', 'V293_cnow', 'V293_chigh', 'V293_cout',
                      'V293_ccounter', 'V293_caop', 'V293_cstack', 'V293_ccritical'):
            self.assertIn(token, src.split('Definition V293_changed_encode', 1)[0])
        self.assertIn('V293_changed_decode(V293_changed_encode x)=Some x',
                      statement(src, 'V293_changed_codec_roundtrip'))
        self.assertIn('V293_changed_encode x=V293_changed_encode y ->x=y',
                      statement(src, 'V293_changed_encode_injective'))
        self.assertIn('length entries=table_length', statement(src, 'V293_dynamic_exit_inv_length'))
        self.assertIn('[|length(V293_centries x)=table_length|]', src)
        self.assertIn('apply pure_split_rule;intro Length', src)
        self.assertNotIn('Variable tasks', src)
        self.assertNotIn('Variable c:', src)
        self.assertNotIn('CertiOS.audit.', src)

    def test_actual_builders_body_and_one_environment(self):
        src = (R / SOURCES['body']).read_text()
        stmt = statement(src, 'V293_OSIntExit_dynamic_builder_contract')
        self.assertEqual(stmt.count('InfRules'), 1)
        for token in ('Spec sched_id=Some(jfp,jfq,(Tvoid,nil))', 'BuildPreI P f vl lg',
                      'BuildRetI P f vl lg', 'V293_scheduler V293_shared_li Inv0',
                      'V293_interrupt_handoff high current target'):
            self.assertIn(token, stmt)
        for token in ('V293_OSIntExit_changed_builder_contract', 'V293_OSIntExit_unified_builder_contract',
                      'V293_InfRules_spec_embedding', 'V293_critical_to_joint', 'V293_ISR_to_joint',
                      'V293_OSSchedNew_joint_contract', 'V293_OSIntEnter_internal_contract',
                      'V293_dynamic_exit_env_WFFunEnv', 'V293_dynamic_exit_env_WFIFun'):
            self.assertIn(token, src)

    def test_nonempty_memory_and_valid_codec_counter_control(self):
        src = (R / SOURCES['probe']).read_text()
        for name in ('DPenvironment', 'DPbuilders', 'DPactual_contract', 'DPchanged_nonempty',
                     'DPpre_reduces', 'DPcounter_load', 'DPcounter_dynamic_control',
                     'DPmalformed', 'DQquiet_nonempty', 'DQsame_nonempty'):
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r' :')
        stmt = statement(src, 'DPcounter_dynamic_control')
        self.assertEqual(stmt.count('V293_changed_decode('), 2)
        self.assertIn('Int.max_unsigned', stmt)
        self.assertIn('~(CXstate', stmt)
        self.assertIn('load Tint32(getmem st)(12%positive,0%Z)=Some(Vint32 c)',
                      statement(src, 'DPcounter_load'))
        for token in ('CBpre_owned', 'apply UBquiet_pre_nonempty', 'apply UBsame_pre_nonempty',
                      'rewrite A in W;vm_compute in W;discriminate'):
            self.assertIn(token, src)
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
