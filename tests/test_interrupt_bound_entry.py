"""入口连接的来源/结构回归；语义由 Coq 和递归 coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage244-bound-dispatch-entry'
SOURCES = {'entry': 'certiucos/v293/proofs/V293InterruptBoundEntry.v',
           'probe': 'audit/probes/V293InterruptBoundEntryProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class BoundEntryTests(unittest.TestCase):
    def test_fixed_source_and_protocol(self):
        s = read('source-check.json')
        self.assertTrue(s['passed'])
        self.assertEqual([x['function']['name'] for x in s['functions']],
                         ['OSIntEnter', 'OSIntExit', 'OS_SchedNew', 'OS_Sched'])
        for p, h in s['files'].items():
            self.assertEqual(sha(R / p), h)
        self.assertEqual(s['previous_manifest_sha256'],
                         '23ba6611c41c5fb2a0d0405ed2970f3c13b12f85ea11d98cb30c84a8cdbbb782')
        self.assertEqual(sha(D / 'protocol.json'), read('protocol-identity.json')['protocol.json'])
        for x in s['functions']:
            self.assertEqual(sha(D / (x['function']['name'] + '.configured.c.txt')),
                             x['function']['preprocessed_definition_sha256'])

    def test_actual_builder_direction_and_resource_closure(self):
        src = (R / SOURCES['entry']).read_text()
        for path in ['changed', 'same']:
            header = src.split('Theorem V293_' + path + '_entry_BuildintPre :', 1)[1].split('Proof.', 1)[0]
            self.assertIn('Some pre=BuildintPre 0 intspec ir si Inv0 li t nil', header)
            self.assertIn(path + ' nest aop(isrupd ir 0 true)(0::si)t ==>pre', header)
            for token in ['V293_ready_rel', 'Forall', 'nc<256', 'nest<256',
                          'rule_type_val_match Tint8 hv=true', 'rule_type_val_match(Tptr tp)out=true']:
                self.assertIn(token, header)
            self.assertNotIn('InfRules', header)
            self.assertNotIn('Agvarenv', header)
        for token in ['V293_retained_arrays_ready', 'V293_storage_byte_close',
                      'V293_storage_append', 'V293_irq_bound_snapshot_pack',
                      'V293_outer_active_isr_inv', 'V293_outer_entry_pre']:
            self.assertIn(token, src)
        self.assertNotIn('InfRules', src)
        old = read('baseline.json')['files']
        for p in ['framework/logic/inferules.v',
                  'certiucos/v293/proofs/V293InterruptBoundDispatchContinuous.v',
                  'certiucos/v293/proofs/V293InterruptBindings.v',
                  'certiucos/v293/proofs/V293OSIntExitBoundDynamic.v']:
            self.assertEqual(sha(R / p), old[p])

    def test_same_state_and_single_factor_operation(self):
        src = (R / SOURCES['probe']).read_text()
        for label, entry, state, pre, wrapper in [
                ('BEchanged', 'CCentry', 'CCstate', 'BCpre', 'BCactual_wrapper'),
                ('BEsame', 'SCentry', 'SCirq_state', 'BSpre', 'BSactual_wrapper')]:
            section = src.split('Theorem ' + label + '_same_state :', 1)[1].split('Qed.', 1)[0]
            self.assertIn(state + ' M O|=' + entry, section)
            self.assertIn(state + ' M O|=' + pre, section)
            self.assertIn('InfRules BDspec V293_scheduler LDli RDinv', section)
            self.assertIn('apply ' + wrapper, section)
            control = src.split('Theorem ' + label + '_operation_control :', 1)[1].split('Qed.', 1)[0]
            self.assertIn('BuildintPre', control)
            self.assertIn('~' + state + ' M O|=' + label + '_wrong', control)
            self.assertIn('apply BEbuilder_operation in Wrong;discriminate', control)
        a = read('operation-ablation.json')
        self.assertFalse(a['two_executions'])
        self.assertEqual(a['proof_source_sha256'], sha(R / SOURCES['probe']))
        self.assertEqual(read(a['compile'] + '.json')['exit'], 0)

    def test_import_ablation_and_bounded_claims(self):
        a = read('import-ablation.json')
        bodies = []
        for phase in ['before', 'after']:
            label = a[phase + '_compile']
            self.assertEqual(read(label + '.json')['exit'], 0)
            raw = (D / (label + '.v.snapshot.txt')).read_bytes()
            self.assertEqual(hashlib.sha256(raw).hexdigest(), a[phase + '_source_sha256'])
            bodies.append(b''.join(x for x in raw.splitlines(keepends=True)
                                   if not x.startswith(b'Require Import ')))
        self.assertEqual(bodies[0], bodies[1])
        self.assertEqual(len(a['removed_imports']), 5)
        self.assertEqual(read('entry12.json')['exit'], 1)
        self.assertEqual(read('entry13.json')['exit'], 1)
        for p, h in read('adversarial-review.json')['source_sha256'].items():
            self.assertEqual(sha(R / p), h)
        doc = (R / 'audit/STAGE244_BOUND_DISPATCH_ENTRY.md').read_text()
        for text in ['不是所有 BuildintPre', '不是 `WFInt`', '不是 `GOOD_OS`',
                     '不是初始化可达', '不是两次完整执行', 'uCOS3 未开始',
                     '旧423失败、1错误', '单向蕴含', 'all-clear']:
            self.assertIn(text, doc)

    def test_independent_roots_and_stable_sources(self):
        roots = []
        for kind, p in SOURCES.items():
            src = (R / p).read_text()
            label = read('stable-compiles.json')[kind]
            row = read(label + '.json')
            self.assertEqual(row['exit'], 0)
            self.assertEqual(sha(R / p), row['initial_source_sha256'])
            self.assertEqual(sha(R / p), row['source_sha256'])
            self.assertEqual(sha(R / p), sha(D / (label + '.v.snapshot.txt')))
            self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
            if kind != 'probe':
                self.assertNotIn('CertiOS.audit.', src)
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', src, re.M)]
        t = read('trust.json')
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 14)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in t['commands']))
        self.assertTrue(set(t['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
