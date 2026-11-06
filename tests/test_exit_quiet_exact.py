"""quiet 精确资源的结构与身份回归；语义由 Coq 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage230-exit-quiet-exact'
SOURCES = {'quiet': 'certiucos/v293/proofs/V293OSIntExitQuietExact.v',
           'dynamic': 'certiucos/v293/proofs/V293OSIntExitQuietExactDynamic.v',
           'probe': 'audit/probes/V293OSIntExitQuietExactProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


class ExitQuietExactTests(unittest.TestCase):
    def test_source_and_prospective_protocol_identity(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        self.assertEqual([x['function']['name'] for x in source['functions']],
                         ['OSIntEnter', 'OSIntExit', 'OS_SchedNew', 'OS_Sched'])
        for row in source['functions']:
            self.assertEqual(hashlib.sha256((D / (row['function']['name'] + '.configured.c.txt')).read_bytes()).hexdigest(),
                             row['function']['preprocessed_definition_sha256'])
        for p, h in source['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])
        self.assertEqual(source['previous_manifest_sha256'],
                         '19018e4df778f5f1ce5756c6f2bed760d75a4881d65fb761239d1df8c300874f')

    def test_stable_compiles_and_recursive_trust(self):
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
            self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
            if kind != 'probe':
                self.assertNotIn('CertiOS.audit.', src)
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', src, re.M)]
        trust = read('trust.json')
        self.assertTrue(trust['passed'])
        self.assertTrue(trust['recursive'])
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))
        self.assertEqual(trust['single_factor_local_assertion_boundary_control'],
                         'V293OSIntExitQuietExactProbe.Qlocal_control')

    def test_real_quiet_body_exact_local_and_original_codec(self):
        src = (R / SOURCES['quiet']).read_text()
        for token in ['p_local li t nil ** extra', 'V293_OSIntExit_nondispatch_body',
                      'V293_quiet_exit_index', 'V293_quiet_exit_valid',
                      'V293_quiet_builder_names', 'V293_quiet_forget_names',
                      'V293_exact_local_weakens', 'BuildPreI', 'BuildRetI']:
            self.assertIn(token, src)
        self.assertNotIn('CurLINV li t ** extra', src)
        dynamic = (R / SOURCES['dynamic']).read_text()
        for token in ['Some(false,args)=>match V293_exit_path args with',
                      'Some(true,qlg)=>qfp', 'Some(true,qlg)=>qfq',
                      'V293_quiet_exact_dynamic_changed_kept', 'V293_quiet_exact_dynamic_same_kept',
                      'V293_OSIntExit_exact_dynamic_builder_contract',
                      'V293_OSIntExit_quiet_exact_builder_contract']:
            self.assertIn(token, dynamic)

    def test_one_program_spec_inv_and_real_call(self):
        src = (R / SOURCES['dynamic']).read_text()
        for token in ['WFFunEnv(V293_ready_irq_unit', 'WFIFun(V293_ready_irq_unit',
                      'Let Inv0:=V293_ready_dynamic_exit_inv', 'eapply call_rule',
                      'V293_OSIntEnter_local_contract', 'V293_OSSchedNew_exact_joint_contract',
                      'V293_OSIntExit_quiet_exact_dynamic_contract']:
            self.assertIn(token, src)
        probe = (R / SOURCES['probe']).read_text()
        for token in ['WFFunEnv RDprogram Qspec', 'InfRules Qspec', 'forall RI,',
                      'getasrt(Qfq nil result Qlg OwnershipWaiting)=[|result=None|] ** Qexternal 1',
                      'Qstate Qmemory |=Qpre', 'Theorem Qcall_entry_nonempty']:
            self.assertIn(token, probe)

    def test_nonempty_fixture_and_bounded_control_claims(self):
        src = (R / SOURCES['probe']).read_text()
        self.assertIn('Proof. apply RLlocal_exactness_control. Qed.', src)
        self.assertIn('Definition Qmemory:=merge', src)
        self.assertNotIn('Atrue', src)
        for name in ['Qcurrent_owned', 'Qspatial', 'Qentry_nonempty', 'Qactual_contract', 'Qactual_call']:
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        doc = (R / 'audit/STAGE230_EXIT_QUIET_EXACT.md').read_text()
        for token in ['quiet 的新前置也更强', '不是初始化可达', '不是两次完整执行',
                      '不声称语义 TDD', 'same 仍弱', '常 Aemp', '五块']:
            self.assertIn(token, doc)
