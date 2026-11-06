"""调用点抽象与真实 switch 的结构回归；语义依据是 Coq，而不是文本断言。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage200-interrupt-switch-boundary'
PROD = 'certiucos/v293/proofs/V293OSIntExitBoundarySwitch.v'
PROBE = 'audit/probes/V293OSIntExitBoundarySwitchProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return src.split(name + ' :', 1)[1].split('Proof.', 1)[0]


class InterruptBoundarySwitchTests(unittest.TestCase):
    def test_exact_source_and_frozen_protocol(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        self.assertEqual([x['function']['name'] for x in source['functions']], ['OSIntExit', 'OS_SchedNew'])
        for x in source['functions']:
            self.assertTrue(x['reconstructed_repaired_source_matches'])
            self.assertTrue(x['temporary_source_removed_on_context_exit'])
            self.assertEqual(hashlib.sha256((D / (x['function']['name'] + '.configured.c.txt')).read_bytes()).hexdigest(),
                             x['function']['preprocessed_definition_sha256'])
        for p, h in source['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
            self.assertEqual(h, read('baseline.json')['files'][p])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(), read('protocol-identity.json')['protocol.json'])
        old = R / 'audit/logs/stage199-interrupt-global-entry/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_fixed_handoff_actual_switch_and_no_execution_oracle(self):
        src = (R / PROD).read_text()
        stmt = statement(src, 'V293_OSIntExit_boundary_switch')
        pre = stmt.split('exists bs next nh Me Ms Mf,', 1)[0]
        for token in ('cstepstar', 'V293_global_steps', 'V293_local_steps', 'store ', 'free ',
                      'evalval', 'fresh M', 'InOS', 'handoff ->'):
            self.assertNotIn(token, pre)
        for token in ('get T ct=Some', 'get les ct=Some caller', 'get aus ct=Some(enabled,si,ci)',
                      'get ge OSTCBCur=Some(bcur,Tptr V293_tcb_type)',
                      'exists C le aux,get T t=Some C /\\ get les t=Some le /\\ get aus t=Some aux',
                      'if sync then V293_interrupt_handoff high current target else sprim(switch target)',
                      '(T,(ge,les,M,ir,aus),ct)', 'set aus ct(false,si,enabled::ci)),next)',
                      'kseq(sprim excrit)(kseq sret(kcall f', 'kint interrupted ike interrupted_le ks',
                      'V293_cache_current tasks next Mf bc <-> sync=true',
                      'store(Tptr V293_tcb_type)Ms(bcur,0%Z)(Vptr next)=Some Mf'):
            self.assertIn(token, stmt)
        for token in ('V293_exit_boundary_entry_global', 'V293_handoff_copy_execution',
                      'V293_interrupt_local_steps_global', 'V293_ready_switch_cache',
                      'V293_global_trans', 'map_get_set\' by congruence'):
            self.assertIn(token, src)
        self.assertNotIn('CertiOS.audit.', src)

    def test_independent_nonempty_fixture_and_both_initial_ie(self):
        src = (R / PROBE).read_text()
        for token in ('Definition BXge := set SXge OSTCBCur(1%positive,Tptr V293_tcb_type)',
                      'Lemma BXready :', 'Lemma BXentry :', 'Lemma BXindependent_entry :',
                      '(BXdomain other otherle otheraux enabled ci)', '(BXindependent_entry ci)',
                      'Lemma BXother_maps :', 'Lemma BXcommon_pointer_types :',
                      'BXcomplete_switch sync false ci other otherle otheraux cst',
                      'BXcomplete_switch sync true ci other otherle otheraux cst'):
            self.assertIn(token, src)
        stmt = statement(src, 'BXboth_IE_complete')
        self.assertEqual(stmt.count('V293_global_steps(BXglobal sync)cst'), 2)
        self.assertEqual(stmt.count('(GXtasks other,(BXge,GXenvs otherle,SXmemory 1 6,'), 2)
        for token in ('false::ci', 'true::ci', 'get M0(b0,Z.of_nat k)', 'get M1(b1,Z.of_nat k)',
                      'load Tint8 M0(99%positive,0%Z)', 'load Tint8 M1(100%positive,0%Z)', 'Int.repr 20'):
            self.assertIn(token, stmt)

    def test_single_factor_full_switch_ablation_and_separate_raw_model(self):
        src = (R / PROBE).read_text()
        stmt = statement(src, 'BXcopy_ablation')
        self.assertEqual(stmt.count('V293_global_steps(BXglobal'), 2)
        self.assertEqual(stmt.count('(GXtasks other,(BXge,GXenvs otherle,SXmemory 1 6,'), 2)
        for token in ('BXglobal true', 'BXglobal false', 'Some(Vptr OwnershipReady)',
                      'load Tint8 M0(96%positive,0%Z)=Some(V293_byteval 4)',
                      'load Tint8 M1(96%positive,0%Z)=Some(V293_byteval 6)',
                      '~V293_cache_current OwnershipTasks OwnershipReady M1 96%positive'):
            self.assertIn(token, stmt)
        for token in ('Lemma BXprogram_only_callsite :', 'BXcomplete_switch true enabled ci',
                      'BXcomplete_switch false enabled ci', 'Theorem BXraw_port_still_stuck :',
                      'eapply V293_missing_port_disabled_no_global_step', 'exact SXswitch_lookup_absent',
                      'Lemma BXnormalization :', 'Lemma BXreject_nonempty_args :',
                      'Lemma BXreject_value_call :', 'Lemma BXreject_runtime :', '(sfree nil None)=None'):
            self.assertIn(token, src)
        prod = (R / PROD).read_text()
        for token in ('Fixpoint V293_intswitch_calls', '| sfexec _ _ _ | salloc _ _ | sfree _ _ =>None',
                      'V293_OSIntExit_abstract_normalization'):
            self.assertIn(token, prod)

    def test_stable_compiles_dynamic_roots_and_no_new_holes(self):
        stable = read('stable-compiles.json')
        roots = []
        for kind, p in (('body', PROD), ('probe', PROBE)):
            src = (R / p).read_text()
            row = read(stable[kind] + '.json')
            h = hashlib.sha256((R / p).read_bytes()).hexdigest()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(h, row['initial_source_sha256'])
            self.assertEqual(h, row['source_sha256'])
            self.assertEqual(h, hashlib.sha256((D / (stable[kind] + '.v.snapshot.txt')).read_bytes()).hexdigest())
            self.assertNotRegex(src, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', src, re.M)]
        trust = read('trust.json')
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
        self.assertTrue(all(x['exit'] == 0 for x in trust['commands']))
