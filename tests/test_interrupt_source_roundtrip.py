"""中断现场来源连接的结构回归；执行语义由独立 Coq 根核验。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage202-interrupt-source-roundtrip'
PROD = 'certiucos/v293/proofs/V293InterruptSourceRoundtrip.v'
PROBE = 'audit/probes/V293InterruptSourceRoundtripProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return src.split(name + ' :', 1)[1].split('Proof.', 1)[0]


class InterruptSourceRoundtripTests(unittest.TestCase):
    def test_exact_three_sources_and_prospective_protocol(self):
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
        old = R / 'audit/logs/stage201-interrupt-resumed-return/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_real_entry_complete_calls_and_return_without_trace_oracle(self):
        src = (R / PROD).read_text()
        stmt = statement(src, 'V293_interrupt_source_roundtrip')
        pre = stmt.split('exists bs Mf,', 1)[0]
        for token in ('cstepstar', 'V293_global_steps', 'V293_local_steps', 'store ',
                      'free ', 'evalval', 'fresh M', 'InOS', 'kint'):
            self.assertNotIn(token, pre)
        for token in ('get T ct=Some(interrupted,(ike,ks))', 'get les ct=Some interrupted_le',
                      'Some((true,si,nil):localst)', 'higherint ir i', 'i<INUM',
                      'ip i=Some(V293_irq_source_wrapper entry f vector)',
                      'P entry=Some(V293_OSIntEnter_function running nesting)',
                      'V293_highest_ready tasks ct', '(false,i::si,nil)',
                      '(T,(ge,les,Mf,ir,aus),ct)', 'get Mf(bs,Z.of_nat k)=None'):
            self.assertIn(token, stmt)
        for token in ('eapply pint_step', 'eapply li_step', 'V293_OSIntEnter_zero_call',
                      'V293_OSIntExit_same_task_call_execution', 'V293_interrupt_local_steps_global',
                      'eapply exint_step;reflexivity', 'TasksMod.get_set_same Code',
                      'CltEnvMod.get_set_same Env', 'TaskLStMod.get_set_same Aux'):
            self.assertIn(token, src)
        self.assertNotIn('CertiOS.audit.', src)

    def test_nonempty_source_fixture_restored_context_free_and_canaries(self):
        src = (R / PROBE).read_text()
        for token in ('SXindependent_entry', 'FXentry 0 4', 'SX_ready_stack',
                      'SX_context FXframe', 'V293_ready_core_aux', 'SXmerge',
                      'keop1 negation Tint32 kenil', 'set emp FXct FXcaller',
                      'SXip 1=Some SXwrapper', '(RIfixed_tasks FXct)FXcurrent FXhighest',
                      '(FXlookup 0 4)SXindependent_entry', 'SXcomplete_roundtrip cst'):
            self.assertIn(token, src)
        stmt = statement(src, 'SXroundtrip_canaries')
        self.assertEqual(stmt.count('SXaus true'), 2)
        for token in ('Some(V293_byteval 0)', 'Some(Vptr OwnershipReady)',
                      'get Mf(bs,Z.of_nat k)=None', 'Some(Vint32(Int.repr 19))',
                      'Some(V293_byteval 99)', 'Some(V293_byteval 23)'):
            self.assertIn(token, stmt)
        # No general GoodInvAsrt-to-ISR-stack transport shortcut.
        self.assertNotIn('GoodInvAsrt', statement(src, 'SX_ready_stack'))
        self.assertIn('SX_context R', statement(src, 'SX_ready_stack'))

    def test_ie_boundary_and_executed_eoi_only_prefix_control(self):
        src = (R / PROBE).read_text()
        self.assertIn('lpstep SXp SXT', statement(src, 'SXenabled_actual_entry'))
        self.assertIn('~lintstep SXip SXcode', statement(src, 'SXdisabled_no_interrupt'))
        self.assertIn('forall t,t<>FXct', statement(src, 'SXonly_IE_changed'))
        stmt = statement(src, 'SXeoi_prefix_control')
        for token in ('forall clear cst', 'V293_global_steps(SXcontrol_p clear)cst',
                      'SXaus true', 'set SXT FXct SXprefix_code', 'FXmemory 0 4',
                      'SXprefix_ir clear', 'FXct(false,[1],nil)'):
            self.assertIn(token, stmt)
        stmt = statement(src, 'SXeoi_only_effect')
        for token in ('SXcontrol_p true=SXp', 'SXcontrol_handler false=sseq(sskip None)SXcalls',
                      'SXprefix_ir true 1=false', 'SXprefix_ir false 1=true'):
            self.assertIn(token, stmt)
        self.assertIn('eapply V293_interrupt_source_enter', src)
        self.assertIn('eapply eoi_step', src)
        self.assertIn('Only EOI is neutralized, before either complete call', src)

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
