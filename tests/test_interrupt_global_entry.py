"""已有中断现场的全局前缀；结构回归不替代 Coq 的语义检查。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage199-interrupt-global-entry'
PROD = 'certiucos/v293/proofs/V293OSIntExitInterruptGlobal.v'
PROBE = 'audit/probes/V293OSIntExitInterruptGlobalProbe.v'


def read(name):
    return json.loads((D / name).read_text())


class InterruptGlobalEntryTests(unittest.TestCase):
    def test_exact_sources_and_frozen_protocol(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        self.assertEqual([f['function']['name'] for f in source['functions']], ['OSIntExit', 'OS_SchedNew'])
        for f in source['functions']:
            self.assertTrue(f['reconstructed_repaired_source_matches'])
            self.assertTrue(f['temporary_source_removed_on_context_exit'])
            self.assertEqual(hashlib.sha256((D / (f['function']['name'] + '.configured.c.txt')).read_bytes()).hexdigest(),
                             f['function']['preprocessed_definition_sha256'])
        for p, h in source['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
            self.assertEqual(h, read('baseline.json')['files'][p])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(), read('protocol-identity.json')['protocol.json'])
        old = R / 'audit/logs/stage198-interrupt-switch-entry/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_main_binds_existing_maps_without_execution_or_classification_oracle(self):
        src = (R / PROD).read_text()
        stmt = src.split('Theorem V293_OSIntExit_interrupt_switch_entry :', 1)[1].split('Proof.', 1)[0]
        pre = stmt.split('exists bs next nh Mf,', 1)[0]
        for token in ('loststep', 'cstepstar', 'V293_local_steps', 'V293_global_steps',
                      'store ', 'free ', 'evalval', 'InOS', 'fresh M'):
            self.assertNotIn(token, pre)
        for token in ('get T ct=Some', 'get les ct=Some caller', 'get aus ct=Some',
                      'goodks(pc,(po,pi,ip))ks', 'V293_global_steps(pc,(po,pi,ip))cst',
                      '(T,(ge,les,M,ir,aus),ct)', 'kint interrupted ike interrupted_le ks',
                      'set aus ct(false,si,enabled::ci)', 'sfexec int_switch nil nil'):
            self.assertIn(token, stmt)
        for token in ('V293_OSIntExit_switch_entry_execution', 'loststep_cont_locality',
                      'V293_interrupt_enclosing_inos', 'V293_interrupt_enclosing_not_no_os',
                      'ltstep_goodks', 'eapply pt_step', 'V293_global_endpoint_other_tasks'):
            self.assertIn(token, src)
        self.assertNotIn('CertiOS.audit.', src)

    def test_nonempty_complete_prefix_both_ie_and_other_task_frame(self):
        src = (R / PROBE).read_text()
        for token in ('Theorem GXcomplete_global_prefix :', 'V293_OSIntExit_interrupt_switch_entry',
                      'GXmerge(GXcode other)(GXenv otherle)(GXaux_current enabled ci otheraux)I',
                      '(SXindependent_entry ci)', 'GXcomplete_global_prefix false ci other otherle otheraux cst',
                      'GXcomplete_global_prefix true ci other otherle otheraux cst',
                      'Lemma GXother_maps :', 'Theorem GXnonempty_other_task_frame :',
                      'Some GXother', 'Some SXcaller', 'Some(true,[1],nil)',
                      'get SXcaller 601%Z=Some(99%positive,Tint8)'):
            self.assertIn(token, src)
        stmt = src.split('Theorem GXboth_IE_complete_global :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(stmt.count('V293_global_steps GXprogram cst'), 2)
        self.assertEqual(stmt.count('GXtasks other,(SXge,GXenvs otherle,SXmemory 1 6,'), 2)
        for token in ('GXaux false ci otheraux', 'GXaux true ci otheraux', 'cons false ci', 'cons true ci',
                      'Int.repr 20', 'get M0(b0,Z.of_nat k)', 'get M1(b1,Z.of_nat k)',
                      'load Tint8 M0(99%positive,0%Z)', 'load Tint8 M1(100%positive,0%Z)'):
            self.assertIn(token, stmt)

    def test_global_dead_end_and_only_ie_boundary_control(self):
        prod = (R / PROD).read_text()
        stmt = prod.split('Theorem V293_missing_port_disabled_no_global_step :', 1)[1].split('Proof.', 1)[0]
        for token in ('Some(false,si,ci)', 'InOS', 'pumerge po pi port=None',
                      '~exists T\' cst\' S\' t\'', 'lpstep(pc,(po,pi,ip))'):
            self.assertIn(token, stmt)
        src = (R / PROBE).read_text()
        for token in ('Theorem GXprefix_endpoint_stuck :', 'GXboundary_disabled_stuck',
                      'GXboundary_enabled_interrupt', 'GXonly_IE_changed',
                      'Definition GXboundary_aux enabled otheraux',
                      'set(GXaux false nil otheraux)SXct(enabled,nil,nil)',
                      'GXboundary_aux false otheraux', 'GXboundary_aux true otheraux',
                      'eapply pint_step', 'eapply li_step with(i:=0)', 'i Bound;reflexivity',
                      'apply map_get_set', 'exact SXswitch_lookup_absent'):
            self.assertIn(token, src)
        # Both use the same program, same heap and task/env maps; ci=nil on both sides.
        disabled = src.split('Theorem GXboundary_disabled_stuck :', 1)[1].split('Proof.', 1)[0]
        enabled = src.split('Theorem GXboundary_enabled_interrupt :', 1)[1].split('Proof.', 1)[0]
        for token in ('GXboundary_program', '(set(GXtasks other)SXct GXend)cst',
                      '(SXge,GXenvs otherle,SXmemory 1 6,(fun _=>false),'):
            self.assertIn(token, disabled)
            self.assertIn(token, enabled)

    def test_stable_compiles_trust_and_no_new_holes(self):
        stable = read('stable-compiles.json')
        for kind, p in (('body', PROD), ('probe', PROBE)):
            row = read(stable[kind] + '.json')
            h = hashlib.sha256((R / p).read_bytes()).hexdigest()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(h, row['initial_source_sha256'])
            self.assertEqual(h, row['source_sha256'])
            self.assertEqual(h, hashlib.sha256((D / (stable[kind] + '.v.snapshot.txt')).read_bytes()).hexdigest())
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
        trust = read('trust.json')
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(trust['roots_printed'], len(trust['roots']))
        self.assertEqual(trust['roots_printed'], 20)
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))
