"""不同任务中断退出至切换调用入口；结构回归不替代 Coq 执行证明。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage198-interrupt-switch-entry'
PROD = 'certiucos/v293/proofs/V293OSIntExitSwitchEntry.v'
PROBE = 'audit/probes/V293OSIntExitSwitchEntryProbe.v'


def read(name):
    return json.loads((D / name).read_text())


class InterruptSwitchEntryTests(unittest.TestCase):
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
        old = R / 'audit/logs/stage197-interrupt-dispatch-call/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_primary_has_no_trace_allocation_or_store_oracle(self):
        src = (R / PROD).read_text()
        stmt = src.split('Theorem V293_OSIntExit_switch_entry_execution :', 1)[1].split('Proof.', 1)[0]
        pre = stmt.split('exists bs next nh Mf,', 1)[0]
        for token in ('cstepstar', 'V293_local_steps', 'fresh M', 'store ', 'free ', 'evalval'):
            self.assertNotIn(token, pre)
        for token in ('~V293_highest_ready tasks ct', 'V293_current_task tasks ct nc',
                      'sfexec int_switch nil nil', 'next<>ct', 'nh<>nc',
                      'kseq(sprim excrit)(kseq sret(kcall f', 'Int.add c Int.one',
                      'Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero)', 'exists v,get Mf',
                      'block<>bs', 'block<>bo', 'block<>bcount'):
            self.assertIn(token, stmt)
        for token in ('V293_OSIntExit_dispatch_prefix_execution', 'V293_OSSched_current_target',
                      'V293_exit_change_to_sfexec', 'V293_owned_record_cell_update',
                      'V293_tick_assign32_execution', 'apply snpcall_step',
                      'apply encrit_step', 'eapply salloclv_step'):
            self.assertIn(token, src)
        self.assertNotIn('CertiOS.audit.', src)

    def test_consistent_nonempty_full_prefix_and_both_IE(self):
        src = (R / PROBE).read_text()
        for token in ('Definition SXct := OwnershipWaiting', 'apply OwnershipCellsSpatial.',
                      'Theorem SXconsistent_current :', 'V293_current_task OwnershipTasks SXct 6',
                      '~V293_highest_ready OwnershipTasks SXct', 'load(Tptr Tvoid)(SXmemory 1 6)',
                      'Theorem SXcomplete_prefix :', 'V293_OSIntExit_switch_entry_execution',
                      'SXcomplete_prefix false ci kstop', 'SXcomplete_prefix true ci kstop'):
            self.assertIn(token, src)
        both = src.split('Theorem SXboth_IE_prefix :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(both.count('V293_local_steps SXprogram'), 2)
        self.assertEqual(both.count('((SXge,SXcaller,SXmemory 1 6)'), 2)
        self.assertEqual(both.count('(curs(sfexec 112%Z nil nil),(kenil,SXK kstop))'), 2)
        for token in ('(false,nil,ci)', '(true,nil,ci)', 'cons false ci', 'cons true ci',
                      'Int.repr 20', 'get M0(b0,Z.of_nat k)', 'get M1(b1,Z.of_nat k)'):
            self.assertIn(token, both)
        for b in (99, 100):
            self.assertIn(f'load Tint8 M0({b}%positive,0%Z)', both)
            self.assertIn(f'load Tint8 M1({b}%positive,0%Z)', both)

    def test_single_factor_reaches_same_tail_boundary_and_missing_port_is_bounded(self):
        src = (R / PROBE).read_text()
        normal = src.split('Definition SXtail :=', 1)[1].split('Definition SXomit_tail :=', 1)[0]
        omitted = src.split('Definition SXomit_tail :=', 1)[1].split('Definition SXtail_frame :=', 1)[0]
        self.assertEqual(normal.replace('(sseq(V293_OSSched_increment 111%Z)', '').replace('nil)))', 'nil))').strip(),
                         omitted.strip())
        stmt = src.split('Theorem SXcounter_increment_ablation :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('(curs SXtail,(kenil,ks))(SXge,SXcaller,M19)', stmt)
        self.assertIn('(curs SXomit_tail,(kenil,ks))(SXge,SXcaller,M19)', stmt)
        self.assertEqual(stmt.count('(curs(sfexec 112%Z nil nil),(kenil,ks))'), 2)
        for token in ('load Tint32 M19', 'Int.repr 19', 'load Tint32 M20', 'Int.repr 20',
                      'get M20(b,i)=get M19(b,i)', 'Theorem SXswitch_lookup_absent : SXprogram 112%Z=None.',
                      'Theorem SXreal_port_boundary_no_step :', 'apply V293_missing_port_has_no_step'):
            self.assertIn(token, src)

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
