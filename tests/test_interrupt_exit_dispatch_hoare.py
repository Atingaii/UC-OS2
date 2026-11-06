"""结构回归只约束本步证据；实际 Hoare 证明由 Coq 核验。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage211-interrupt-exit-dispatch-hoare'
PROD = 'certiucos/v293/proofs/V293OSIntExitDispatchHoare.v'
PROBE = 'audit/probes/V293OSIntExitDispatchHoareProbe.v'

def read(n):
    return json.loads((D / n).read_text())

def statement(src, name):
    return src.split(name + ' :', 1)[1].split('Proof.', 1)[0]

class InterruptExitDispatchHoareTests(unittest.TestCase):
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
        old = R / 'audit/logs/stage210-interrupt-exit-handoff-hoare/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_actual_dispatch_no_body_or_evaluation_oracle(self):
        src = (R / PROD).read_text()
        stmt = statement(src, 'V293_OSIntExit_changed_dispatch')
        self.assertEqual(stmt.count('InfRules'), 1)
        self.assertNotIn('evalval', stmt)
        self.assertNotIn('evaltype', stmt)
        for token in ('V293_exit_boundary_dispatch table high target current counter sched_id',
                      'V293_interrupt_handoff high current target', 'V293_exit_dispatch_resumed',
                      'V293_bitmap_tasks lo hi tasks', 'V293_priority_table entries tasks', 'nh<>nc'):
            self.assertIn(token, stmt)
        for token in ('apply V293_retained_OSSched_storage_prefix_returned',
                      'apply V293_exit_dispatch_open', 'eapply if_rule',
                      'V293_exit_dispatch_guard', 'apply V293_OSIntExit_changed_tail',
                      'apply pfalse_rule', 'V293_handoff_cast'):
            self.assertIn(token, src)
        self.assertNotIn('CertiOS.audit.', src)

    def test_shared_arrays_returned_not_private_or_resumption_snapshots(self):
        src = (R / PROD).read_text()
        private = src.split('Let private:=', 1)[1].split('Let kept', 1)[0]
        self.assertEqual(private.strip(), 'bindings ** (px ** Atrue).')
        bindings = src.split('Let bindings:=', 1)[1].split('Let private', 1)[0]
        for token in ('V293_storage ', 'V293_inputs_full', 'V293_array true',
                      'V293_handoff_byte ', 'V293_counter_cell ', 'tasks', 'events', 'now'):
            self.assertNotIn(token, bindings)
        resumed = src.split('Definition V293_exit_dispatch_resumed:=', 1)[1].split('Lemma', 1)[0]
        self.assertIn('V293_exit_handoff_resumed', resumed)
        self.assertIn('tp arrays tid aop stack critical private', resumed)
        for token in (' nh', ' nc', ' tasks', ' events', ' now', ' c.'):
            self.assertNotIn(token, resumed)
        for token in ('Let arrays:=V293_input_cells bt bg br ++ V293_array_cells',
                      'Let inv:=V293_storage_inv cells target tp',
                      'apply V293_inputs_to_storage', 'apply V293_array_to_storage',
                      'apply V293_storage_append'):
            self.assertIn(token, src)
        self.assertIn('V293_highest_ready tasks next', statement(src, 'V293_exit_dispatch_open'))

    def test_independent_entry_actual_instance_and_bounded_controls(self):
        src = (R / PROBE).read_text()
        for name in ('DXbyte_owned', 'DXextra_owned', 'DXphysical_owned', 'DXempty_owned',
                     'DXresources_owned', 'DXentry_owned', 'DXentry_nonempty',
                     'DXmax_entry_nonempty', 'DXcomparison_control', 'DXactual_dispatch'):
            self.assertRegex(src, r'(?:Theorem|Lemma) ' + name + ' :')
        for token in ('encode_val Tint8(V293_byteval n)',
                      'V293_switch_target true<>V293_idle_tid',
                      'Int.repr Int.max_unsigned', 'V293_highest_ready',
                      'apply V293_retained_storage_prefix_lend_value',
                      'apply V293_OSIntExit_changed_dispatch', 'Check BXcopy_ablation.',
                      'This observes the guard, not two body executions.'):
            self.assertIn(token, src)
        ctrl = statement(src, 'DXcomparison_control')
        self.assertIn('s|=DXentry c events now aop', ctrl)
        self.assertIn('V293_OSSched_different 103%Z 113%Z', ctrl)
        self.assertIn('V293_OSSched_different 113%Z 113%Z', ctrl)
        self.assertEqual(ctrl.count('(getsmem s)'), 2)
        self.assertEqual(statement(src, 'DXactual_dispatch').count('InfRules'), 1)
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
