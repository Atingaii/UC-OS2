"""结构回归只约束本步证据；实际 Hoare 证明由 Coq 核验。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage210-interrupt-exit-handoff-hoare'
PROD = 'certiucos/v293/proofs/V293OSIntExitHandoffHoare.v'
PROBE = 'audit/probes/V293OSIntExitHandoffHoareProbe.v'

def read(n):
    return json.loads((D / n).read_text())

def statement(src, name):
    return src.split(name + ' :', 1)[1].split('Proof.', 1)[0]

class InterruptExitHandoffHoareTests(unittest.TestCase):
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
        old = R / 'audit/logs/stage209-interrupt-exit-unified-builders/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_actual_suffix_no_whole_body_or_evaluation_oracle(self):
        src = (R / PROD).read_text()
        stmt = statement(src, 'V293_OSIntExit_changed_tail')
        self.assertEqual(stmt.count('InfRules'), 1)
        for token in ('V293_OSSched_increment counter', 'sskip None',
                      'V293_interrupt_handoff high current target', 'V293_exit_handoff_resumed'):
            self.assertIn(token, stmt)
        for token in ('apply V293_exit_handoff_increment', 'apply V293_exit_handoff_copy',
                      'eapply switch_rule', 'apply V293_storage_tail_switch_pre',
                      'apply V293_storage_tail_return', 'eapply mapstoval_load'):
            self.assertIn(token, src)
        stmt = statement(src, 'V293_handoff_byte_copy')
        self.assertEqual(stmt.count('InfRules'), 1)
        self.assertNotIn('evalval', stmt)
        self.assertNotIn('CertiOS.audit.', src)

    def test_shared_full_write_cells_not_frozen_private_snapshot(self):
        src = (R / PROD).read_text()
        private = src.split('Let private :=', 1)[1].split('Definition V293_exit_handoff_tail', 1)[0]
        for token in ('V293_handoff_byte ', 'V293_counter_cell ', 'Amapsto', 'tasks', 'events', 'now'):
            self.assertNotIn(token, private)
        resumed = src.split('Definition V293_exit_handoff_resumed :=', 1)[1].split('Lemma', 1)[0]
        for token in (' nh', ' nc', ' tasks', ' events', ' now', ' c.'):
            self.assertNotIn(token, resumed)
        self.assertIn('V293_storage_resumed', resumed)
        close = statement(src, 'V293_exit_handoff_close')
        self.assertIn('V293_storage_tail', close)
        self.assertIn('nh<256 ->nc<256', close)
        storage = (R / 'certiucos/v293/proofs/V293DispatchStorage.v').read_text()
        self.assertIn('EX v : val, [|rule_type_val_match tau v = true|] ** Amapsto a tau true v', storage)
        self.assertIn('Amapsto(b,0%Z)Tint8 true', src)

    def test_independent_nonempty_different_task_max_counter_and_control_limits(self):
        src = (R / PROBE).read_text()
        for name in ('FHbyte_owned', 'FHextra_witness', 'FHspatial', 'FHentry_nonempty',
                     'FHdifferent_max_nonempty', 'FHactual_changed_tail', 'FHcopy_observable', 'FHcounter_wrap'):
            self.assertRegex(src, r'(?:Theorem|Lemma) ' + name + ' :')
        witness = statement(src, 'FHdifferent_max_nonempty')
        for token in ('V293_switch_target true<>V293_idle_tid', 'Int.repr Int.max_unsigned',
                      'V293_highest_ready', 'indom', 'Aemp 12 4'):
            self.assertIn(token, witness)
        self.assertIn('encode_val Tint8(V293_byteval n)', src)
        self.assertIn('apply V293_OSIntExit_changed_tail', src)
        self.assertIn('Check BXcopy_ablation.', src)
        self.assertIn('not an execution of FH', src)
        self.assertNotIn('V293_global_steps', src)
        self.assertNotIn('cstepstar', src)

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
