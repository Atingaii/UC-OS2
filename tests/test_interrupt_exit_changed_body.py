"""结构回归只约束本步证据；实际 Hoare 证明由 Coq 核验。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage212-interrupt-exit-changed-body'
PROD = 'certiucos/v293/proofs/V293OSIntExitChangedBody.v'
PROBE = 'audit/probes/V293OSIntExitChangedBodyProbe.v'

def read(n):
    return json.loads((D / n).read_text())

def statement(src, name):
    return src.split(name + ' :', 1)[1].split('Proof.', 1)[0]

class InterruptExitChangedBodyTests(unittest.TestCase):
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
        old = R / 'audit/logs/stage211-interrupt-exit-dispatch-hoare/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_full_normalized_body_no_body_or_expression_oracle(self):
        src = (R / PROD).read_text()
        stmt = statement(src, 'V293_OSIntExit_changed_body')
        self.assertEqual(stmt.count('InfRules'), 1)
        for token in ('evalval', 'evaltype'):
            self.assertNotIn(token, stmt)
        for token in ('V293_exit_boundary_body running nesting lock saved',
                      'V293_interrupt_handoff high current target', 'nest<=1',
                      'V293_exit_changed_resumed ci', 'OS[(fun _:hid=>false),false,si,ci]'):
            self.assertIn(token, stmt)
        for token in ('V293_time_zero', 'V293_exit_running_eval', 'apply encrit2_rule',
                      'V293_OSIntExit_nesting_dispatch_hoare', 'apply V293_OSIntExit_changed_dispatch',
                      'apply V293_storage_resumed_excrit', 'apply ret_rule'):
            self.assertIn(token, src)
        self.assertNotIn('CertiOS.audit.', src)

    def test_controls_returned_to_same_inv_no_shared_value_snapshot(self):
        src = (R / PROD).read_text()
        controls = src.split('Let controls:=', 1)[1].split('Let returned', 1)[0]
        for block in ('brun', 'bn', 'bl'):
            self.assertIn('((' + block + ',0%Z),Tint8)', controls)
        self.assertIn('Let returned:=controls++rest.', src)
        self.assertIn('Let inv:=V293_storage_inv cells target tp.', src)
        resumed = src.split('Definition V293_exit_changed_resumed critical:=', 1)[1].split('Lemma', 1)[0]
        self.assertIn('tp entries returned tid aop si critical dispatchpx', resumed)
        self.assertNotRegex(resumed, r'\b(?:tasks|events|now|hv|nc|lo|hi)\b')
        private = src.split('Let dispatchpx:=', 1)[1].split('Definition V293_exit_changed_resumed', 1)[0]
        self.assertIn('V293_time_cell true saved bs(Vint32 Int.zero)', private)
        for token in ('V293_handoff_byte', 'V293_storage ', 'tasks', 'events', 'now'):
            self.assertNotIn(token, private)
        self.assertIn('apply V293_disabled_clear_flags', src)

    def test_independent_bytes_nonempty_instance_and_primitive_tail_control(self):
        src = (R / PROBE).read_text()
        for name in ('CXcontrols_witness', 'CXphysical_all', 'CXenv_owned',
                     'CXresources_owned', 'CXpre_owned', 'CXentry_nonempty',
                     'CXzero_max_entry', 'CXactual_body', 'CXexcrit_control'):
            self.assertRegex(src, r'(?:Theorem|Lemma) ' + name + ' :')
        for token in ('encode_val Tint8', 'CXmemory nest c old', 'Int.repr Int.max_unsigned',
                      'V293_highest_ready', 'V293_switch_target true<>V293_idle_tid',
                      'apply V293_OSIntExit_changed_body', 'apply excrit_step'):
            self.assertIn(token, src)
        self.assertEqual(statement(src, 'CXactual_body').count('InfRules'), 1)
        control = statement(src, 'CXexcrit_control')
        self.assertIn('false::ci', control)
        self.assertIn('Acs ci ** Atrue', control)
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
