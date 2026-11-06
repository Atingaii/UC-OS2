"""结构回归只约束本步证据；实际 Hoare 证明由 Coq 核验。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage206-scheduler-isr-context'
PROD = 'certiucos/v293/proofs/V293OSSchedISRContext.v'
PROBE = 'audit/probes/V293OSSchedISRContextProbe.v'

def read(n):
    return json.loads((D / n).read_text())

def statement(src, name):
    return src.split(name + ' :', 1)[1].split('Proof.', 1)[0]

class SchedulerISRContextTests(unittest.TestCase):
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
        old = R / 'audit/logs/stage205-interrupt-exit-nondispatch/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_actual_builders_context_not_smuggled_into_frame(self):
        src = (R / PROD).read_text()
        stmt = statement(src, 'V293_OSSchedNew_ISR_contract')
        self.assertEqual(stmt.count('InfRules'), 1)
        for token in ('BuildPreI P f vl lg', 'BuildRetI P f vl lg',
                      'V293_OSSchedNew_body', 'V293_ISR_sched_fpre', 'V293_ISR_sched_fpost'):
            self.assertIn(token, stmt)
        self.assertIn('apply V293_sched_internal_payload', src)
        self.assertIn('OS[ir,false,si,ci]', src)
        self.assertIn('if held then invlth_isr I 0 (gettopis si) else Aemp', src)
        self.assertIn('~GoodFrm(V293_sched_ISR_context I held ir si ci)', src)
        self.assertIn('GoodFunAsrt(V293_sched_ISR_context I held ir si ci)', src)
        self.assertIn('GoodFrm frame', statement(src, 'V293_OSSchedNew_ISR_call'))
        self.assertIn('eapply call_rule', src)
        self.assertIn('WFFunEnv (V293_OSSchedNew_internal_unit', src)
        self.assertNotIn('CertiOS.audit.', src)

    def test_actual_enabled_dispatch_without_assumed_middle(self):
        src = (R / PROD).read_text()
        stmt = statement(src, 'V293_OSIntExit_context_same_dispatch')
        self.assertEqual(stmt.count('InfRules'), 1)
        for token in ('nest<=1', 'V293_ready_select lo hi(V293_ready_group lo hi)=nc',
                      'V293_OSIntExit_nesting_dispatch', 'V293_exit_boundary_dispatch',
                      'V293_ISR_sched_fpre', '(pre nest old c)', '(tail c)'):
            self.assertIn(token, stmt)
        for token in ('V293_exit_ready_decrement', 'apply V293_OSSched_ISR_prefix',
                      'V293_OSSched_priority_comparison', 'flag:=true', 'flag:=false'):
            self.assertIn(token, src)
        self.assertNotIn('BuildPreI', stmt)
        self.assertNotIn('V293_exit_boundary_body', stmt)
        self.assertNotIn('WFFunEnv', stmt)
        self.assertIn('V293_OSSched_target_assign', src)

    def test_nonempty_and_single_stack_field_control(self):
        src = (R / PROBE).read_text()
        for name in ('QSpre_nonempty', 'QSselector_nonempty', 'QSboth_decoders',
                     'QSwrong_stack', 'QSenabled_same_dispatch', 'QSscheduler_environment'):
            self.assertRegex(src, r'Theorem ' + name + ' :')
        self.assertIn('BLnonempty hv out nest 0 nc c', src)
        self.assertIn('BLstate(BLmemory hv out nest 0 nc c) |= QSselected I nil ** Atrue', src)
        self.assertIn('~(BLstate(BLmemory hv out nest 0 nc c) |= QSselected I(cons true nil) ** Atrue)', src)
        self.assertIn('V293_ISR_sched_args(QSlg(cons true nil))=Some', src)
        self.assertIn('apply astar_l_acs_elim', src)
        self.assertNotIn('cstepstar', src)
        self.assertNotIn('loststep', src)

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
