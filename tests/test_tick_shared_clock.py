"""仅检查身份、接线与证据一致性；语义结论由 Coq 根定理检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage148-tick-shared-clock'
SHARED = 'certiucos/v293/proofs/V293TimeTickShared.v'
PROBE = 'audit/probes/V293TimeTickSharedProbe.v'


class TickSharedClockTests(unittest.TestCase):
    def setUp(self):
        self.shared = (R / SHARED).read_text()
        self.probe = (R / PROBE).read_text()

    def test_frozen_source_and_ast_identity(self):
        row = json.loads((D / 'source-identity.json').read_text())
        source = (R / row['current_upstream_file']).read_bytes()
        self.assertEqual(hashlib.sha256(source).hexdigest(), row['current_upstream_file_sha256'])
        i = row['identity']
        lines = b''.join(source.splitlines(keepends=True)[i['first_line'] - 1:i['last_line']])
        self.assertEqual(hashlib.sha256(lines).hexdigest(), i['source_lines_sha256'])
        self.assertEqual(row['existing_AST'], 'certiucos/v293/code/V293OSTimeTick.v')
        self.assertFalse(row['new_AST'])
        self.assertNotIn('Definition V293_tick_post_hook', self.shared)

    def test_original_abstract_step_and_physical_increment(self):
        for term in ('spec_prim_step', 'absinfer_prim', 'V293_shared_replace_slot',
                     'V293_OSSched_counter_increment', 'V293_time_shared_inv bn'):
            self.assertIn(term, self.shared)
        statement = self.shared.split('Theorem V293_tick_clock_write :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('sassign (evar now) (ebinop oplus (evar now) (econst32 Int.one))', statement)
        for oracle in ('evalval', 'store ', 'cstepstar', 'Int.max_unsigned'):
            self.assertNotIn(oracle, statement)
        self.assertIn('checked_tick_other_slots', self.probe)
        self.assertIn('checked_tick_wrap', self.probe)

    def test_single_factor_control_reaches_real_execution(self):
        control = self.probe.split('Theorem checked_tick_physical_control :', 1)[1]
        self.assertIn('cstepstar P', control)
        self.assertIn('V293_owned_record_cell_update', control)
        self.assertIn('V293_tick_assign32_execution', control)
        self.assertIn('~NamesState Mf (NamesAbstract (Int.repr 37))', control)
        self.assertIn('NamesState Mf (set (NamesAbstract (Int.repr 37)) ostmid (ostm (Int.repr 38)))', control)
        negative = self.probe.split('Theorem checked_tick_wrong_increment :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('(ostm (Int.repr 39))', negative)
        self.assertNotIn('BuildPre', negative)

    def test_exact_stopped_suffix_not_whole_tick_claim(self):
        statement = self.shared.split('Theorem V293_tick_stopped_shared_suffix :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('run<>1', statement)
        self.assertIn('(V293_tick_post_hook ptcb rows group now running head)', statement)
        disabled = self.shared.split('Theorem V293_tick_clock_disabled :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('V293_time_shared_core bn', disabled)
        for term in ('WFIFun', 'WFAPI', 'GOOD_OS', 'CertiOS.audit.', 'verified_os'):
            self.assertNotIn(term, self.shared)

    def test_stable_compiles_no_holes(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('shared', SHARED), ('probe', PROBE)]:
            source = (R / path).read_bytes()
            self.assertNotRegex(source.decode(), r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show|idtac)\b')
            self.assertNotRegex(source.decode(), re.compile(r'^Inductive ', re.M))
            row = json.loads((D / (stable[kind] + '.json')).read_text())
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256(source).hexdigest())
            self.assertEqual(source, (D / (stable[kind] + '.v.snapshot.txt')).read_bytes())
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(SHARED), 1)

    def test_old_inputs_and_evidence_not_rewritten(self):
        base = json.loads((D / 'baseline.json').read_text())
        for name, row in base.items():
            if name.endswith('.v') or name.startswith(('csrc/', 'framework/', 'tactics/', 'audit/logs/')):
                self.assertEqual(hashlib.sha256((R / name).read_bytes()).hexdigest(), row['sha256'], name)


if __name__ == '__main__':
    unittest.main()
