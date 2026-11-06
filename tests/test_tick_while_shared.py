"""身份与接线检查；原语义执行和联合所有权由 Coq 内核另行检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage152-tick-while-shared'
PRODUCTION = 'certiucos/v293/proofs/V293TimeTickWhileShared.v'
PROBE = 'audit/probes/V293TimeTickWhileSharedProbe.v'


class TickWhileSharedTests(unittest.TestCase):
    def setUp(self):
        self.production = (R / PRODUCTION).read_text()
        self.probe = (R / PROBE).read_text()

    def test_fixed_source_and_original_relations(self):
        identity = json.loads((D / 'source-identity.json').read_text())
        raw = (R / identity['current_upstream_file']).read_bytes()
        self.assertEqual(hashlib.sha256(raw).hexdigest(), identity['current_upstream_file_sha256'])
        i = identity['identity']
        body = b''.join(raw.splitlines(keepends=True)[i['first_line'] - 1:i['last_line']])
        self.assertEqual(hashlib.sha256(body).hexdigest(), i['source_lines_sha256'])
        self.assertFalse(identity['new_AST'])
        for term in ('V293_tick_while_owned_records bindings', 'apply V293_tick_wait_transition',
                     'apply spec_seq_step2', 'apply spec_seq_step1'):
            self.assertIn(term, self.production)
        self.assertNotIn('CertiOS.audit.', self.production)

    def test_ordered_computed_batch_not_output_oracle(self):
        run = self.production.split('Fixpoint V293_tick_bindings_run', 1)[1].split('Lemma ', 1)[0]
        for term in ('rdy => tasks', 'V293_tick_bindings_run rest',
                     'rdy => V293_tick_chain_code rest', 'spec_prim nil (V293_tick_wait_step'):
            self.assertIn(term, run)
        statement = self.production.split('Theorem V293_tick_chain_transition :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('V293_tick_bindings_run bindings tasks', statement)
        self.assertNotIn('newtasks', statement)
        for term in ('Theorem V293_tick_bindings_run_map :', 'Theorem V293_tick_record_chain_transition :',
                     'Forall V293_tick_binding_valid bindings', 'NoDup (V293_tick_record_keys bindings idle)'):
            self.assertIn(term, self.production)

    def test_old_records_derived_from_same_joint_entry(self):
        statement = self.production.split('Theorem V293_tick_while_shared_records :', 1)[1].split('Proof.', 1)[0]
        inputs, outputs = statement.split('->\n  V293_task_records M', 1)
        self.assertNotIn('V293_task_records', inputs)
        self.assertNotIn('V293_owned_task_records', inputs)
        self.assertIn('V293_shared_fields current (V293_tick_record_map false', inputs)
        self.assertIn('V293_tick_chain_records_before', self.production)
        self.assertIn('V293_owned_task_records_sound', self.production)
        self.assertIn('V293_tick_record_map false bindings idle message', outputs)

    def test_same_Mf_and_joint_shared_update(self):
        statement = self.production.split('Theorem V293_tick_while_shared_records :', 1)[1].split('Proof.', 1)[0]
        before, after = statement.split('exists Mf,', 1)
        self.assertIn('spec_stepstar sd (V293_tick_chain_code bindings)', before)
        self.assertIn('forall id, id<>abstcblsid', before)
        for term in ('V293_local_steps P', 'swhile (V293_tick_guard ptcb)',
                     'load (Tptr V293_tcb_type) Mf', 'V293_task_records Mf',
                     '(ge,le,Mf,', 'V293_shared_fields current (V293_tick_record_map true',
                     'V293_tick_bitmap_cells bg br gf lof hif', '** R'):
            self.assertIn(term, after)
        self.assertIn('apply V293_shared_replace_slot', self.production)
        for claim in ('Theorem GOOD_OS', 'Theorem WFIFun', 'verified_os'):
            self.assertNotIn(claim, self.production)

    def test_nonempty_executed_single_omission_and_other_slots(self):
        for term in ('Theorem ChainEntry :', 'Theorem ChainLiteral :', 'Theorem ChainFirstStep :',
                     'Lemma ChainFirstIsSingleOmission : ChainFirstTasks=WhileOmitSecond.',
                     'Theorem ChainOmitSecondControl :', 'Theorem ChainSlotsReadyIdleFrame :',
                     'sig (84%positive,Int.repr 4)', 'V293_shared_fixture_abs WhileReady',
                     'ostm (Int.repr 37)', 'V293_task_record Mf WhileIdle', 'Int.repr 99'):
            self.assertIn(term, self.probe)
        negative = self.probe.split('Theorem ChainOmitSecondControl :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('exists Mf,', negative)
        self.assertIn('WhileExecution P ks Mf /\\ ChainResult Mf', negative)
        self.assertEqual(negative.count('spec_stepstar sd'), 2)
        self.assertIn('ChainFirstTasks=WhileOmitSecond', negative)
        self.assertIn('~ V293_task_records Mf ChainFirstTasks', negative)
        self.assertNotIn('del Mf', negative)

    def test_stable_compilation_and_no_holes(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('production', PRODUCTION), ('probe', PROBE)]:
            raw = (R / path).read_bytes()
            self.assertNotRegex(raw.decode(), r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show|idtac)\b')
            self.assertNotRegex(raw.decode(), re.compile(r'^Inductive ', re.M))
            row = json.loads((D / (stable[kind] + '.json')).read_text())
            self.assertEqual(row['exit'], 0)
            self.assertEqual(hashlib.sha256(raw).hexdigest(), row['source_sha256'])
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(raw, (D / (stable[kind] + '.v.snapshot.txt')).read_bytes())
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(PRODUCTION), 1)

    def test_old_sources_tests_and_evidence_unchanged(self):
        baseline = json.loads((D / 'baseline.json').read_text())['files']
        for name, digest in baseline.items():
            if name.endswith('.v') or name.startswith(('csrc/', 'framework/', 'tactics/', 'audit/logs/', 'tests/')):
                self.assertEqual(hashlib.sha256((R / name).read_bytes()).hexdigest(), digest, name)


if __name__ == '__main__':
    unittest.main()
