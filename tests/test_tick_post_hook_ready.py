"""固定身份与结构回归；语义结论以真实Coq编译及独立内核检查为准。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage154-tick-post-hook-ready'
PRODUCTION = 'certiucos/v293/proofs/V293TimeTickPostHookReady.v'
PROBE = 'audit/probes/V293TimeTickPostHookReadyProbe.v'


class TickPostHookReadyTests(unittest.TestCase):
    def setUp(self):
        self.production = (R / PRODUCTION).read_text()
        self.probe = (R / PROBE).read_text()

    def test_fixed_source_original_suffix_and_existing_relations(self):
        identity = json.loads((D / 'source-identity.json').read_text())
        raw = (R / identity['current_upstream_file']).read_bytes()
        self.assertEqual(hashlib.sha256(raw).hexdigest(), identity['current_upstream_file_sha256'])
        i = identity['identity']
        body = b''.join(raw.splitlines(keepends=True)[i['first_line'] - 1:i['last_line']])
        self.assertEqual(hashlib.sha256(body).hexdigest(), i['source_lines_sha256'])
        self.assertFalse(identity['new_AST'])
        for term in ('V293_tick_post_hook_owned_execution (map fst bindings)',
                     'V293_tick_chain_records_before', 'V293_tick_chain_records_after',
                     'V293_tick_record_chain_ready_rel bindings', 'V293_ready_payload br bg bp'):
            self.assertIn(term, self.production)
        self.assertNotIn('CertiOS.audit.', self.production)
        self.assertNotRegex(self.production, r'(?m)^(?:Inductive|Definition) ')

    def test_original_clock_then_chain_abstract_steps(self):
        statement = self.production.split('Lemma V293_tick_post_hook_transition :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('spec_seq V293_tick_clock_action (V293_tick_chain_code bindings)', statement)
        self.assertIn('set (set O ostmid (ostm (Int.add now Int.one))) abstcblsid', statement)
        for term in ('apply V293_tick_clock_transition', 'apply V293_tick_record_chain_transition',
                     'apply spec_seq_step2', 'apply spec_seq_step1'):
            self.assertIn(term, self.production)

    def test_same_Mf_clock_records_bitmap_table_and_shared_fields(self):
        statement = self.production.split('Theorem V293_tick_post_hook_ready_payload :', 1)[1].split('Proof.', 1)[0]
        entry, result = statement.split('exists Mf,', 1)
        self.assertNotIn('exists Mf,', result)
        self.assertEqual(entry.count('V293_priority_cells bp 0%Z entries'), 1)
        self.assertNotIn('V293_owned_task_records', entry)
        self.assertIn('bc scan (map fst bindings)', entry)
        for term in ('V293_tick_post_hook ptcb rows group clock running head',
                     'load Tint32 Mf (bn,0%Z)=Some (Vint32 (Int.add now Int.one))',
                     'V293_task_records Mf', 'V293_ready_loads Mf br bg bp',
                     'V293_ready_payload br bg bp', '(ge,le,Mf,ir,',
                     'events\n              (Int.add now Int.one)'):
            self.assertIn(term, result)
        self.assertIn('eapply V293_ready_loads_sub', self.production)

    def test_satisfiable_nonempty_entry_and_nontrivial_initialization(self):
        for term in ('OwnershipCellsSeparated PHcells', 'OwnershipCellsSpatial',
                     'Lemma PHraw_entry :', 'Theorem PHentry :', 'Theorem PHliteral :',
                     'V293_tick_pointer_cell 70%positive WhileIdle :: tl RCcells',
                     'WhileHead<>WhileIdle', 'V293_task_record Mf WhileHead (Int.repr 10) rdy',
                     'V293_task_record Mf WhileSecond (Int.repr 2) (wait os_stat_time (Int.repr 2))',
                     '(false,[3%nat],[false])'):
            self.assertIn(term, self.probe)

    def test_single_abstract_clock_omission_same_execution(self):
        statement = self.probe.split('Theorem PHomitted_clock_control :', 1)[1].split('Proof.', 1)[0]
        for term in ('PHexecution P ks Mf /\\ PHresult Mf',
                     'get ChainNew ostmid=Some (ostm (Int.repr 37))',
                     'forall id, id<>ostmid -> get PHnew id=get ChainNew id',
                     'V293_shared_fields WhileReady WhileNewTasks ChainEvents (Int.repr 38)'):
            self.assertIn(term, statement)
        self.assertNotIn('del Mf', statement)
        self.assertIn('Theorem PHold_physical_clock_control :', self.probe)
        for term in ('V293_table_loads V293_tcb_type Mf 94%positive RCentries',
                     'get PHnew absecblsid=Some (absecblist ChainEvents)', 'Int.repr 99'):
            self.assertIn(term, self.probe)

    def test_stable_compilation_project_and_no_holes(self):
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
