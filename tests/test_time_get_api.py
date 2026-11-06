"""身份与连接回归；时钟一致性结论由 Coq 探针及独立 coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage147-time-get-api'
API = 'certiucos/v293/proofs/V293TimeGetAPI.v'
LINK = 'certiucos/v293/proofs/V293TimeGetLink.v'
PROBE = 'audit/probes/V293TimeGetAPIProbe.v'


class TimeGetAPITests(unittest.TestCase):
    def setUp(self):
        self.api = (R / API).read_text()
        self.link = (R / LINK).read_text()
        self.probe = (R / PROBE).read_text()

    def test_source_identity_and_unchanged_existing_body(self):
        row = json.loads((D / 'source-identity.json').read_text())
        identity = row['identity']
        source = (R / row['current_upstream_file']).read_bytes()
        self.assertEqual(hashlib.sha256(source).hexdigest(), identity['source_file_sha256'])
        lines = b''.join(source.splitlines(keepends=True)[identity['first_line'] - 1:identity['last_line']])
        self.assertEqual(hashlib.sha256(lines).hexdigest(), identity['source_lines_sha256'])
        self.assertEqual(hashlib.sha256(row['preprocessed_body'].encode()).hexdigest(),
                         identity['preprocessed_body_sha256'])
        self.assertFalse(row['new_AST'])
        self.assertEqual(row['existing_AST'], 'certiucos/v293/proofs/V293TimeAccess.v')
        self.assertNotIn('Definition V293_TimeGet_body', self.api)

    def test_read_linearizes_before_excrit_and_never_replaces_clock(self):
        step = self.api.split('Definition V293_time_get_step :', 1)[1].split('Definition V293_time_get_action', 1)[0]
        self.assertIn('get O ostmid = Some (ostm clock)', step)
        self.assertIn('result = (Some (Vint32 clock), O)', step)
        self.assertIn('spec_prim_step', self.api)
        self.assertIn('V293_time_get_transition', self.api)
        self.assertNotIn('V293_shared_replace_slot', self.api)
        critical = self.api.split('Theorem V293_time_get_critical :', 1)[1].split('Qed.', 1)[0]
        self.assertLess(critical.index('apply V293_time_get_copy'), critical.index('apply excrit1_rule'))
        body = self.api.split('Theorem V293_OSTimeGet_refined_body :', 1)[1].split('Proof.', 1)[0]
        self.assertIn('result = Some (Vint32 clock)', body)
        self.assertNotIn('V293_time_shared_core', body)

    def test_actual_api_builders_and_satisfiable_same_local_invariant(self):
        contract = self.api.split('Theorem V293_TimeGet_api_contract :', 1)[1]
        for term in ("BuildPreA'", "BuildRetA'", 'V293_OSTimeGet_refined_body'):
            self.assertIn(term, contract)
        for term in ('checked_get_actual_builders', 'checked_get_joint_entry',
                     'checked_get_caller_entry', 'checked_get_body_same_shared_environment',
                     'NamesJointMemory clock', 'GetPre', 'LinkSpec', 'LinkLI'):
            self.assertIn(term, self.probe)
        self.assertIn('NamesCallerMemory emp |= GetPre', self.probe)
        self.assertIn('change_aop_rule', self.probe)

    def test_three_api_component_reuses_one_shared_environment(self):
        wf = self.link.split('Theorem V293_clock_WFAPI :', 1)[1].split('Qed.', 1)[0]
        for term in ('V293_OSVersion_api_contract', 'V293_TimeSet_api_contract', 'V293_TimeGet_api_contract'):
            self.assertIn(term, wf)
        statement = self.link.split('Theorem V293_clock_components_checked :', 1)[1].split('Proof.', 1)[0]
        for term in ('GoodI', 'WFAPI', 'WFIFun', 'no_fun_same'):
            self.assertIn(term, statement)
            self.assertNotIn(term, '->'.join(statement.split('->')[:-1]))
        self.assertEqual(statement.count('let Spec :='), 1)
        self.assertIn('checked_four_actual_bindings', self.probe)
        for source in (self.api, self.link):
            self.assertNotIn('CertiOS.audit.', source)
            self.assertNotIn("verified_os'", source)
            self.assertNotIn('InitAsrt', source)

    def test_wrong_value_control_reaches_original_read_transition(self):
        positive = self.probe.split('Theorem checked_get_read_positive :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('load Tint32', positive)
        self.assertIn('spec_step sd V293_time_get_action', positive)
        exact = self.probe.split('Theorem checked_get_read_result_exact :', 1)[1].split('Qed.', 1)[0]
        self.assertIn("result=Some (Vint32 clock) /\\ O'=O", exact)
        self.assertIn('inversion Step', exact)
        negative = self.probe.split('Theorem checked_get_wrong_result_rejected :', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(negative.count('NamesAbstract (Int.repr 37)'), 2)
        self.assertIn('END (Some (Vint32 (Int.repr 38)))', negative)
        self.assertNotIn('BuildPre', negative)

    def test_checked_snapshots_no_holes_and_frozen_old_implementation(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        project = (R / '_CoqProject').read_text().splitlines()
        for kind, name in [('api', API), ('link', LINK), ('probe', PROBE)]:
            source = (R / name).read_bytes()
            self.assertNotRegex(source.decode(), r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show|idtac)\b')
            self.assertNotRegex(source.decode(), re.compile(r'^Inductive ', re.M))
            if kind != 'probe':
                self.assertEqual(project.count(name), 1)
            row = json.loads((D / (stable[kind] + '.json')).read_text())
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256(source).hexdigest())
            self.assertEqual(source, (D / (stable[kind] + '.v.snapshot.txt')).read_bytes())
        baseline = json.loads((D / 'baseline.json').read_text())
        for name, row in baseline.items():
            if name.endswith('.v') or name.startswith(('csrc/', 'framework/', 'tactics/')):
                self.assertEqual(hashlib.sha256((R / name).read_bytes()).hexdigest(), row['sha256'], name)


if __name__ == '__main__':
    unittest.main()
