"""结构检查不是语义证明；真实调用fixture与Coq内核复核另行执行。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage83-call-records'
PROOF = ROOT / 'certiucos/v293/proofs/V293CallRecords.v'
PROBE = ROOT / 'audit/probes/V293CallRecordsProbe.v'


class CallRecordsTests(unittest.TestCase):
    def test_real_call_allocates_instead_of_assuming_callee_objects(self):
        s = PROOF.read_text()
        self.assertIn(str(PROOF.relative_to(ROOT)), (ROOT / '_CoqProject').read_text().splitlines())
        sig = s.split('Theorem V293_OS_TCBInit_call_return_records_under_hooks :')[1].split('Proof.')[0]
        self.assertIn('P f=Some(V293_TCBInit_function hi hc)', sig)
        self.assertIn('(forall b, In b blocks -> fresh M b)', sig)
        entry = sig.split('(ge,caller,M,ir,aux,O,op) |=')[1].split('exists Mf,')[0]
        self.assertIn('V293_owned_task_records tasks ** Atrue', entry)
        self.assertNotIn('V293_tcb_function_cells', entry)
        self.assertNotIn('V293_tcb_prefix_inputs', entry)
        for part in ['destruct (V293_tcb_call_prologue P',
                     'destruct (V293_tcb_call_prologue_records tasks P',
                     'destruct (V293_OS_TCBInit_prefix_return_records_under_hooks tasks P',
                     'exact Prologue |exact Body']:
            self.assertIn(part, s)

    def test_reversible_raw_view_retains_actual_record_witnesses(self):
        s = PROOF.read_text()
        view = s.split('Lemma V293_task_list_raw_view :')[1].split('Lemma V293_tcb_call_prologue_records')[0]
        for part in ['exists cells', 'forall Q', 'destruct Head as [p [pend Head]]',
                     'V293_owned_cells_types', 'V293_record_cells_to_raw',
                     'V293_raw_record_ownership', 'exists p. exists pend.', 'exact JM', 'exact JO']:
            self.assertIn(part, view)
        self.assertNotIn('destruct status', view)
        self.assertNotIn('CertiOS.audit', s)
        self.assertNotRegex(re.sub(r'\(\*.*?\*\)', '', s, flags=re.S),
                            r'\b(Axiom|Parameter|Conjecture|Admitted|admit)\b')
        self.assertIn('apply Rebuild in Final', s)

    def test_return_is_joint_with_explicit_survivor_separation(self):
        sig = PROOF.read_text().split('Theorem V293_OS_TCBInit_call_return_records_under_hooks :')[1].split('Proof.')[0]
        self.assertEqual(sig.count('V293_records_hook_return tasks\''), 2)
        for part in ['In (t,value) (TcbMod.lst tasks\') -> ~In (fst t) blocks',
                     'In (a,tp,v) (tl after++survivors) -> ~In (fst a) blocks',
                     'V293_rdy_raw_cells (tl after++survivors) Atrue',
                     '(curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((ge,caller,Mf)',
                     'get Mf (b,Z.of_nat k)=None']:
            self.assertIn(part, sig)
        self.assertNotIn('V293_tcb_init_final_fields', sig)

    def test_literal_no_initial_locals_and_exact_compilation(self):
        inv = json.loads((LOG / 'literal-inventory.json').read_text())
        self.assertEqual((inv['cells'], inv['bytes'], inv['initial_local_objects']), (35, 85, 0))
        self.assertEqual(sum(x[4] for x in inv['items']), 85)
        self.assertTrue(all(int(x[0]) not in range(201, 210) for x in inv['items']))
        for label, path in [('proof10', PROOF), ('probe04', PROBE)]:
            row = json.loads((LOG / (label + '.json')).read_text())
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['source_sha256'], hashlib.sha256(path.read_bytes()).hexdigest())
            self.assertEqual(path.read_bytes(), (LOG / (label + '.v.snapshot.txt')).read_bytes())
        s = PROBE.read_text()
        fields = s.split('Definition CallOldFields :')[1].split('Definition CallLinks')[0]
        self.assertEqual(fields.count('(Vundef)'), 18)
        self.assertIn('Lemma CallNoInitialLocals : forall b i', s)
        self.assertIn('V293_task_records Mf CallUpdated /\\ CallReads Mf /\\ CallFreed Mf', s)

    def test_real_missing_hook_fixture_and_prefix_negative_are_bounded(self):
        s = PROBE.read_text()
        for part in ['Theorem CallPrefixExcludesWrong', 'Theorem CallActualMissingHook',
                     'Definition CallFixtureProgram', 'Theorem CallMissingHookFixture',
                     'if Z.eq_dec f 900%Z then Some(V293_TCBInit_function 901%Z 902%Z) else None',
                     'apply CallActualMissingHook;reflexivity.',
                     'apply V293_missing_hook_cannot_return', 'rewrite Read in Physical. discriminate.']:
            self.assertIn(part, s)
        self.assertTrue(json.loads((LOG / 'controls.json').read_text())['passed'])

    def test_prospective_single_final_priority_same_proof_control(self):
        plan = json.loads((LOG / 'post-control-plan.json').read_text())
        a = (LOG / 'Positive.v.snapshot.txt').read_text()
        b = (LOG / 'WrongNewPriority.v.snapshot.txt').read_text()
        self.assertEqual(a.count(plan['old']), 1)
        self.assertEqual(a.replace(plan['old'], plan['new'], 1), b)
        self.assertEqual(a.split('Proof.')[1], b.split('Proof.')[1])
        for name, code in [('Positive', 0), ('WrongNewPriority', 1)]:
            self.assertEqual(json.loads((LOG / (name + '.json')).read_text())['exit'], code)
        order = json.loads((LOG / 'prospective-order.json').read_text())
        self.assertLess(order['protocol.json']['mtime_ns'], order['proof01.json']['mtime_ns'])
        self.assertLess(order['post-control-plan.json']['mtime_ns'], order['Positive.json']['mtime_ns'])
        for name in ['protocol.json', 'post-control-plan.json']:
            self.assertEqual(order[name]['sha256'], hashlib.sha256((LOG / name).read_bytes()).hexdigest())
