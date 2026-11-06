"""结构回归仅检查接线/证据；Coq内核和实际语义fixture才是证明。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage82-init-publish-records'
PROOF = ROOT / 'certiucos/v293/proofs/V293InitPublishRecords.v'
PROBE = ROOT / 'audit/probes/V293InitPublishRecordsProbe.v'


class InitPublishRecordsTests(unittest.TestCase):
    def test_continuous_real_prefix_priority_publication_and_free(self):
        s = PROOF.read_text()
        self.assertIn(str(PROOF.relative_to(ROOT)), (ROOT / '_CoqProject').read_text().splitlines())
        for part in ['V293_OS_TCBInit_prefix_execution P', 'apply V293_initialized_ready_record',
                     'eapply V293_task_records_insert', 'V293_TCBInit_prefix_to_record_hook tasks P',
                     'V293_OS_TCBInit_priority_to_second_hook P',
                     'V293_OS_TCBInit_publication_return_preserves_records tasks P',
                     'exact Prefix', 'exact FirstExec', 'exact PriorityExec', 'exact SecondExec', 'exact Suffix']:
            self.assertIn(part, s)
        self.assertNotIn('CertiOS.audit', s)
        self.assertNotRegex(re.sub(r'\(\*.*?\*\)', '', s, flags=re.S),
                            r'\b(Axiom|Parameter|Conjecture|Admitted|admit)\b')

    def test_hooks_are_actual_independent_resource_preserving_contracts(self):
        s = PROOF.read_text()
        contract = s.split('Definition V293_records_hook_return')[1].split('(* This prefix')[0]
        for part in ['forall Mh', 'exists Mr', 'curs(sfexec hook', 'curs(sskip None)',
                     'V293_owned_task_records tasks ** V293_rdy_raw_cells cells Atrue']:
            self.assertIn(part, contract)
        self.assertEqual(contract.count('V293_owned_task_records tasks **'), 2)
        self.assertNotIn('prefix_return_records_under_hooks', contract)
        self.assertIn('destruct (Hook1 Mi Initialized)', s)
        self.assertIn('destruct (Hook2 Mh SecondOwned)', s)
        sig = s.split('Theorem V293_OS_TCBInit_prefix_return_records_under_hooks :')[1].split('Proof.')[0]
        entry = sig.split('(ge,le,M,ir,aux,O,op) |=')[1].split('exists Mf,')[0]
        self.assertIn('V293_owned_task_records tasks ** Atrue', entry)
        self.assertNotIn('V293_owned_task_records tasks\'', entry)
        self.assertNotIn('curs(sfexec f', sig)

    def test_return_preserves_joint_finite_resources_with_explicit_support(self):
        s = PROOF.read_text().split('Theorem V293_OS_TCBInit_prefix_return_records_under_hooks :')[1]
        for part in ['In (t,value) (TcbMod.lst tasks\') -> ~In (fst t) blocks',
                     'In (a,tp,v) (tl after++survivors) -> ~In (fst a) blocks',
                     'V293_rdy_raw_cells (tl after++survivors) Atrue',
                     '(curs(sskip(Some(Vint32 Int.zero))),(kenil,ks)) ((ge,caller,Mf)',
                     'get Mf (b,Z.of_nat k)=None']:
            self.assertIn(part, s)
        self.assertNotIn('V293_tcb_init_final_fields', s)

    def test_independent_uninitialized_literal_and_exact_compiled_sources(self):
        inv = json.loads((LOG / 'literal-inventory.json').read_text())
        self.assertEqual((inv['cells'], inv['bytes']), (44, 114))
        self.assertEqual(sum(x[4] for x in inv['items']), 114)
        for label, path in [('proof07', PROOF), ('probe05', PROBE)]:
            row = json.loads((LOG / (label + '.json')).read_text())
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['source_sha256'], hashlib.sha256(path.read_bytes()).hexdigest())
            self.assertEqual(path.read_bytes(), (LOG / (label + '.v.snapshot.txt')).read_bytes())
        s = PROBE.read_text()
        for part in ['(301%positive,Int.repr 8)', '(301%positive,Int.repr 128)',
                     'Definition ChainInitial := ChainOldFields++',
                     'Definition ChainCaller : env := sig 777%Z',
                     'ChainHooks P f hi hc ks enabled si ci false ->',
                     'ChainHooks P f hi hc ks enabled si ci true ->',
                     'V293_task_records Mf ChainUpdated /\\ ChainReads Mf /\\ ChainFreed Mf']:
            self.assertIn(part, s)
        fields = s.split('Definition ChainOldFields :')[1].split('Definition ChainInputs')[0]
        self.assertEqual(fields.count('(Vundef)'), 18)

    def test_actual_prefix_negative_is_not_claimed_as_downstream_success(self):
        s = PROBE.read_text()
        for part in ['Theorem ChainPrefixExcludesWrong', 'Theorem ChainActualMissingHook',
                     'destruct (ChainPrefix P f hi hc ks enabled si ci)',
                     'apply V293_missing_hook_cannot_return',
                     'rewrite Read in Physical. discriminate.',
                     'load (Tptr V293_tcb_type) M (406%positive,44%Z)',
                     'load (Tptr V293_tcb_type) M (405%positive,0%Z)',
                     'load (Tptr Tint32) M (301%positive,128%Z)']:
            self.assertIn(part, s)
        self.assertTrue(json.loads((LOG / 'controls.json').read_text())['passed'])

    def test_prospective_same_proof_single_factor_control(self):
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
