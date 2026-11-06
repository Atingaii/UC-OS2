"""Hook 资源边界的结构回归；语义结论由 Coq／coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage129-tcb-hook-frame'
SOURCE = 'certiucos/v293/proofs/V293TCBHookFrame.v'
PROBE = 'audit/probes/V293TCBHookFrameProbe.v'


class TCBHookFrameTests(unittest.TestCase):
    def setUp(self):
        self.source = (R / SOURCE).read_text()
        self.probe = (R / PROBE).read_text()

    def section(self, name, probe=False):
        text = self.probe if probe else self.source
        return text.split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_no_holes_audit_dependency_or_duplicate_registration(self):
        for text in [self.source, self.probe]:
            self.assertNotRegex(text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.', self.source)
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

    def test_original_impossible_premise_is_explicitly_rejected(self):
        negative = self.section('V293_tcb_hook_former_premise_rejected')
        self.assertIn('~ GoodFunAsrt(V293_create_owned_share', negative)
        self.assertIn('V293_tcb_publication_globals', negative)
        self.assertIn('exact(proj1(proj2 H))', negative)
        red = json.loads((D / 'rejected01.json').read_text())
        self.assertEqual(red['exit'], 1)
        self.assertIn('GoodFunAsrt (V293_tcb_publication_globals', (D / 'rejected01.log').read_text())

    def test_independent_controls_isolate_local_facts_not_permissions(self):
        positive = self.section('HFPositive', True)
        self.assertIn('GoodFunAsrt(HFOwner ** FPR)', positive)
        self.assertIn('V293_reservation_owner', positive)
        self.assertNotIn('V293_tcb_hook_owner_accepted', positive)
        for name, text in [('HFNegative', '~ GoodFunAsrt(HFOwner ** (HFGlobals ** FPR))'),
                           ('HFOwnerOnly', 'GoodFunAsrt(HFOwner ** Aemp)'),
                           ('HFGlobalOnly', 'GoodFunAsrt(Agvarenv'),
                           ('HFLocalOnly', '~ GoodFunAsrt(A_notin_lenv')]:
            self.assertIn(text, self.section(name, True))

    def test_typed_hook_entries_exclude_caller_environment(self):
        whole = self.section('V293_OS_TCBInit_site_hook_framed')
        signature = whole.split('Proof.', 1)[0]
        hooks = signature.split(' Spec hi=Some', 1)[1].split(' (V293_tcb_enabled_state', 1)[0]
        self.assertNotIn('V293_tcb_publication_globals', hooks)
        self.assertIn('(good:GoodFunAsrt(V293_create_owned_share table reserved p ** R))', signature)
        self.assertIn('(proj2 good)', hooks)
        self.assertIn('V293_tcb_publication_globals bh bg br bn ** R', signature)
        self.assertIn('V293_tcb_publication_globals bh bg br bn ** V293_tcb_priority_caller_frame', whole)

    def test_full_original_body_retains_all_actual_operations(self):
        whole = self.section('V293_OS_TCBInit_site_hook_framed')
        for name in ['V293_TCBInit_function_body hi hc',
                     'V293_OS_TCBInit_site_free_body_with_success', 'V293_tcb_allocated_fields',
                     'V293_OS_TCBInit_owned_suffix_after_first_hook', 'V293_tcb_priority_first_hook',
                     'V293_tcb_full_priority_restore', 'V293_tcb_full_publication_view',
                     'V293_OS_TCBInit_publish_finite_enabled', 'V293_tcb_full_publication_restore',
                     '(b,off)<>reserved', 'r(Some(Vint32(Int.repr 66)))', 'r(Some(Vint32 Int.zero))']:
            self.assertIn(name, whole)
        self.assertNotIn('V293_OS_TCBInit_site_allocated_finite_published', whole)

    def test_same_joint_inv_derives_six_borrows_not_assumes_them(self):
        signature, proof = self.section('V293_OS_TCBInit_creator_joint_hook_framed').split('Proof.', 1)
        self.assertIn('V293_create_joint_inv', signature)
        self.assertIn('(fun _=>false)', signature)
        for name in ['Kfree', 'Kprio', 'Kpub', 'FreeOpen', 'FreeClose', 'PriorityOpen', 'PubOpen']:
            self.assertNotIn(name, signature)
        for name in ['free', 'priority', 'publication']:
            self.assertEqual(proof.count('V293_create_joint_borrow_' + name), 2)
        self.assertIn('V293_OS_TCBInit_site_hook_framed', proof)

    def test_literal_caller_frame_and_actual_typed_calls(self):
        for name in ['HFGlobalsLiteral', 'HFCallerLiteral', 'HFCallerShadowRejected']:
            self.assertIn('Proof.', self.section(name, True))
        literal = self.section('HFCallerLiteral', True)
        self.assertIn('HFCallerState emp |= HFOwner ** HFGlobals', literal)
        self.assertIn('V293_encoded_memory_mapsto', literal)
        shadow = self.section('HFCallerShadowRejected', True)
        self.assertIn('HFCallerState HFShadow |= HFOwner ** HFGlobals', shadow)
        self.assertIn('exists(701%positive,Tint8)', shadow)
        for i in [1, 2]:
            call = self.section('HFCall' + str(i), True)
            self.assertIn('V293_tcb_priority_first_hook', call)
            self.assertIn('HFFrameGood', call)
            self.assertIn('HFLookup' + str(i), call)
            self.assertIn('scall ' + str(989 + i) + '%Z[evar 108%Z]', call)

    def test_stable_compilations_and_honest_limits(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('proof', SOURCE), ('probe', PROBE)]:
            label = stable[kind]
            row = json.loads((D / (label + '.json')).read_text())
            data = (R / path).read_bytes()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(hashlib.sha256(data).hexdigest(), row['initial_source_sha256'])
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(data, (D / (label + '.v.snapshot.txt')).read_bytes())
        doc = (R / 'audit/STAGE129_TCB_HOOK_FRAME.md').read_text()
        for text in ['前提无法实例化', '不是生产全局Inv', '单因素', '不是 Hook 函数体',
                     'token freshness', 'fpre', 'fpost', 'WFIFun', 'GOOD_OS', 'uCOS3', '423']:
            self.assertIn(text, doc)


if __name__ == '__main__':
    unittest.main()
