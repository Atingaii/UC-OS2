"""OSStart 源码映射／边界结构检查；实际语义证据由 Coq 独立核对。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage76-start'


def strip_cast(node):
    while node['kind'] == 'ImplicitCastExpr':
        node, = node['inner']
    return node


def ref(node):
    node = strip_cast(node)
    assert node['kind'] == 'DeclRefExpr'
    return node['referencedDecl']['name']


class StartTests(unittest.TestCase):
    def test_replayed_exact_c_guard_call_and_store_order(self):
        evidence = json.loads((LOG / 'source/result.json').read_text())
        self.assertTrue(evidence['all94_identities_equal'])
        item = evidence['selected']['OSStart']
        self.assertEqual(item['identity']['preprocessed_body_sha256'],
                         'ace6a295a4176b3abbcb8cced0c44fa9af1a11d28b4b963dff565385f4d15f7c')
        branch, = item['clang_body']['inner']
        self.assertEqual(branch['kind'], 'IfStmt')
        guard, body = branch['inner']
        self.assertEqual((guard['kind'], guard['opcode']), ('BinaryOperator', '=='))
        lhs, rhs = guard['inner']
        self.assertEqual(ref(lhs), 'OSRunning')
        self.assertEqual(strip_cast(rhs)['value'], '0')
        first, a, b, c, last = body['inner']
        self.assertEqual([ref(x['inner'][0]) for x in (first, last)],
                         ['OS_SchedNew', 'OSStartHighRdy'])
        self.assertEqual([ref(x['inner'][0]) for x in (a, b, c)],
                         ['OSPrioCur', 'OSTCBHighRdy', 'OSTCBCur'])
        self.assertTrue(all(x['opcode'] == '=' for x in (a, b, c)))
        self.assertEqual(ref(a['inner'][1]), 'OSPrioHighRdy')
        array = strip_cast(b['inner'][1])
        self.assertEqual(array['kind'], 'ArraySubscriptExpr')
        self.assertEqual([ref(x) for x in array['inner']], ['OSTCBPrioTbl', 'OSPrioHighRdy'])
        self.assertEqual(ref(c['inner'][1]), 'OSTCBHighRdy')

    def test_manual_model_has_real_calls_and_no_new_trust_holes(self):
        paths = ['code/V293OSStart.v', 'proofs/V293OSSchedNewStartup.v', 'proofs/V293Start.v']
        project = (ROOT / '_CoqProject').read_text().splitlines()
        for name in paths:
            p = ROOT / 'certiucos/v293' / name
            self.assertIn(str(p.relative_to(ROOT)), project)
            text = re.sub(r'\(\*.*?\*\)', '', p.read_text(), flags=re.S)
            self.assertNotRegex(text, r'\b(Axiom|Admitted|admit|Parameter|Conjecture)\b')
            self.assertNotIn('CertiOS.audit', text)
        code = (ROOT / 'certiucos/v293/code/V293OSStart.v').read_text()
        self.assertIn('scall', code)
        self.assertIn('sifthen', code)
        self.assertIn('earrayelem', code)

    def test_startup_does_not_require_preexisting_current_task_or_port_body(self):
        startup = (ROOT / 'certiucos/v293/proofs/V293OSSchedNewStartup.v').read_text()
        proof = (ROOT / 'certiucos/v293/proofs/V293Start.v').read_text()
        signature = startup.split('Theorem V293_OSSchedNew_startup_fresh_call', 1)[1].split('Proof.', 1)[0]
        self.assertNotIn('CurLINV', signature)
        self.assertNotIn('CurTid', signature)
        self.assertIn('V293_init_fresh_four', startup)
        self.assertIn('V293_raw_cells_return_many', startup)
        port_signature = proof.split('Theorem V293_OSStart_call_to_port', 1)[1].split('Proof.', 1)[0]
        self.assertIn('sfexec port nil nil', port_signature)
        self.assertNotRegex(port_signature, r'P\s+port\s*=')
        self.assertIn('V293_ready_selection_task', proof)
        self.assertIn('V293_OSStart_already_running_call', proof)

    def test_literal_fixture_preserves_unimplemented_port_and_running_ablation(self):
        probe = (ROOT / 'audit/probes/V293StartProbe.v').read_text()
        self.assertIn('Theorem StartPortMissing : StartProgram 902%Z=None.', probe)
        self.assertIn('Vint32(if active then Int.one else Int.zero)', probe)
        for name in ['StartLiteralEntry', 'StartColdCall', 'StartWarmCall',
                     'StartAllPostReads', 'StartHighestCall']:
            self.assertIn('Theorem ' + name, probe)
        missing = json.loads((LOG / 'source/result.json').read_text())['unresolved_boundaries']
        self.assertTrue(any(x['name'] == 'OSStartHighRdy' and not x['defined'] for x in missing))

    def test_wrong_post_control_changes_only_pointer_not_proof_body(self):
        plan = json.loads((LOG / 'control-plan.json').read_text())
        positive = (LOG / 'Positive.v.snapshot.txt').read_text()
        wrong = (LOG / 'WrongCurrent.v.snapshot.txt').read_text()
        self.assertTrue(plan['frozen_before_compilation'])
        self.assertEqual(positive.count(plan['old']), 1)
        self.assertEqual(positive.replace(plan['old'], plan['new'], 1), wrong)
        self.assertEqual(hashlib.sha256(positive.encode()).hexdigest(), plan['positive_sha256'])
        self.assertEqual(hashlib.sha256(wrong.encode()).hexdigest(), plan['wrong_sha256'])
        self.assertEqual(json.loads((LOG / 'Positive.json').read_text())['exit'], 0)
        self.assertNotEqual(json.loads((LOG / 'WrongCurrent.json').read_text())['exit'], 0)
        output = (LOG / 'WrongCurrent.log').read_text()
        self.assertIn('StartColdCurrent', output)
        self.assertIn('Some Vnull', output)
