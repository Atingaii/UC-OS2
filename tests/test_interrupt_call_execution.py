"""函数入口/分配/返回的回归；结构检查不代替 Coq 语义证明。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage195-interrupt-call-execution'
PROD = 'certiucos/v293/proofs/V293OSIntExitCallExecution.v'
PROBE = 'audit/probes/V293OSIntExitCallExecutionProbe.v'


def read(name):
    return json.loads((D / name).read_text())


class InterruptCallExecutionTests(unittest.TestCase):
    def test_exact_source_and_frozen_protocol(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        for p, h in source['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
            self.assertEqual(h, read('baseline.json')['files'][p])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(), read('protocol-identity.json')['protocol.json'])
        old = R / 'audit/logs/stage194-interrupt-nested-execution/checkpoint-evidence-manifest-final.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_actual_entry_allocation_without_execution_or_store_oracle(self):
        src = (R / PROD).read_text()
        stmt = src.split('Theorem V293_OSIntExit_nested_call_execution :', 1)[1].split('Proof.', 1)[0]
        pre = stmt.split('exists bs Mf,', 1)[0]
        for token in ('V293_local_steps', 'fresh M', 'store ', 'NoDup', 'callcont', 'Spec', 'InfRules'):
            self.assertNotIn(token, pre)
        for token in ('P f=Some(V293_OSIntExit_abstract_function', '2<=n', 'n<256',
                      'exists old,get M(bn,0%Z)=Some(true,old)', 'curs(scall f nil)',
                      '((ge,caller,Mf),ir,(enabled,si,ci))', 'get Mf(bs,Z.of_nat k)=None'):
            self.assertIn(token, stmt)
        for token in ('memory_has_fresh_block', 'snpcall_step', 'sfexec_step',
                      'salloclv_step', 'sallocend_step', 'V293_OSIntExit_nested_execution',
                      'V293_put_byte_store', 'V293_success_scheduler_storage'):
            self.assertIn(token, src)
        self.assertNotIn('CertiOS.audit.', src)

    def test_nonempty_complete_execution_shadowing_and_both_boundaries(self):
        src = (R / PROBE).read_text()
        for token in ('Theorem CLnested_call_witness :', 'Lemma CLentry_loads :',
                      'Corollary CLnest2 :', 'Corollary CLnest255 :',
                      'Definition CLprogram : progunit := fun f=>if Z.eq_dec f 300%Z then Some CLfunction else None.',
                      'Theorem CLno_other_callee :', 'Theorem CLcaller_shadow :',
                      'sig 601%Z(54%positive,Tint8)', '100%Z(53%positive,Tint8)',
                      'load Tint8 Mf(53%positive,0%Z)=Some(V293_byteval 0)',
                      'load Tint8 Mf(54%positive,0%Z)=Some(V293_byteval 23)'):
            self.assertIn(token, src)
        stmt = src.split('Theorem CLnested_call_witness :', 1)[1].split('Proof.', 1)[0]
        self.assertNotIn('store ', stmt)
        self.assertIn('forall n ir enabled si ci,2<=n ->n<256', stmt)

    def test_single_factor_entry_controls_are_actual_semantic_no_steps(self):
        src = (R / PROBE).read_text()
        for name in ('CLmissing_function_no_step', 'CLreject_extra_argument'):
            stmt = src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]
            self.assertIn("~exists C' st',loststep", stmt)
            self.assertIn('curs(sfexec 300%Z', stmt)
            self.assertNotIn('BuildPreI', stmt)
        self.assertIn('V293_missing_port_has_no_step', src)
        self.assertIn('H:tlmatch _ dnil', src)
        self.assertIn('Vint32 Int.zero::nil', src)

    def test_stable_compiles_recursive_trust_and_no_holes(self):
        stable = read('stable-compiles.json')
        for kind, p in (('body', PROD), ('probe', PROBE)):
            row = read(stable[kind] + '.json')
            h = hashlib.sha256((R / p).read_bytes()).hexdigest()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(h, row['initial_source_sha256'])
            self.assertEqual(h, row['source_sha256'])
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
        trust = read('trust.json')
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(trust['roots_printed'], len(trust['roots']))
        self.assertEqual(trust['roots_printed'], 9)
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))
