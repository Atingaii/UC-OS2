"""成功调用与原始后缀的结构回归；不替代 Coq 内核检查。"""
from pathlib import Path
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskCreateSuccessHoare.v'


class TaskCreateSuccessHoareTests(unittest.TestCase):
    def setUp(self):
        self.text = (ROOT / SOURCE).read_text()
        self.public = self.text.split('Theorem V293_OSTaskCreateExt_success_call_suffix_hoare :')[1].split('Proof.')[0]

    def test_original_call_and_suffix_composed(self):
        for term in ['sseq (V293_TaskCreateExt_TCB_call 209%Z f',
                     'V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z running sched',
                     'V293_TaskCreateExt_TCB_snapshot_call',
                     'V293_OSTaskCreateExt_idle_success_suffix_hoare']:
            self.assertIn(term, self.text)

    def test_same_full_snapshot_specification(self):
        for branch in ['empty', 'success']:
            for part in ['fpre', 'fpost']:
                self.assertIn('V293_tcb_' + branch + '_' + part, self.public)
        self.assertIn('Spec f=Some(fp,fq,(Tint8,rev V293_TCBInit_argument_types))', self.public)
        self.assertEqual(self.public.count('Spec f='), 1)

    def test_guards_come_from_actual_owned_bytes(self):
        for term in ['V293_create_success_err_read', 'V293_create_success_guards',
                     'V293_create_global_binding_env', 'V293_mapsto_load',
                     'evalval(ebinop oeq(evar running)(econst32 Int.one))',
                     'Amapsto(brun,0%Z)Tint8 false(Vint32 Int.zero)']:
            self.assertIn(term, self.text)

    def test_complete_post_and_caller_frame_retained(self):
        for term in ['getasrt(fq(V293_tcb_success_arguments',
                     'V293_create_tcb_arguments p top bottom identity size ext options F',
                     'V293_create_idle_running running brun ** F',
                     '[|result=Some(Vint32 Int.zero)|]']:
            self.assertIn(term, self.text)
        self.assertNotIn('GoodFrm F ->', self.text.split('Theorem V293_OSTaskCreateExt_idle_success_suffix_hoare :')[1].split('Proof.')[0])

    def test_no_execution_oracle_or_new_axiom(self):
        self.assertNotRegex(self.public, r'\b(evalval|evaladdr|load|sfexec|WFIFun)\b')
        self.assertNotRegex(self.text, r'\b(Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.probes.', self.text)
        self.assertIn('apply rete_rule', self.text)

    def test_nonvacuous_same_spec_entry_and_post_probe(self):
        probe = (ROOT / 'audit/probes/V293TaskCreateSuccessHoareProbe.v').read_text()
        for name in ['IdleSameSpecCallee', 'IdleHoareChecked', 'IdleLiteralEntry',
                     'IdleEntrySatisfiable', 'IdleLiteralPost', 'IdlePostSatisfiable',
                     'IdleLiteralPhysicalPost']:
            self.assertRegex(probe, r'(?:Lemma|Theorem) ' + name + r'\s*:')
        self.assertIn('apply CallCalleeContractChecked.', probe)
        self.assertNotIn('Definition IdleSpec', probe)
        project = (ROOT / '_CoqProject').read_text().splitlines()
        self.assertEqual(project.count(SOURCE), 1)
