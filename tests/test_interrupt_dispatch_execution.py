"""末层中断的真实调度执行；结构回归不能代替 Coq 语义证明。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage196-interrupt-dispatch-execution'
PROD = 'certiucos/v293/proofs/V293OSIntExitDispatchExecution.v'
PROBE = 'audit/probes/V293OSIntExitDispatchExecutionProbe.v'


def read(name):
    return json.loads((D / name).read_text())


class InterruptDispatchExecutionTests(unittest.TestCase):
    def test_exact_both_sources_and_prospective_protocol(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        self.assertEqual([f['function']['name'] for f in source['functions']], ['OSIntExit', 'OS_SchedNew'])
        for f in source['functions']:
            self.assertTrue(f['reconstructed_repaired_source_matches'])
            self.assertTrue(f['temporary_source_removed_on_context_exit'])
            name = f['function']['name'] + '.configured.c.txt'
            self.assertEqual(hashlib.sha256((D / name).read_bytes()).hexdigest(), f['function']['preprocessed_definition_sha256'])
        for p, h in source['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
            self.assertEqual(h, read('baseline.json')['files'][p])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(), read('protocol-identity.json')['protocol.json'])
        old = R / 'audit/logs/stage195-interrupt-call-execution/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_main_interface_actual_call_no_execution_allocation_store_oracle(self):
        src = (R / PROD).read_text()
        stmt = src.split('Theorem V293_OSIntExit_dispatch_prefix_execution :', 1)[1].split('Proof.', 1)[0]
        pre = stmt.split('exists tasks,', 1)[0]
        for token in ('cstepstar', 'V293_local_steps', 'fresh M', 'store ', 'callcont', 'InfRules', 'Spec', 'load Tint8 M(bn,'):
            self.assertNotIn(token, pre)
        for token in ('P f=Some(V293_OSSchedNew_function', 'GoodInvAsrt R', 'current counter int_switch',
                      'V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 1)',
                      'free Tint8 b Ms=Some Mskip', 'get Mskip(b,0%Z)=None',
                      'curs(sif(V293_OSSched_different high current)', 'V293_scheduler O next',
                      'c<>bo', '(c,i)<>(bh,0%Z)', '(c,i)<>(bn,0%Z)'):
            self.assertIn(token, stmt)
        for token in ('V293_owned_record_cell_update', 'V293_ready_dispatch_call',
                      'V293_exit_one_decrement_execution', 'V293_exit_zero_guards_enter'):
            self.assertIn(token, src)
        self.assertNotIn('CertiOS.audit.', src)

    def test_independent_nonempty_positive_and_actual_priority_branches(self):
        src = (R / PROBE).read_text()
        for token in ('Lemma DXentry :', 'apply DXold_entry.', 'apply OwnershipCellsSpatial.',
                      'Theorem DXprefix :', 'RTonly_ready', 'Theorem DXsame_priority_complete_middle :',
                      'Theorem DXdifferent_priority_enters_change :', 'DXpriority4_eval', 'DXpriority6_eval',
                      'apply sviff_step', 'apply svift_step', 'load Tint32 Mf(97%positive,0%Z)=Some(Vint32(Int.repr 19))',
                      'load Tint8 Mf(90%positive,0%Z)=Some(V293_byteval 99)'):
            self.assertIn(token, src)
        stmt = src.split('Theorem DXsame_priority_complete_middle :', 1)[1].split('Proof.', 1)[0]
        self.assertNotIn('->', stmt)
        self.assertIn('(curs(sskip None),(kenil,ks))', stmt)
        self.assertIn('DXmemory 1 4', stmt)
        self.assertIn('Some(Vptr OwnershipReady)', stmt)
        self.assertIn('Theorem DXswitch_body_absent : RCprogram 112%Z=None.', src)

    def test_single_factor_whole_heap_controls_and_real_omission_execution(self):
        src = (R / PROBE).read_text()
        for name, byte in (('DXcurrent_only', 96), ('DXnesting_only', 94)):
            stmt = src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]
            self.assertIn(f'(b,i)<>({byte}%positive,0%Z)', stmt)
            self.assertIn('get(DXmemory', stmt)
            self.assertNotIn('load ', stmt)
        for token in ('Theorem DXnested_two_skips_dispatch :', 'DXmemory 2 4',
                      'V293_OSIntExit_nested_middle_execution',
                      'Theorem DXomit_decrement_skips_dispatch :',
                      'curs(V293_OSIntExit_guards 108%Z 109%Z DXdispatch)',
                      'Some(Vptr OwnershipWaiting)', 'V293_success_global_byte_eq'):
            self.assertIn(token, src)
        omitted = src.split('Theorem DXomit_decrement_skips_dispatch :', 1)[1].split('Proof.', 1)[0]
        self.assertNotIn('->', omitted)
        self.assertIn('(DXge,RTle,DXmemory 1 4)', omitted)

    def test_stable_compiles_recursive_trust_and_no_new_holes(self):
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
        self.assertEqual(trust['roots_printed'], 26)
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))
