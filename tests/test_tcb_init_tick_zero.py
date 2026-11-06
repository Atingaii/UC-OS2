"""实际初始化字段与同堆零延时一步；文本检查不替代Coq内核。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage335-tcb-init-tick-zero'
P = 'certiucos/v293/proofs/V293TCBInitTickZero.v'
Q = 'audit/probes/V293TCBInitTickZeroProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class TCBInitTickZeroTests(unittest.TestCase):
    def test_fixed_configured_source_replayed(self):
        rows = read('source-identities.json')
        self.assertEqual({r['name'] for r in rows}, {'OS_TCBInit', 'OSTimeTick'})
        self.assertEqual(read('source-replay.json')['exit'], 0)
        inventory = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        for row in rows:
            self.assertIn(row, inventory['functions'])
            self.assertEqual(sha(D / (row['name'] + '.source.c.snapshot.txt')), row['source_lines_sha256'])
            data = (D / (row['name'] + '.configured.c.snapshot.txt')).read_bytes()
            self.assertEqual(hashlib.sha256(data[:-1]).hexdigest(), row['preprocessed_definition_sha256'])
        self.assertIn('ptcb->OSTCBDly = 0u;', (D / 'OS_TCBInit.configured.c.snapshot.txt').read_text())
        tick = (D / 'OSTimeTick.configured.c.snapshot.txt').read_text()
        self.assertIn('if (ptcb->OSTCBDly != 0u)', tick)
        self.assertIn('ptcb = ptcb->OSTCBNext;', tick)

    def test_stable_interface_has_no_success_oracle(self):
        s = (R / P).read_text()
        st, proof = s.split('Theorem V293_TCBInit_fields_then_zero_iteration :', 1)[1].split('Proof.', 1)
        inputs, outputs = st.split(' exists Mi Mf,', 1)
        for token in ['load ', 'store ', 'evalval', 'cstep', 'V293_local_steps', 'TaskSim']:
            self.assertNotIn(token, inputs)
        for token in ['V293_tcb_init_old_fields bt base old', 'V293_tcb_init_env le',
                      'V293_tcb_init_values_valid', 'p<13', 'V293_owned_record_cell']:
            self.assertIn(token, inputs)
        for token in ['V293_OS_TCBInit_fields_execution', 'V293_rdy_raw_load',
                      'V293_initialized_tick_resources', 'V293_tick_zero_iteration_owned_execution']:
            self.assertIn(token, proof)
        self.assertIn('load Tint32 Mi(bt,(base+44)%Z)=Some(Vint32 Int.zero)', outputs)
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertNotRegex(s, r'Require Import CertiOS\.(?:ucos|os_code|os_proof)\.')

    def test_all_fields_and_frame_retained(self):
        s = (R / P).read_text()
        spares = s.split('Definition V293_tcb_tick_spares', 1)[1].split('Lemma ', 1)[0]
        self.assertIn('V293_tcb_init_record_remainder', spares)
        self.assertIn('firstn 2 cells++skipn 3 cells', spares)
        original = (R / 'certiucos/v293/proofs/V293StartRecord.v').read_text()
        remainder = original.split('Definition V293_tcb_init_record_remainder', 1)[1].split('Lemma ', 1)[0]
        offsets = re.findall(r'base\+(\d+)', remainder)
        self.assertEqual(len(offsets), 11)
        self.assertEqual(offsets[2], '44')
        self.assertEqual(len(offsets[:2] + offsets[3:]), 10)
        adapter = s.split('Lemma V293_initialized_tick_resources :', 1)[1].split('Theorem ', 1)[0]
        for token in ['V293_initialized_ready_record', 'V293_raw_record_ownership',
                      'V293_owned_task_record', 'V293_tick_zero_node',
                      'tl(V293_tcb_init_input_cells', 'V293_tcb_tick_spares', ' R)']:
            self.assertIn(token, adapter)

    def test_positive_reuses_original_nonempty_entry(self):
        s = (R / Q).read_text()
        self.assertNotIn('Definition TZmemory', s)
        self.assertNotIn('Definition TZentry', s)
        self.assertEqual(sha(R / 'audit/probes/V293TCBInitFieldsProbe.v'),
                         'e1433347c92b75740ba5e69ed53b260bd8dfa25edd28f1b4e3639a7cab466b04')
        entry = s.split('Lemma TZentry :', 1)[1].split('Theorem TZactual_init_then_tick', 1)[0]
        self.assertIn('InitLiteralEntry 11', entry)
        actual = s.split('Theorem TZactual_init_then_tick :', 1)[1].split('(* Only delay44', 1)[0]
        self.assertTrue(actual.startswith(' forall P ki kt,exists Mi Mf,'))
        self.assertIn('(fun _:Z=>Vundef)TZnext', actual)
        self.assertIn('InitEnvironment(InitValues 11)TZentry', actual)
        self.assertNotIn('TZcandidate', actual)
        self.assertNotIn(' ->', actual.split('Proof.', 1)[0].split('(forall b i,', 1)[0])

    def test_same_initialized_heap_and_real_iteration(self):
        s = (R / P).read_text()
        outputs = s.split(' exists Mi Mf,', 1)[1].split('Proof.', 1)[0]
        for token in ['(ge,le,M)(curs(sskip None),(kenil,ki))(ge,le,Mi)',
                      '((ge,le,Mi),ir,(enabled,si,ci))', '((ge,le,Mf),ir,(enabled,si,ci))',
                      'store(Tptr V293_tcb_type)Mi(bc,0%Z)(Vptr next)=Some Mf',
                      'get Mf(b,i)=get Mi(b,i)', 'V293_owned_task_record', 'V293_tick_zero_node']:
            self.assertIn(token, outputs)
        original = (R / 'certiucos/v293/proofs/V293TimeTickTraversal.v').read_text()
        execution = original.split('Theorem V293_tick_zero_iteration_owned_execution', 1)[1].split('Qed.', 1)[0]
        for token in ['encrit_step', 'excrit_step', 'V293_tick_delay', 'sviff_step', 'V293_tick_advance']:
            self.assertIn(token, execution)

    def test_prospective_single_factor_resource_ablation(self):
        self.assertEqual(sha(D / 'protocol.json'), 'e3871e2184ad5bd8d67b919392d4f0c07f149d862afea139fb1f714e1352591b')
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
        protocol = read('protocol.json')
        self.assertTrue(protocol['prospective'])
        self.assertEqual(protocol['ablation']['factor'], 'remove only the runtime-zero resource requirement from the ready-node interface')
        self.assertIn('not an executed mutant initializer', protocol['ablation']['scope'])
        s = (R / Q).read_text()
        family = s.split('Definition TZcells d:', 1)[1].split('Definition TZcandidate d', 1)[0]
        self.assertEqual(family.count('Vint32 d'), 1)
        self.assertIn('TZcanonical++', family)
        self.assertIn('((301%positive,52%Z),Tint32,Vint32 d)', family)
        for token in ['Theorem TZready_record_insufficient', 'Theorem TZzero_gate_passes',
                      'TZcandidate_owned(Int.repr 3)', 'rewrite TZcandidate_delay in Zero;discriminate',
                      'Theorem TZsingle_factor_outside', '(i<52)%Z \/(56<=i)%Z',
                      'get(TZcandidate d1)(b,i)=get(TZcandidate d2)(b,i)', 'V293_encoded_memory_outside']:
            self.assertIn(token, s)

    def test_recursive_kernel_check_and_repeat_compilation(self):
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
        trust = read('trust.json')
        self.assertEqual(len(roots), 11)
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], 11)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']), {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        for name, p in [('production', P), ('probe', Q)]:
            for i in [1, 2]:
                row = read(f'stable-{name}-{i}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / p))
                self.assertEqual(row['source_sha256'], sha(R / p))

    def test_history_append_contract_and_bounded_claims(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in read('baseline.json')['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        for n in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / n).read_bytes().endswith((D / (n + '.baseline')).read_bytes()))
        prefix = (D / '_CoqProject.baseline').read_bytes() + (P + '\n').encode()
        current = (R / '_CoqProject').read_bytes()
        self.assertTrue(current.startswith(prefix))
        self.assertTrue(all(line.startswith('certiucos/v293/') and line.endswith('.v')
                            for line in current[len(prefix):].decode().splitlines()))
        doc = (R / 'audit/STAGE335_TCB_INIT_TICK_ZERO.md').read_text()
        for token in ['GOOD_OS', 'K1–K4', 'uCOS3', '总目标保持active', '手工源码模型',
                      '不是合法ISR', '不是完整OS_TCBInit', '不是完整OSTimeTick',
                      '不是head/Next的初始化来源', '不是执行突变初始化器', 'canonical ready记录本身不拥有delay44']:
            self.assertIn(token, doc)
