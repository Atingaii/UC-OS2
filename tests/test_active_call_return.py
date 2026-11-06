"""真实分配、切回及返回回归；文本检查不替代 Coq 内核检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage268-active-call-return'
PROD = 'certiucos/v293/proofs/V293OSIntExitSwitchReturn.v'
PROBE = 'audit/probes/V293ActiveCallReturnProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class ActiveCallReturnTests(unittest.TestCase):
    def test_old_inputs_and_exact_registration_delta(self):
        base = read('baseline.json')['files']
        for p, h in base.items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md', '_CoqProject']:
                self.assertEqual(sha(R / p), h, p)
        project = (R / '_CoqProject').read_bytes()
        self.assertEqual(project.count((PROD + '\n').encode()), 1)
        self.assertEqual(hashlib.sha256(project.replace((PROD + '\n').encode(), b'')).hexdigest(), base['_CoqProject'])
        self.assertNotIn(PROBE, project.decode())
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h, p)
        lines = (R / 'csrc/upstream/v2.93.01/checkout/Source/os_core.c').read_text().splitlines()
        for n, anchor in read('source-identity.json')['line_anchors'].items():
            self.assertEqual(lines[int(n) - 1].strip(), anchor)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- active-call-return-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), base[p])

    def test_production_original_continuation_and_resource_construction(self):
        src = (R / PROD).read_text()
        body = theorem(src, 'V293_int_exit_switch_resume_return')
        statement = body.split('Proof.', 1)[0]
        for term in ['kseq (sprim excrit) (kseq sret (kcall f body caller ks))',
                     'GoodInvAsrt R', 'V293_owned_record_cell', 'Amapsto (b,0%Z) Tint32 true v ** R']:
            self.assertIn(term, statement)
        self.assertNotIn('ProgSim', statement)
        for term in ['V293_owned_record_cell_update', 'pswitch_step', 'V293_int_exit_pending_return',
                     'get Mf (b,i)=None', 'V293_storebytes_outside']:
            self.assertIn(term, body)
        self.assertNotIn('CertiOS.audit', src)

    def test_entry_to_same_allocated_saved_return(self):
        src = (R / PROBE).read_text()
        body = theorem(src, 'ARroundtrip')
        statement = body.split('Proof.', 1)[0]
        self.assertNotIn('ProgSim', statement)
        self.assertIn('fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->', statement)
        self.assertEqual(statement.count('->'), 3)  # Two fresh premises and the byte-range quantifier.
        for term in ['ARfirst_switch', 'ARprepare', 'ARresume', 'V293_global_trans']:
            self.assertIn(term, body)
        for term in ['free Tint32 bs Ms=Some Mf', 'get Mf(bs,i)=None',
                     'set(ARsavedenvs bs)OwnershipWaiting emp']:
            self.assertIn(term, statement)
        for name, terms in {
            'ARenter': ['sfexec 114%Z nil nil', 'allocb', 'V293_global_steps'],
            'ARto_switch': ['FTfixed_prefix', 'V293_handoff_copy_execution', 'V293_local_steps_global', 'ARenter'],
            'ARfirst_switch': ['V293_ready_switch_step', 'ARsuspended'],
            'ARprepare': ['ARtable', 'ARcells', 'V293_assign_pointer_execution'],
            'ARresume': ['V293_int_exit_switch_resume_return', 'V293_record_star_load_l'],
            'ARnonvacuous': ['memory_has_fresh_block(NPinitial 1)', 'memory_has_fresh_block(QPmemory br 1 1)', 'ARroundtrip'],
        }.items():
            for term in terms:
                self.assertIn(term, theorem(src, name))
        metadata = theorem(src, 'ARendpoint_metadata')
        for term in ['get ARtasks OwnershipWaiting=Some(curs(sfexec',
                     'get ARsuspended OwnershipWaiting=Some RPpending',
                     'get ARdone OwnershipWaiting=Some(SKIP,(kenil,kstop))',
                     'get ARdone OwnershipReady=Some(SKIP,(kenil,CPcall))']:
            self.assertIn(term, metadata)

    def test_actual_same_heap_single_factor_stack_control(self):
        body = theorem((R / PROBE).read_text(), 'ARstack_control')
        statement = body.split('Proof.', 1)[0]
        self.assertEqual(statement.count('V293_global_steps'), 3)
        self.assertEqual(body.count('destruct(ARresume'), 2)
        for term in ['ARfirst_switch', 'ARprepare', 'good_inv_prop', 'assert(Msn=Ms)by congruence',
                     'assert(Mfn=Mf)by congruence', 'false,nil,true::ci', 'true,nil,ci',
                     'get a OwnershipWaiting']:
            self.assertIn(term, body)

    def test_stable_compile_recursive_trust_and_protocol(self):
        sources = [PROD, PROBE]
        roots = []
        for p in sources:
            src = (R / p).read_text()
            self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        for p, labels in read('stable-compiles.json').items():
            for label in labels:
                row = read(label + '.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
                self.assertEqual(row['source_sha256'], sha(R / p))
        trust = read('trust.json')
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertEqual(list(read('assumptions-by-root.json')), roots)
        self.assertLessEqual(set(trust['assumptions']),
                             {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])

    def test_claim_boundaries_and_entry_deviation_disclosed(self):
        doc = (R / 'audit/STAGE268_ACTIVE_CALL_RETURN.md').read_text()
        for term in ['环境 fixture，不是真实调度器', '仍然 blocked', '不是所有路径 OSIntExit',
                     '公平性', 'sfexec', '协议原写 scall 入口', '不是**同一固定 C 内核',
                     '初态不同于第267步', '切回快照资源', 'cache 仍沿用4',
                     '不是 GOOD_OS', '不是 WFInt', 'K1–K4 未闭合', 'uCOS3 未开始',
                     '未提交／推送', 'ADR-0005/0010', '不是通过早期契约拒绝', 'B **没有返回**']:
            self.assertIn(term, doc)
