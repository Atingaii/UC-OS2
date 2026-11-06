"""同入口活跃调用有限执行回归；字符串/身份检查不替代 Coq。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage267-active-call-trace'
PROBE = 'audit/probes/V293ActiveCallTraceProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class ActiveCallTraceTests(unittest.TestCase):
    def test_frozen_sources_and_registration_unchanged(self):
        for p, h in read('baseline.json')['files'].items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md']:
                self.assertEqual(sha(R / p), h, p)
        identity = read('source-identity.json')
        for p, h in identity['files'].items():
            self.assertEqual(sha(R / p), h, p)
        lines = (R / 'csrc/upstream/v2.93.01/checkout/Source/os_core.c').read_text().splitlines()
        for line, anchor in identity['line_anchors'].items():
            self.assertEqual(lines[int(line) - 1].strip(), anchor)
        self.assertNotIn(PROBE, (R / '_CoqProject').read_text())

    def test_original_entry_actual_execution_and_storage(self):
        src = (R / PROBE).read_text()
        body = theorem(src, 'FTfinite_call')
        statement = body.split('Proof.', 1)[0]
        self.assertNotIn('ProgSim', statement)
        self.assertIn('fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->', statement)
        for term in ['(FWtasks,FWos br cs ncs,OwnershipWaiting)',
                     '(FTreturned,FTreturnstate br bs Mret cs ncs,OwnershipReady)',
                     'free Tint32 98%positive Msw=Some Mret',
                     'get Mret(98%positive,i)=None',
                     'load Tint32 Mret(bs,0%Z)=Some(Vint32 Int.zero)',
                     'FTto_switch br bs cs ncs ip FR FS', 'V293_ready_switch_step',
                     'V293_int_exit_pending_return', 'exact Switch|exact Return',
                     'V293_load_block_frame', 'good_inv_prop']:
            self.assertIn(term, body)
        for name, terms in {
            'FTenter': ['sfexec 114%Z nil nil', 'V293_global_steps', 'allocb'],
            'FTto_switch': ['FTfixed_prefix', 'V293_handoff_copy_execution', 'V293_local_steps_global', 'FTenter'],
            'FTfixed_prefix': ['FWinitial_owned', 'FTbody_prefix', 'RTonly_ready'],
        }.items():
            for term in terms:
                self.assertIn(term, theorem(src, name))

    def test_same_entry_nonvacuity_and_suspended_metadata(self):
        src = (R / PROBE).read_text()
        same = theorem(src, 'FTsame_entry')
        self.assertEqual(same.split('Proof.', 1)[0].count('ProgSim'), 1)
        self.assertIn('apply FWcomplete_active_simulation', same)
        self.assertIn('FTfinite_call br bs cs ncs ip FR FS', same)
        nonempty = theorem(src, 'FTnonvacuous')
        for term in ['memory_has_fresh_block(NPinitial 1)',
                     'memory_has_fresh_block(QPmemory br 1 1)', 'apply FTsame_entry']:
            self.assertIn(term, nonempty)
        meta = theorem(src, 'FTendpoint_metadata')
        for term in ['get FTreturned OwnershipWaiting=Some RPpending',
                     'get FTreturned OwnershipReady=Some(SKIP,(kenil,kstop))',
                     'Some(V293_cpu_lenv 120%Z bs)', 'Some(false,nil,false::cs)',
                     'Some(false,nil,ncs)']:
            self.assertIn(term, meta)

    def test_controls_and_claim_boundaries(self):
        old = (R / 'audit/probes/V293ActiveCallWitnessProbe.v').read_text()
        self.assertIn('~get(set FWtasks OwnershipReady(SKIP,(kenil,kstop)))OwnershipReady=Some RPpending',
                      theorem(old, 'FWpending_contract_control'))
        doc = (R / 'audit/STAGE267_ACTIVE_CALL_TRACE.md').read_text()
        for term in ['不是一个完整 mutant 程序执行', '不能证明下游机制',
                     '目标 pending 已经存在', '切出任务仍挂起', 'IE=false', 'high=88',
                     '不是 `GOOD_OS`', '不是 `WFInt`', 'K1–K4 未闭合',
                     'uCOS3 未开始', '未提交／推送', 'ADR-0010', '不是所有执行终止']:
            self.assertIn(term, doc)

    def test_stable_compiles_trust_and_preserved_document_tail(self):
        src = (R / PROBE).read_text()
        self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
        for label in read('stable-compiles.json')['repeat_passes']:
            row = read(label + '.json')
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['source_sha256'], row['initial_source_sha256'])
            self.assertEqual(row['source_sha256'], sha(R / PROBE))
        roots = [Path(PROBE).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        trust = read('trust.json')
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertEqual(len(roots), 9)
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']),
                             {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertEqual(list(read('assumptions-by-root.json')), roots)
        self.assertEqual(read('build.json')['exit'], 0)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- active-call-trace-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
