"""活跃完整调用实例的接口/来源回归；证明有效性由 Coq/coqchk 独立检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage266-active-call-witness'
PROBE = 'audit/probes/V293ActiveCallWitnessProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class ActiveCallWitnessTests(unittest.TestCase):
    def test_old_proofs_program_and_source_identity_unchanged(self):
        for p, h in read('baseline.json')['files'].items():
            if p.endswith('.v') or p in ['_CoqProject', '.Makefile.coq.d']:
                self.assertEqual(sha(R / p), h, p)
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h, p)
        self.assertNotIn(PROBE, (R / '_CoqProject').read_text())
        self.assertNotIn('CertiOS.audit.', (R / 'certiucos/v293/proofs/V293ExitActiveCallProgSim.v').read_text())

    def test_original_full_call_simulation_without_simulation_premise(self):
        src = (R / PROBE).read_text()
        body = theorem(src, 'FWcomplete_active_simulation')
        self.assertEqual(body.split('Proof.', 1)[0].count('ProgSim'), 1)
        for term in ['fresh(NPinitial 1)br', 'FWtasks(FWos br cs ncs)',
                     'V293_exit_active_call_progsim', '(entry:=sfexec 114%Z nil nil)',
                     'intros bs SavedFresh', 'FWactive_resources runningblock bs Fresh SavedFresh',
                     'apply HPschedule', 'eapply SPterminal']:
            self.assertIn(term, body)
        for term in ['memory_has_fresh_block(NPinitial 1)', 'apply FWinitial_owned',
                     'apply FWcomplete_active_simulation']:
            self.assertIn(term, theorem(src, 'FWnonvacuous'))
        self.assertIn('sfexec 114%Z nil nil', src.split('Definition FWtasks:', 1)[1].split('Definition FWos', 1)[0])

    def test_all_fresh_same_heap_spatial_storage_chain(self):
        src = (R / PROBE).read_text()
        body = theorem(src, 'FWactive_resources')
        statement = body.split('Proof.', 1)[0]
        self.assertNotIn('ProgSim', statement)
        self.assertIn('fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->', statement)
        for term in ['store Tint32(allocb(QPmemory br 1 1)bs 0%Z 4)',
                     'Some(Vint32 Int.one)', 'V293_sched_read_memory',
                     'V293_OSSched_different', 'Int.add Int.mone Int.one',
                     'store Tint8 M1(94%positive,0%Z)(V293_byteval 4)=Some Mc',
                     'store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Msw',
                     'free Tint32 98%positive Msw=Some Mret',
                     'FWinitial_owned', 'V293_cpu_initialized_frame',
                     'V293_owned_byte_update', 'FWentry_observations', 'FWdispatch_resources']:
            self.assertIn(term, body)
        dispatch = theorem(src, 'FWdispatch_resources')
        for term in ['V293_ready_dispatch_call', 'HalfPermMap.extensionality',
                     'V293_owned_record_cell_update', 'V293_handoff_copy_execution',
                     'V293_ready_current_write', 'V293_cpu_release']:
            self.assertIn(term, dispatch)
        self.assertNotIn('ProgSim', dispatch)
        self.assertIn('V293_owned_cells_context', theorem(src, 'FWbase'))

    def test_pending_omission_is_only_contract_control(self):
        src = (R / PROBE).read_text()
        body = theorem(src, 'FWpending_contract_control')
        for term in ['get FWtasks OwnershipReady=Some RPpending',
                     '~get(set FWtasks OwnershipReady(SKIP,(kenil,kstop)))OwnershipReady=Some RPpending']:
            self.assertIn(term, body)
        self.assertNotIn('ProgSim', body)
        doc = (R / 'audit/STAGE266_ACTIVE_CALL_WITNESS.md').read_text()
        for term in ['不是一个完整 mutant 程序执行', '不能证明下游机制',
                     'pending 已经存在', '切出任务仍挂起', 'IE=false', 'high=88',
                     '不是 `GOOD_OS`', '不是 `WFInt`', 'K1–K4 未闭合',
                     'uCOS3 未开始', '未提交／推送', 'ADR-0010']:
            self.assertIn(term, doc)

    def test_stable_compiles_recursive_trust_and_document_tail(self):
        src = (R / PROBE).read_text()
        self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
        self.assertEqual(sha(D / 'protocol.json'), (D / 'protocol.sha256').read_text().strip())
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
        self.assertEqual(len(roots), 11)
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']),
                             {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertEqual(list(read('assumptions-by-root.json')), roots)
        self.assertEqual(read('build.json')['exit'], 0)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- active-call-witness-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
