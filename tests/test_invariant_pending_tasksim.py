"""泛型 pending 桥的结构回归；语义由 Coq 内核独立核查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage277-invariant-pending'
GEN = 'certiucos/v293/proofs/V293InvariantPendingTaskSim.v'
STORAGE = 'certiucos/v293/proofs/V293StoragePendingTaskSim.v'
PROBE = 'audit/probes/V293InvariantPendingTaskSimProbe.v'
SOURCES = [GEN, STORAGE, PROBE]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def body(s, n):
    return s.split(n + ' :', 1)[1].split('Qed.', 1)[0]


class InvariantPendingTaskSimTests(unittest.TestCase):
    def test_frozen_inputs_and_registration(self):
        b = read('baseline.json')['files']
        self.assertEqual(len(b), 1626)
        for p, h in b.items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d']:
                self.assertEqual(sha(R / p), h, p)
        lines = (R / '_CoqProject').read_text().splitlines()
        for p in [GEN, STORAGE]:
            self.assertEqual(lines.count(p), 1)
        self.assertNotIn(PROBE, lines)
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h, p)
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])

    def test_generic_steps_and_one_shared_suffix(self):
        s = (R / GEN).read_text()
        self.assertNotIn('CertiOS.audit', s)
        self.assertNotRegex(s, r'(?m)^Definition ')
        self.assertEqual(re.findall(r'^Theorem (\w+)\s*:', s, re.M), ['V293_invariant_pending_TaskSim'])
        main = body(s, 'V293_invariant_pending_TaskSim')
        stmt = main.split('Proof.', 1)[0]
        self.assertEqual(stmt.count('TaskSim('), 1)
        for bad in ['ProgSim', 'V293_global_steps', 'V293_ready_current_core', 'free Tint32']:
            self.assertNotIn(bad, stmt)
        for term in ['getinv(I(S INUM))=Aemp', 'GoodInvAsrt Core', '|=SWINV I', '|=INV I',
                     'Amapsto(b,0%Z)Tint32 true v **(Core **CurTid t)', 'RDYINV I t **LINV',
                     'destruct top', 'V293_invariant_nil_close']:
            self.assertIn(term, main)
        self.assertEqual(main.count('V293_invariant_return_suffix with'), 2)
        suffix = body(s, 'V293_invariant_return_suffix')
        for term in ['V293_tick_free_owned', 'free_mono', 'join_free', 'V293_cpu_layout',
                     'V293_return_client_coinduction', 'V293_invariant_cstep_TaskSim']:
            self.assertIn(term, suffix)
        ordinary = body(s, 'V293_invariant_cstep_TaskSim')
        self.assertNotIn('V293_invariant_nil_empty', ordinary)
        self.assertIn('V293_enabled_join_frames', ordinary)
        self.assertIn('eapply inv_ncare_le;exact Inv', ordinary)
        self.assertIn('join M Mf Mall', ordinary)
        self.assertIn('forall Cf mf,cstep', ordinary)

    def test_existing_storage_and_strong_compatibility(self):
        s = (R / STORAGE).read_text()
        self.assertNotIn('CertiOS.audit', s)
        self.assertNotIn('V293_ready_current_core', s)
        self.assertNotRegex(s, r'(?m)^Definition ')
        self.assertEqual(re.findall(r'^Theorem (\w+)\s*:', s, re.M), ['V293_storage_pending_TaskSim'])
        main = body(s, 'V293_storage_pending_TaskSim')
        self.assertEqual(main.split('Proof.', 1)[0].count('TaskSim('), 1)
        self.assertIn('V293_invariant_pending_TaskSim', main)
        for name in ['V293_storage_return_enabled_INV', 'V293_storage_return_disabled_SWINV']:
            self.assertIn('V293_ready_storage_noisr_core', body(s, name))
        compat = body((R / PROBE).read_text(), 'IWcurrent_compatible')
        for term in ['V293_invariant_pending_TaskSim', 'V293_return_disabled_SWINV', 'V293_return_enabled_INV']:
            self.assertIn(term, compat)

    def test_old_private_saved_frame_and_bounded_witness(self):
        s = (R / PROBE).read_text()
        packet = s.split('Definition IWpacket', 1)[1].split('Lemma IWopen', 1)[0]
        for term in ['join Mt Mf M', 'join Ot Of(RIabstract OwnershipWaiting)',
                     '|=IWowned br bs', '|=IWframe', 'RPpending', 'OwnershipWaiting']:
            self.assertIn(term, packet)
        self.assertIn('98%positive', s.split('Definition IWframe', 1)[1].split('Definition IWpacket', 1)[0])
        actual = body(s, 'IWactual_old_cut')
        for term in ['OPactual_entry', 'forall top ci,IWpacket', 'V293_current_guard 94%positive', 'V293_byteval 4']:
            self.assertIn(term, actual)
        self.assertEqual(body(s, 'IWnonvacuous').count('memory_has_fresh_block'), 2)
        self.assertIn('IWowned_saved_necessary', body(s, 'IWreject_missing_saved'))
        doc = (R / 'audit/STAGE277_INVARIANT_PENDING_TASKSIM.md').read_text()
        for term in ['不是完整入口 TaskSim', '不是整核证明', 'saved(bs) 私有', 'cache=4',
                     '不是原完整入口 true 可达性', '不是完整单因素执行消融', 'protocol_fully_completed=false',
                     'ADR-0010', 'uCOS3 未开始']:
            self.assertIn(term, doc)

    def test_repeat_compiles_and_recursive_kernel(self):
        roots = []
        for p in SOURCES:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', s, re.M)]
        self.assertEqual(len(roots), 16)
        for p, labels in read('stable-compiles.json').items():
            self.assertEqual(len(labels), 2)
            for n in labels:
                row = read(n + '.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
                self.assertEqual(row['source_sha256'], sha(R / p))
        t = read('trust.json')
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 16)
        self.assertEqual(list(read('assumptions-by-root.json')), roots)
        self.assertTrue(all(row['exit'] == 0 for row in t['commands']))
        self.assertLessEqual(set(t['assumptions']), {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
