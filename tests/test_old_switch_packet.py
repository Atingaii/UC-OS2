"""真实旧任务切出资源的结构/证据回归；语义检查由 Coq 内核承担。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage276-old-switch-packet'
PROD = 'certiucos/v293/proofs/V293StorageSwitchPre.v'
PROBE = 'audit/probes/V293OldSwitchPacketProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def body(s, n):
    return s.split(n + ' :', 1)[1].split('Qed.', 1)[0]


class OldSwitchPacketTests(unittest.TestCase):
    def test_old_inputs_registration_and_source_identity(self):
        baseline = read('baseline.json')['files']
        self.assertEqual(len(baseline), 1622)
        for p, h in baseline.items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d']:
                self.assertEqual(sha(R / p), h, p)
        lines = (R / '_CoqProject').read_text().splitlines()
        self.assertEqual(lines.count(PROD), 1)
        self.assertNotIn(PROBE, lines)
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h, p)
        self.assertTrue(read('source-identity-check.json')['passed'])

    def test_general_same_shared_heap_contract(self):
        s = (R / PROD).read_text()
        self.assertNotIn('CertiOS.audit', s)
        self.assertNotRegex(s, r'(?m)^Definition ')
        self.assertEqual(re.findall(r'^Theorem (\w+)\s*:', s, re.M), ['V293_storage_switch_pre'])
        main = body(s, 'V293_storage_switch_pre')
        stmt = main.split('Proof.', 1)[0]
        for term in ['TaskSim', 'ProgSim', 'V293_global_steps', 'free Tint32', 'V293_ready_current_inv']:
            self.assertNotIn(term, stmt)
        for term in ['get O abstcblsid', 'indom tasks current', 'V293_highest_ready tasks next',
                     'load(Tptr tp)M(bt,0%Z)', r'current //\\', 'SWPRE_NDEAD V293_scheduler target current',
                     'V293_ready_switch_full', 'V293_tasks_highest_spatial']:
            self.assertIn(term, main)
        readframe = body(s, 'V293_dispatch_read_frame')
        for term in ['join M Mf Mall', 'load(Tptr tp)Mall', 'V293_dispatch_cell target tp **R',
                     'mapstoval_load', 'lmachLib.load_mono', 'v=Vptr next']:
            self.assertIn(term, readframe)

    def test_actual_old_entry_and_private_saved(self):
        s = (R / PROBE).read_text()
        packet = s.split('Definition OPpre', 1)[1].split('Lemma OPpartition', 1)[0]
        for term in ['Amapsto(bs,0%Z)', 'SWPRE_NDEAD V293_scheduler 106%Z OwnershipWaiting',
                     '98%positive', 'RCframe']:
            self.assertIn(term, packet)
        self.assertNotIn('TaskSim', packet)
        partition = body(s, 'OPpartition')
        for term in ['STrepack br bs cs OwnershipWaiting', 'V293_dispatch_read_frame',
                     'V293_storage_switch_pre', 'Mc Mf M', 'JM Target Open', 'exact Both', 'exact Frame']:
            self.assertIn(term, partition)
        actual = body(s, 'OPactual_entry')
        for term in ['FTto_switch', 'OPpartition', 'FWos br cs ncs,OwnershipWaiting',
                     'FTenvs bs', 'V293_byteval 4', 'apply SPcopied_cache_gap']:
            self.assertIn(term, actual)
        self.assertNotIn('TaskSim', actual)
        self.assertEqual(body(s, 'OPnonvacuous').count('memory_has_fresh_block'), 2)

    def test_necessary_conditions_and_bounded_claims(self):
        s = (R / PROBE).read_text()
        n = body(s, 'OPnecessary')
        for term in ['exists next,load(Tptr tp)M', 'V293_highest_ready tasks next /\\indom tasks current',
                     'OSAbstMod.join_get_l', 'load_mem_mono', 'exact(proj1 Pure)']:
            self.assertIn(term, n)
        for name in ['OPreject_wrong_selection', 'OPreject_dead_current']:
            self.assertIn('OPnecessary', body(s, name))
        self.assertIn('SCwaiting_not_highest', body(s, 'OPreject_waiting_target'))
        doc = (R / 'audit/STAGE276_OLD_SWITCH_PACKET.md').read_text()
        for term in ['逻辑必要性/拒绝控制', '没有全部完成', 'saved(bs) 私有', '同一个共享子堆',
                     '不是完整入口 TaskSim', '强 current', 'ADR-0010', 'uCOS3 未开始', '这不是整核证明']:
            self.assertIn(term, doc)

    def test_stable_compiles_and_recursive_kernel_check(self):
        roots = []
        for p in [PROD, PROBE]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', s, re.M)]
        self.assertEqual(len(roots), 9)
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
        self.assertEqual(t['roots_printed'], 9)
        self.assertEqual(list(read('assumptions-by-root.json')), roots)
        self.assertTrue(all(row['exit'] == 0 for row in t['commands']))
        self.assertLessEqual(set(t['assumptions']), {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
