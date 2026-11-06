"""边界解释内 handoff 的局部桥；静态结构检查不代替 Coq 内核核查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage279-handoff-tasksim'
PROD = 'certiucos/v293/proofs/V293HandoffTaskSim.v'
PROBE = 'audit/probes/V293HandoffTaskSimProbe.v'
SOURCES = [PROD, PROBE]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def body(s, name):
    return s.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class HandoffTaskSimTests(unittest.TestCase):
    def test_identity_and_registration(self):
        b = read('baseline.json')['files']
        self.assertEqual(len(b), 1635)
        for p, h in b.items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d']:
                self.assertEqual(sha(R / p), h, p)
        project = (R / '_CoqProject').read_text().splitlines()
        self.assertEqual(project.count(PROD), 1)
        self.assertNotIn(PROBE, project)
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h, p)
        lines = (R / 'csrc/upstream/v2.93.01/checkout/Source/os_core.c').read_text().splitlines()
        for n, anchor in read('source-identity.json')['line_anchors'].items():
            self.assertEqual(lines[int(n) - 1].strip(), anchor)
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])

    def test_public_entry_constructs_store_and_tail(self):
        s = (R / PROD).read_text()
        self.assertNotIn('CertiOS.audit', s)
        self.assertNotRegex(s, r'(?m)^Definition ')
        self.assertEqual(re.findall(r'^Theorem (\w+)\s*:', s, re.M), ['V293_handoff_TaskSim'])
        main = body(s, 'V293_handoff_TaskSim')
        stmt = main.split('Proof.', 1)[0]
        self.assertEqual(stmt.count('TaskSim('), 1)
        for bad in ['store Tint8', 'free Tint32', 'ProgSim', 'V293_global_steps', 'V293_current_guard']:
            self.assertNotIn(bad, stmt)
        for term in ['nh<256', 'top::ci', 'get O abstcblsid', 'indom tasks t',
                     'V293_highest_ready tasks next', '|=Owned old',
                     'RDYINV G t **LINV V293_shared_li t nil',
                     'V293_owned_record_cell_update', 'V293_copy_owned_local;exact Held',
                     'V293_copy_owned_local;exact AfterOwned', 'V293_storage_switch_TaskSim',
                     'V293_copy_switch_resources']:
            self.assertIn(term, main)

    def test_frame_safe_seven_steps_and_resource_partition(self):
        s = (R / PROD).read_text()
        steps = body(s, 'V293_copy_csteps_TaskSim')
        for rule in ['sseq_step', 'sassign_step', 'evar_step', 'sassignrv_step',
                     'eaddr_step', 'sassignend_step', 'sskip_step']:
            self.assertIn(rule, steps)
        for term in ['forall Mf Mall,join Mi Mf Mall', 'cstep_idmove_deter',
                     'V293_invariant_cstep_TaskSim', 'lmachLib.store_mono',
                     'join_store_join', 'V293_store_cstep_unique', 'evalval_mono',
                     'evaltype_irrev_mem', 'exact Before', 'exact After']:
            self.assertIn(term, steps)
        res = body(s, 'V293_copy_switch_resources')
        stmt = res.split('Proof.', 1)[0]
        self.assertIn(r'(SWINVt G t //\\ SWPRE_NDEAD', stmt)
        for term in ['apply sat_split in Held', 'apply map_join_emp\' in JO',
                     'V293_owned_record_cell_load', 'V293_exit_cell_to_storage',
                     'V293_ready_storage_switch_resources', 'V293_storage_switch_pre']:
            self.assertIn(term, res)

    def test_actual_same_call_and_bounded_claims(self):
        s = (R / PROBE).read_text()
        packet = s.split('Definition HCpacket', 1)[1].split('Lemma HCpartition', 1)[0]
        for term in ['join Mt Mf M', 'join Ot Of(RIabstract OwnershipWaiting)',
                     '|=HCowned br bs', '|=IWframe', 'V293_interrupt_handoff 103%Z 108%Z 106%Z']:
            self.assertIn(term, packet)
        actual = body(s, 'HCactual_handoff')
        for term in ['FTfixed_prefix', 'V293_local_steps_global', 'FTenter',
                     'HCpartition', 'V293_byteval 6']:
            self.assertIn(term, actual)
        nonvac = body(s, 'HCnonvacuous')
        self.assertEqual(nonvac.count('memory_has_fresh_block'), 2)
        self.assertIn('snd V293SwitchProgSimProbe.SPph', nonvac)
        self.assertIn('V293_handoff_TaskSim', body(s, 'HCpartition'))
        self.assertIn('OPactual_entry', body(s, 'HCactual_switch_gap'))
        self.assertIn('HCsaved_necessary', body(s, 'HCreject_missing_saved'))
        doc = (R / 'audit/STAGE279_HANDOFF_TASKSIM.md').read_text()
        for term in ['不是完整调用入口 TaskSim', '不是全局切回可达性', 'saved(bs) 私有',
                     'saved98 与 RCframe 外部', 'cache=4', '不是完整单因素执行消融',
                     'protocol_fully_completed=false', 'ADR-0010', 'GOOD_OS 未闭合',
                     'uCOS3 未开始', '没有证明列表置换下 Inv 的等价', '不是原始外部声明']:
            self.assertIn(term, doc)

    def test_repeat_compiles_and_recursive_kernel(self):
        roots = []
        for p in SOURCES:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', s, re.M)]
        self.assertEqual(len(roots), 10)
        self.assertEqual(list(read('stable-compiles.json')), SOURCES)
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
        self.assertEqual(t['roots_printed'], 10)
        self.assertEqual(list(read('assumptions-by-root.json')), roots)
        self.assertTrue(all(row['exit'] == 0 for row in t['commands']))
        self.assertLessEqual(set(t['assumptions']), {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
