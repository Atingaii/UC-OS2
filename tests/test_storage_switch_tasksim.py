"""原 switch 的弱 storage 桥；结构检查不替代 Coq 语义核查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage278-storage-switch-tasksim'
PROD = 'certiucos/v293/proofs/V293StorageSwitchTaskSim.v'
PROBE = 'audit/probes/V293StorageSwitchTaskSimProbe.v'
SOURCES = [PROD, PROBE]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def body(s, name):
    return s.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class StorageSwitchTaskSimTests(unittest.TestCase):
    def test_frozen_inputs_and_registration(self):
        b = read('baseline.json')['files']
        self.assertEqual(len(b), 1631)
        for p, h in b.items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d']:
                self.assertEqual(sha(R / p), h, p)
        lines = (R / '_CoqProject').read_text().splitlines()
        self.assertEqual(lines.count(PROD), 1)
        self.assertNotIn(PROBE, lines)
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h, p)
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])

    def test_resource_only_public_switch_and_real_obligations(self):
        s = (R / PROD).read_text()
        self.assertNotIn('CertiOS.audit', s)
        self.assertNotRegex(s, r'(?m)^Definition ')
        self.assertNotIn('V293_ready_current_core', s)
        self.assertEqual(re.findall(r'^Theorem (\w+)\s*:', s, re.M), ['V293_storage_switch_TaskSim'])
        main = body(s, 'V293_storage_switch_TaskSim')
        stmt = main.split('Proof.', 1)[0]
        self.assertEqual(stmt.count('TaskSim('), 1)
        for bad in ['ProgSim', 'V293_global_steps', 'free Tint32', 'V293_current_guard']:
            self.assertNotIn(bad, stmt)
        for term in [r'Amapsto(b,0%Z)Tint32 true v **(SWINVt G t //\\ SWPRE_NDEAD',
                     'getsched(pc,A)=V293_scheduler', 'RDYINV G t **LINV',
                     'apply sat_split in Held', 'apply task_sim',
                     'V293_invariant_nil_empty G eq_refl', 'exact Partition', 'exact AbsPartition',
                     "intros Mc' Oc' o' O' Restore JoinMem JoinAbs", 'V293_storage_resume_callback',
                     'V293_switch_local_empty', 'exact PreAll']:
            self.assertIn(term, main)
        self.assertEqual(main.count('\n - intros '), 7)

    def test_fixed_private_saved_and_universal_restoration(self):
        s = (R / PROD).read_text()
        resume = body(s, 'V293_storage_resume_callback')
        stmt = resume.split('Proof.', 1)[0]
        self.assertEqual(stmt.count('TaskSim('), 1)
        for term in ['forall Mc Oc o\' O\'', 'join Ol Oc O\'',
                     'satp(ge,V293_cpu_lenv saved b,Mc,ir', 'joinmem(ge,V293_cpu_lenv saved b,Ml,ir',
                     'Amapsto(b,0%Z)Tint32 true v', 'SWINVt G t', 'RDYINV G t **LINV']:
            self.assertIn(term, stmt)
        self.assertNotIn('Mc=', stmt)
        self.assertNotIn('destruct top', resume)
        self.assertEqual(resume.count('eapply V293_storage_pending_TaskSim'), 1)
        self.assertIn('apply V293_resume_high_done', resume)
        self.assertNotIn('sfree_step', s)
        opened = body(s, 'V293_storage_resume_open')
        self.assertIn('V293_shared_clear_state', opened)
        self.assertIn('V293_ready_storage_switch_open', opened)

    def test_actual_old_cut_nonvacuity_frames_and_boundaries(self):
        s = (R / PROBE).read_text()
        packet = s.split('Definition WSpacket', 1)[1].split('Lemma WSpartition', 1)[0]
        for term in ['join Mt Mf M', 'join Ot Of(RIabstract OwnershipWaiting)',
                     '|=WSowned br bs', '|=IWframe', '(curs(sprim(switch 106%Z)),(kenil,FTpending))']:
            self.assertIn(term, packet)
        actual = body(s, 'WSactual_old_switch')
        for term in ['OPactual_entry', 'WSpartition', 'V293_current_guard 94%positive', 'V293_byteval 4']:
            self.assertIn(term, actual)
        nonvac = body(s, 'WSnonvacuous')
        self.assertEqual(nonvac.count('memory_has_fresh_block'), 2)
        self.assertIn('snd V293SwitchProgSimProbe.SPph', nonvac)
        resume = body(s, 'WSresume')
        self.assertEqual(resume.split('Proof.', 1)[0].count('TaskSim('), 1)
        self.assertIn("forall ip A Mc' Oc' o' O'", resume)
        self.assertIn('V293_storage_resume_callback', resume)
        concrete = body(s, 'WSresume_concrete')
        self.assertIn('eapply Resume;[exact Shared| |exact JOt]', concrete)
        self.assertIn('exact JMt', concrete)
        self.assertIn('WSsaved_necessary', body(s, 'WSreject_missing_saved'))
        doc = (R / 'audit/STAGE278_STORAGE_SWITCH_TASKSIM.md').read_text()
        for term in ['不是完整调用入口 TaskSim', '不是全局切回可达性', 'saved(bs) 私有',
                     'saved98 与 RCframe 外部', 'cache=4', '不是完整单因素执行消融',
                     'protocol_fully_completed=false', 'ADR-0010', 'GOOD_OS 未闭合', 'uCOS3 未开始']:
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
