"""条件式源码返回与原创建规则的资源连接，不替代整个创建API模拟。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage347-init-ready-commit'
SOURCES = ['certiucos/v293/proofs/V293InitReadyCommit.v',
           'audit/probes/V293InitReadyCommitProbe.v']
ALLOWED = {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class InitReadyCommitTests(unittest.TestCase):
    def test_prospective_single_factor_and_boundaries(self):
        p = read('protocol.json')
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json')])
        self.assertTrue(p['prospective'])
        self.assertEqual(set(p['allowed']), ALLOWED)
        self.assertEqual(p['control']['factor'], 'abstract task insertion versus keeping old O')
        self.assertIn('same physical return heap', p['control']['fixed'])
        self.assertFalse(p['regression']['gate_waived'])
        self.assertEqual(p['regression']['tests'], 3029)
        self.assertIn('resource/creation bridge, not whole OSTaskCreate caller simulation', p['limits'])

    def test_source_wrapper_has_no_execution_or_resource_oracle(self):
        s = (R / SOURCES[0]).read_text()
        pre, post = s.split('Theorem V293_OS_TCBInit_shared_return_under_hooks :', 1)[1].split(' exists Mf clientM\',', 1)
        self.assertEqual(pre.count('V293_records_hook_return'), 2)
        for forbidden in ['V293_local_steps', 'V293_ready_payload', 'V293_shared_ready_records', 'cstepstar', 'hpstep']:
            self.assertNotIn(forbidden, pre)
        for needed in ['V293_OS_TCBInit_ready_return_under_hooks', 'V293_init_ready_create_commit',
                       'V293_ready_core br bg table', '(ge,caller,Mf,ir,aux,',
                       'V293_init_ready_stale_commit_rejected']:
            self.assertIn(needed, post)
        self.assertNotIn('Definition V293_ready_core', s)
        self.assertNotIn('CertiOS.audit.', s)
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(SOURCES[0]), 1)

    def test_real_client_allocation_and_original_creation_rule(self):
        s = (R / SOURCES[0]).read_text()
        allocation = s.split('Lemma V293_init_client_allocate :', 1)[1].split('Theorem V293_init_ready_create_commit :', 1)[0]
        pre, proof = allocation.split('Proof.', 1)
        self.assertNotIn(' ->\n cstepstar', pre)
        for token in ['store(Tptr Tvoid)', 'load(Tptr Tvoid)', 'sfexec', 'c_stepstarn',
                      'sfexec_step', 'sallocp_step', 'sallocend_step']:
            self.assertIn(token, allocation)
        self.assertIn('eapply hpcrt_step', s)
        self.assertIn('~eqdomO', s)
        self.assertNotIn('eapply spec_prim_step', s)
        for token in ['get T new=None', 'get cenvs new=None', 'new<>current']:
            self.assertIn(token, s)

    def test_same_physical_heap_and_current_pointer_permissions(self):
        s = (R / SOURCES[0]).read_text()
        pre, proof = s.split('Lemma V293_init_ready_shared_pack :', 1)[1].split('Proof.', 1)
        pre = pre.split('Qed.', 1)[0]
        self.assertIn('(ge,le,M,ir,aux,O,op)', pre)
        self.assertIn('(ge,le,M,ir,aux,O\',op)', pre)
        self.assertIn('GV_separate_rw', s)
        self.assertIn('V293_init_ready_physical_empty', proof)
        stale = s.split('Theorem V293_init_ready_stale_commit_rejected :', 1)[1].split('Qed.', 1)[0]
        self.assertIn('forall br bg bp tasks current new priority events now s,', stale)
        self.assertIn('get tasks new=None', stale)
        self.assertIn('get(getabst s)abstcblsid', stale)
        self.assertNotIn('V293_bitmap_tasks', stale)

    def test_fifteen_roots_repeat_compile_and_trust(self):
        roots = [Path(p).stem + '.' + n for p in SOURCES for n in
                 re.findall(r"^(?:Lemma|Theorem|Corollary) ([\w']+)\s*:", (R / p).read_text(), re.M)]
        t = read('trust.json')
        self.assertEqual(len(roots), 15)
        self.assertEqual(t['roots'], roots)
        self.assertEqual(t['roots_printed'], 15)
        self.assertTrue(t['passed'] and t['recursive'])
        self.assertEqual(set(t['allowed']), ALLOWED)
        byroot = read('assumptions-by-root.json')
        self.assertEqual(set(byroot), set(roots))
        self.assertTrue(all(set(v) <= ALLOWED for v in byroot.values()))
        for label, source in zip(['return', 'probe'], SOURCES):
            for i in [1, 2]:
                row = read(f'stable-{label}-{i}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / source))
                self.assertEqual(row['source_sha256'], sha(R / source))
            self.assertEqual(read('stable-inputs.json')[source], sha(R / source))
            self.assertEqual(read('trust-inputs.json')[source], sha(R / source))
            self.assertNotRegex((R / source).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')

    def test_closed_creation_probe_not_claimed_physical_reachability(self):
        q = (R / SOURCES[1]).read_text()
        for name in ['IRCallocation', 'IRCcreation', 'IRCstale', 'IRCnotPrimitive']:
            self.assertIn('Theorem ' + name + ' :', q)
        self.assertNotIn('V293_ready_payload', q)
        self.assertIn('eapply hpcrt_step', q)
        self.assertIn('Definition IRCold', q)
        self.assertIn('Definition IRCnewO := set IRCold abstcblsid(abstcblist IRCupdated)', q)
        doc = (R / 'audit/STAGE347_INIT_READY_COMMIT.md').read_text()
        for bound in ['固定更新任务表见证', '没有构造满足两个hook契约的完整启动实例',
                      '不是', 'TaskSim', '当前任务属于任务表']:
            self.assertIn(bound, doc)

    def test_old_sources_tests_and_frozen_evidence_preserved(self):
        excluded = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject'}
        for name, expected in read('baseline.json').items():
            if name not in excluded:
                self.assertEqual(sha(R / name), expected, name)
        old = R / 'audit/logs/stage346-init-ready-payload/checkpoint-evidence-manifest.json'
        self.assertEqual(sha(old), (D / 'previous-manifest.sha256').read_text().split()[0])
        for name, row in json.loads(old.read_text()).items():
            if name not in excluded:
                self.assertEqual(sha(R / name), row['sha256'], name)
        self.assertTrue((R / '_CoqProject').read_bytes().startswith((D / '_CoqProject.baseline').read_bytes()))
