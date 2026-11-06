"""本步接口与冻结证据回归；证明有效性由 Coq/coqchk 独立检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage263-resumed-return-progsim'
PROD = 'certiucos/v293/proofs/V293ResumedReturnProgSim.v'
PROBE = 'audit/probes/V293ResumedReturnProgSimProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class ResumedReturnProgSimTests(unittest.TestCase):
    def test_production_only_final_caller_simulation(self):
        src = (R / PROD).read_text()
        for name in ['V293_pending_exit_progsim', 'V293_switch_pending_exit_progsim',
                     'V293_exit_call_resume_progsim']:
            self.assertEqual(theorem(src, name).split('Proof.', 1)[0].count('ProgSim'), 2)
        body = theorem(src, 'V293_pending_exit_progsim')
        for term in ['po f=Some(tau,d1,d2,body)', 'false::cs', 'free Tint32 b M=Some Mf',
                     'V293_excrit_progsim', 'V293_one_local_return_progsim', 'V293_cpu_layout']:
            self.assertIn(term, body)
        body = theorem(src, 'V293_exit_call_resume_progsim')
        for term in ['V293_exit_boundary_dispatch', 'V293_exit_call_dispatch_progsim',
                     'V293_pending_exit_progsim', 'free Tint32 bs Mf=Some Mret',
                     'get Of curtid=Some(oscurt next)']:
            self.assertIn(term, body)

    def test_pending_is_existing_and_outgoing_is_preserved(self):
        src = (R / PROD).read_text()
        body = theorem(src, 'V293_switch_pending_exit_progsim')
        for term in ['current<>next', 'get T next=Some(SKIP', 'get les next=Some',
                     'get aus next=Some', 'V293_switch_progsim',
                     'rewrite map_get_set\' by congruence;exact Pending']:
            self.assertIn(term, body)
        probe = theorem((R / PROBE).read_text(), 'RPactual_switch_and_resume_simulation')
        for term in ['get RPfinal OwnershipWaiting=Some(SKIP,(kenil,HPpending))',
                     'get(set RPenvs OwnershipReady emp)OwnershipWaiting=Some emp',
                     'OwnershipWaiting=Some(false,nil,cs)']:
            self.assertIn(term, probe)
        self.assertEqual(probe.split('Proof.', 1)[0].count('ProgSim'), 1)
        self.assertIn('SPterminal', probe)
        self.assertIn('HPschedule', probe)

    def test_independent_same_heap_execution_simulation_and_free(self):
        src = (R / PROBE).read_text()
        storage = theorem(src, 'RPstorage')
        self.assertNotIn('ProgSim', storage.split('Proof.', 1)[0])
        for term in ['CPtyped_updated 1', 'V293_owned_record_cell_update',
                     'V293_ready_current_write', 'V293_cpu_release',
                     'free Tint32 98%positive Msw=Some Mret']:
            self.assertIn(term, storage)
        trace = theorem(src, 'RPfinite_switch_and_return')
        for term in ['good_inv_prop', 'V293_int_exit_pending_return', 'rt1n_trans',
                     'V293_switch_progress']:
            self.assertIn(term, trace)
        actual = theorem(src, 'RPactual_switch_and_resume_simulation')
        for term in ['exists M Msw Mret', 'RPfinite_switch_and_return',
                     'V293_global_steps', 'RPstate M cs ncs', 'RPreturned Mret cs ncs',
                     'forall i,(0<=i<4)%Z ->get Mret(98%positive,i)=None',
                     'get Mret(b,i)=get Msw(b,i)']:
            self.assertIn(term, actual)

    def test_single_factor_actual_stack_and_high_current_controls(self):
        src = (R / PROBE).read_text()
        empty = theorem(src, 'RPempty_stack_aborts')
        for term in ['lpstepabt', 'RPcritical_state M cs nil', 'progabort',
                     'taskabort', 'CPempty_stack_no_step']:
            self.assertIn(term, empty)
        full = theorem(src, 'RPnonempty_stack_steps')
        for term in ['lpstep(', 'RPcritical_state M cs(false::ncs)',
                     'V293_critical_progress', 'excrit_step']:
            self.assertIn(term, full)
        high = theorem(src, 'RPzero_high_match_rejected')
        for term in ['~ProgSim', 'RIabstract OwnershipWaiting', 'HPThf',
                     'OwnershipReady=OwnershipWaiting', 'congruence;discriminate']:
            self.assertIn(term, high)

    def test_stable_compiles_trust_identity_and_bounded_documentation(self):
        self.assertEqual(sha(D / 'protocol.json'), (D / 'protocol.sha256').read_text().strip())
        stable = read('stable-compiles.json')
        roots = []
        for key, p in [('production', PROD), ('probe', PROBE)]:
            src = (R / p).read_text()
            self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
            row = read(stable[key] + '.json')
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], sha(R / p))
            self.assertEqual(row['source_sha256'], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        self.assertNotIn('CertiOS.audit.', (R / PROD).read_text())
        for label in stable['repeat_passes']:
            self.assertEqual(read(label + '.json')['exit'], 0)
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertEqual(len(roots), 10)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']),
                             {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertEqual(read('build.json')['exit'], 0)
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(PROD), 1)
        doc = (R / 'audit/STAGE263_RESUMED_RETURN_PROGSIM.md').read_text()
        for term in ['不是 `GOOD_OS`', '不是 `WFInt`', 'IE=false', 'ADR-0010',
                     'K1–K4 未闭合', 'uCOS3 未开始', '未提交／推送', 'high=88',
                     '最终 caller 端点模拟', 'pending 在任务映射中已存在',
                     '独立实例从物理 switch 开始', '不是完整 OSIntExit 调用实例',
                     '切出任务仍挂起']:
            self.assertIn(term, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- resumed-return-progsim-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h)
