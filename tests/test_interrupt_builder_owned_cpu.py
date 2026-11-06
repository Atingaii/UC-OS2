"""Coq 检查语义；此处保护真实轨迹连接、权限对照和证据身份。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage314-builder-owned-cpu'
P = 'certiucos/v293/proofs/V293InterruptBuilderOwnedCPU.v'
Q = 'audit/probes/V293InterruptBuilderOwnedCPUProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


class InterruptBuilderOwnedCPUTests(unittest.TestCase):
    def test_owned_prefix_keeps_actual_allocation_without_free_premise(self):
        s = (R / P).read_text()
        pre, body = s.split('Theorem V293_builder_dispatch_owned_cpu_prefix :', 1)[1].split('Proof.', 1)
        for text in ['Some pre=BuildintPre', 'st|=pre', 'P entry=Some(',
                     'P exit=Some(', 'P sched_id=Some(',
                     'Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Atrue']:
            self.assertIn(text, pre)
        self.assertNotIn('free ', pre)
        for text in ['V293_builder_enter_prefix', 'V293_exit_boundary_entry_local',
                     'V293_handoff_copy_execution', 'exact ExitTrace', 'exact CopyTrace']:
            self.assertIn(text, body)
        self.assertNotIn('Require Import CertiOS.audit.', s)

    def test_pending_exit_derives_free_but_keeps_actual_resume_and_caller_obligations(self):
        s = (R / P).read_text().split('Theorem V293_pending_exit_owned_progsim :', 1)[1]
        pre, body = s.split('Proof.', 1)
        for text in ['get T t=Some(SKIP,', 'get les t=Some(V293_cpu_lenv saved b)',
                     'get aus t=Some((false,si,false::cs):localst)',
                     'Amapsto(b,0%Z)Tint32 true(Vint32 Int.zero) **R',
                     'get O curtid=Some(oscurt t)', '(forall Mf,free Tint32 b M=Some Mf ->',
                     'ProgSim(pc,(po,pi,ip))(set T t(SKIP,(kenil,tail)))']:
            self.assertIn(text, pre)
        self.assertIn('V293_tick_free_owned', body)
        self.assertIn('V293_pending_exit_progsim', body)
        self.assertEqual(pre.count('free Tint32 b M=Some Mf ->'), 1)
        self.assertIn('apply Post;assumption.', body)

    def test_same_original_pint_builder_prefix_and_switch_keep_cpu_frame(self):
        s = (R / Q).read_text()
        for text in ['V293_builder_dispatch_owned_cpu_prefix',
                     'V293_interrupt_local_steps_global', 'V293_interrupt_source_enter',
                     'V293_control_switch_forward', '93%positive 1%positive V293_tcb_type CSO(spec_done None)(OCrest bs)',
                     'exact Entry', 'exact Prefix', 'exact Low',
                     'V293_current_core_highest_frame', 'V293_scalar_current_TaskSim']:
            self.assertIn(text, s)
        prep = s.split('Theorem OCprepare :', 1)[1].split('Qed.', 1)[0]
        self.assertNotIn('BGprepare cst', prep)
        self.assertIn('exists M frame bs Ms Mf', s)

    def test_external_ownership_is_not_hidden_in_selected_local_invariant(self):
        s = (R / Q).read_text()
        packet = s.split('Definition OCpacket', 1)[1].split('Theorem OCprepare', 1)[0]
        for text in ['join Mt Mf Mtail /\\join Ms Mtail M',
                     'join Ot Of Otail /\\join Os Otail CSnext',
                     'RDYINV SCinv OwnershipReady **LINV V293_shared_li OwnershipReady nil',
                     'Of,spec_done None)|=OCframe bs', 'TaskSim BGglobal CSready']:
            self.assertIn(text, packet)
        self.assertNotIn('LINV V293_shared_li OwnershipReady nil **OCframe', packet)
        for text in ['get(BGcutL bs)OwnershipReady=Some emp',
                     'TaskLStMap BGcutA OwnershipReady=Some(true,nil,nil)',
                     'BDK ## kint BGinterrupted CSke BGcaller CSks']:
            self.assertIn(text, s)

    def test_same_three_step_endpoint_supplies_precise_free_capability_only(self):
        s = (R / Q).read_text()
        run = s.split('Theorem OCcompleted_client_cpu :', 1)[1]
        for text in ['OCcompleted_owned SCclient', 'SCthree_steps bs Mf',
                     'OCrelease_capability bs Mf Core', 'exact L1', 'exact L2', 'exact L3',
                     '(SCT3,BGcutS bs Mf,OwnershipReady)', 'free Tint32 bs Mf=Some Mr',
                     'get Mr(bs,Z.of_nat k)=None', 'get Mr(b,i)=get Mf(b,i)',
                     'SCcore **(CurTid OwnershipReady **SCframe)']:
            self.assertIn(text, run)
        self.assertNotIn('ProgSim', run)
        self.assertNotIn('BGcutS bs Mr', run)
        release = s.split('Lemma OCrelease_capability :', 1)[1].split('Qed.', 1)[0]
        for text in ['V293_tick_free_owned', 'V293_freeb_removed',
                     'V293_freeb_outside', 'V293_cpu_first_permission']:
            self.assertIn(text, release)

    def test_single_permission_factor_is_rejected_after_real_execution(self):
        protocol = read('ablation-protocol.json')
        result = read('ablation-results.json')
        self.assertTrue(protocol['prospective'] and result['passed'] and result['not_program_deletion'])
        base = (D / 'permission-base-01.v.snapshot.txt').read_text()
        mutant = (D / 'permission-mutant-01.v.snapshot.txt').read_text()
        self.assertEqual(base.count(protocol['old']), 1)
        self.assertEqual(base.replace(protocol['old'], protocol['new']), mutant)
        self.assertEqual(read('permission-base-01.json')['exit'], 0)
        self.assertEqual(read('permission-mutant-01.json')['exit'], 1)
        log = (D / 'permission-mutant-01.log').read_text()
        for text in ['The term "Free" has type', 'Full :', 'Low : lpstep', 'High : hpstep',
                     'Task : TaskSim', 'Shared : satp', 'External :', 'L1 : lpstep',
                     'H1 : hpstep', 'BaseRead :', 'ReadOnly :', 'Denied :']:
            self.assertIn(text, log)
        self.assertEqual(result['protocol_sha256'], sha(D / 'ablation-protocol.json'))
        self.assertEqual(result['production_sha256'], sha(R / P))
        self.assertEqual(result['probe_sha256'], sha(R / Q))

    def test_recursive_trust_and_stable_source_identity(self):
        trust = read('trust.json')
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], 9)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']), {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        for stem, p in [('production', P), ('probe', Q)]:
            for i in [1, 2]:
                row = read(f'{stem}-stable-{i:02d}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / p))
                self.assertEqual(row['source_sha256'], sha(R / p))

    def test_frozen_history_and_bytecode_preserved(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in read('baseline.json')['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        for name in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / name).read_bytes().endswith((D / (name + '.baseline')).read_bytes()))
        project = (R / '_CoqProject').read_bytes()
        self.assertTrue(project.startswith((D / '_CoqProject.baseline').read_bytes() + P.encode() + b'\n'))
        self.assertEqual(project.decode().splitlines().count(P), 1)
        self.assertEqual({str(p.relative_to(R)): sha(p) for p in R.rglob('*.pyc')}, read('bytecode-baseline.json'))
        for name in ['protocol', 'ablation-protocol']:
            self.assertEqual((D / (name + '.sha256')).read_text().split(),
                             [sha(D / (name + '.json')), name + '.json'])


if __name__ == '__main__':
    unittest.main()
