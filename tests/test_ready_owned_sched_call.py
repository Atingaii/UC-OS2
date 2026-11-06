"""调度调用联合资源的身份/连线回归；语义由 Coq 编译及递归内核复核。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage327-ready-owned-sched-call'
OLD = R / 'audit/logs/stage326-time-delay-ready-closure'
P = 'certiucos/v293/proofs/V293ReadyOwnedSchedCall.v'
Q = 'audit/probes/V293ReadyOwnedSchedCallProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class ReadyOwnedSchedCallTests(unittest.TestCase):
    def test_locked_source_replay(self):
        rows = read('source-identities.json')
        self.assertEqual(rows, json.loads((OLD / 'source-identities.json').read_text()))
        self.assertEqual({r['name'] for r in rows}, {'OSTimeDly', 'OS_Sched', 'OS_SchedNew'})
        inventory = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        for r in rows:
            self.assertIn(r, inventory['functions'])
            self.assertEqual(sha(D / (r['name'] + '.source.c.snapshot.txt')), r['source_lines_sha256'])
            self.assertEqual(hashlib.sha256((D / (r['name'] + '.configured.c.snapshot.txt')).read_bytes()[:-1]).hexdigest(),
                             r['preprocessed_definition_sha256'])
        self.assertEqual(read('source-replay.json')['exit'], 0)

    def test_stable_interface_constructs_actual_call_from_owned_resources(self):
        s = (R / P).read_text()
        statement, proof = s.split('Theorem V293_owned_sched_call :', 1)[1].split('Proof.', 1)
        inputs, outputs = statement.split('exists bs byblock Mi My Mh Mtarget Mf,', 1)
        for token in ['V293_local_steps', 'V293_global_steps', 'cstepstar', 'store ', 'SWINVt', 'rdy,message']:
            self.assertNotIn(token, inputs)
        for token in ['V293_OSSched_success_function', 'V293_OSSchedNew_function',
                      'GoodInvAsrt R', 'V293_ready_full br bg bp current **',
                      'V293_owned_sched_frame', '(enabled,nil,ci)', 'nc<256']:
            self.assertIn(token, inputs)
        for token in ['curs(scall f nil)', 'kcall f(V293_OSSched_success_body',
                      '(false,nil,enabled::ci)', 'SWINVt(V293_ready_inv br bg bp)current **',
                      'fresh M bs', 'fresh Mi byblock', 'free Tint8 byblock My=Some Mh',
                      'get Mh(byblock,0%Z)=None', 'store Tint32 Mtarget',
                      'load(Tptr V293_tcb_type)Mf', 'load Tint32 Mf']:
            self.assertIn(token, outputs)
        for token in ['V293_sched_call_enter', 'V293_cpu_initialized_frame',
                      'good_inv_prop', 'V293_sched_control_enter',
                      'V293_ready_dispatch_call', 'V293_ready_source_change']:
            self.assertIn(token, proof)
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertNotRegex(s, r'Require Import CertiOS\.(?:ucos|os_code|os_proof)\.')

    def test_flags_and_frame_transport_have_explicit_boundary(self):
        s = (R / P).read_text()
        disabled = s.split('Lemma V293_owned_ready_disabled', 1)[1].split('Definition V293_owned_sched_frame', 1)[0]
        for token in ['(fun _:hid=>false)', '(false,nil,ci)', 'V293_shared_flags',
                      'V293_ready_switch_halves', '(emp:mem)', '(emp:osabst)']:
            self.assertIn(token, disabled)
        for token in ['assert(GFrame:GoodInvAsrt F)', 'V293_owned_ready_good',
                      'GoodInvAsrt(Amapsto(bs,0%Z)', 'LookupI:forall n', 'V293_load_block_frame']:
            self.assertIn(token, s)
        self.assertNotIn('assert(GRest:', s)
        q = (R / Q).read_text()
        rest = q.split('Definition DOrest:=', 1)[1].split('Lemma DOrest_good', 1)[0]
        self.assertNotIn('V293_priority_cells', rest)
        for token in ['90%positive', '11%positive', '12%positive', '13%positive', 'V293_read_bytes 80%positive']:
            self.assertIn(token, rest)
        lookup = q.split('Lemma DOlookup:', 1)[1].split('Lemma DOselected:', 1)[0]
        self.assertIn('V293_read_bytes_load', lookup)

    def test_same_global_client_link_and_joint_endpoint(self):
        s = (R / Q).read_text()
        st, pf = s.split('Theorem DOglobal_sched:', 1)[1].split('Proof.', 1)
        self.assertEqual(st.split('exists bs')[0], 'forall c enabled,')
        for token in ['DRrun c enabled Mb', 'DRpost c enabled Mb', 'DXrun c enabled bs Mf',
                      'DOpost c enabled bs Mf', 'free Tint8 byblock My=Some Mh',
                      'cstepstar DAprogram', 'DOcontinuation', 'store Tint32 Mt']:
            self.assertIn(token, st)
        for token in ['DRglobal_ready c enabled', 'V293_owned_sched_call', 'DOentry c enabled Mb Owned',
                      'DOlookup c enabled Mb Owned', 'DOselected', 'V293_global_trans',
                      'V293_local_function_extension', 'V293_local_steps_global', 'unfold DOrest in Final']:
            self.assertIn(token, pf)
        selected = s.split('Lemma DOselected:', 1)[1].split('Definition DOcells', 1)[0]
        self.assertIn('DStask_blocks', selected)
        self.assertIn('wait os_stat_time(Int.repr 3)', selected)
        self.assertIn('V293_priority_repr_injective', selected)
        post = s.split('Definition DOpost', 1)[1].split('Definition DOcontinuation', 1)[0]
        self.assertIn('SWINVt(V293_ready_inv 30%positive 31%positive 83%positive)OwnershipReady **', post)
        self.assertIn('V293_owned_record_cells(DOcells c) **', post)
        self.assertIn('V293_read_bytes 80%positive', post)

    def test_both_ie_wraparound_cpu_permissions_and_canary(self):
        s = (R / Q).read_text()
        for token in ['Theorem DOboth_IE:', 'DOglobal_sched c false', 'DOglobal_sched c true',
                      'Theorem DOwrap:', 'DWcounter_wrap', 'Lemma DOobserved:',
                      'V293_bytes_writable Mf bs 0%Z 4', 'V293_bytes_writable Mf 13%positive 0%Z 4',
                      'V293_tick_raw_owned_writable', 'DScells_load', 'Int.repr 99',
                      'Lemma DOcounter_changes:', 'Int.add_neg_zero']:
            self.assertIn(token, s)

    def test_prospective_late_observation_single_factor(self):
        protocol = read('protocol.json')
        self.assertTrue(protocol['prospective'])
        self.assertEqual(sha(D / 'protocol.json'), 'b0cb6670fec4745387c7f8786e8eada5873732b639706d58132cf3601a24061b')
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
        self.assertIn('same actual execution, heap, helper release and joint resources', protocol['ablation']['factor'])
        self.assertEqual(protocol['ablation']['scope'], 'late counter observation gate only, not a mutant whole-program execution')
        s = (R / Q).read_text()
        self.assertIn('if observe then Int.add c Int.one else c', s)
        gate = s.split('Theorem DOlate_ablation:', 1)[1].split('Proof.', 1)[0]
        for token in ['DXrun c enabled bs Mf', 'DOpost c enabled bs Mf',
                      'free Tint8 byblock My=Some Mh', 'V293_bytes_writable Mf', 'Int.repr 99',
                      'Some(Vint32(DOchosen_counter true c))', '<>Some(Vint32(DOchosen_counter false c))']:
            self.assertIn(token, gate)
        self.assertEqual(gate.count('exists bs byblock My Mh Mf,'), 1)
        self.assertIn('apply(DOcounter_changes c)', s)

    def test_recursive_kernel_trust_and_stable_sources(self):
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
        trust = read('trust.json')
        self.assertEqual(len(roots), 13)
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], 13)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(row['exit'] == 0 for row in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']), {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        for name, p in [('production', P), ('probe', Q)]:
            for i in [1, 2]:
                row = read(f'stable-{name}-{i}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / p))
                self.assertEqual(row['source_sha256'], sha(R / p))

    def test_history_and_precise_noncompletion_boundary(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in read('baseline.json')['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        for n in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / n).read_bytes().endswith((D / (n + '.baseline')).read_bytes()))
        project = (R / '_CoqProject').read_bytes()
        self.assertTrue(project.startswith((D / '_CoqProject.baseline').read_bytes() + (P + '\n').encode()))
        self.assertEqual(project.splitlines().count(P.encode()), 1)
        self.assertEqual({str(p.relative_to(R)): sha(p) for p in R.rglob('*.pyc')}, read('bytecode-baseline.json'))
        b = read('function-boundary.json')
        for n in ['joint_ready_ownership_through_actual_scheduler_helper', 'actual_helper_release_boundary',
                  'same_raw_global_client_call', 'both_initial_IE']:
            self.assertTrue(b[n])
        for n in ['joint_ownership_across_scheduler_switch', 'full_api_proved', 'priority_cache_synchronized',
                  'resumption_return_proved', 'global_ProgSim_proved', 'GOOD_OS_proved', 'final_helper_block_fresh_proved']:
            self.assertFalse(b[n])
        self.assertTrue(all(row['located'] and not any(v for k, v in row.items() if k != 'located')
                            for row in b['stages'].values()))
        doc = (R / 'audit/STAGE327_READY_OWNED_SCHED_CALL.md').read_text()
        for token in ['不是完整 API', '不是全局记录不变量', '不是全局 ProgSim', '不是 GOOD_OS',
                      '只在末端计数观察门', '不是修改程序后的完整执行', 'GoodInvAsrt R', 'Mh', 'uCOS3']:
            self.assertIn(token, doc)


if __name__ == '__main__':
    unittest.main()
