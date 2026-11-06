"""真实延时前缀提升为原全局轨迹；不代表整核验收。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage321-time-delay-global-switch'
OLD = R / 'audit/logs/stage320-time-delay-switch'
C = 'certiucos/v293/code/V293OSTimeDlyCall.v'
P = 'certiucos/v293/proofs/V293TimeDlyGlobalSwitch.v'
Q = 'audit/probes/V293TimeDlyGlobalSwitchProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda name: json.loads((D / name).read_text())


class TimeDelayGlobalSwitchTests(unittest.TestCase):
    def test_source_identity_and_complete_normalized_declaration(self):
        identities = read('source-identities.json')
        inventory = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        self.assertEqual(identities, json.loads((OLD / 'source-identities.json').read_text()))
        self.assertEqual([x['name'] for x in identities], ['OSTimeDly', 'OS_Sched', 'OS_SchedNew'])
        for row in identities:
            self.assertIn(row, inventory['functions'])
            self.assertEqual(sha(D / (row['name'] + '.source.c.snapshot.txt')), row['source_lines_sha256'])
            self.assertEqual(hashlib.sha256((D / (row['name'] + '.configured.c.snapshot.txt')).read_bytes()[:-1]).hexdigest(),
                             row['preprocessed_definition_sha256'])
        self.assertEqual(read('source-replay.json')['exit'], 0)
        code = (R / C).read_text()
        for text in ['sassign (evar saved) (econst32 Int.zero)', 'V293_dly_body',
                     'dcons ticks Tint32 dnil', 'dcons y Tint8 (dcons saved Tint32 dnil)']:
            self.assertIn(text, code)

    def test_extension_preserves_actual_positive_semantics(self):
        source = (R / P).read_text()
        for text in ['V293_sstep_function_extension', 'V293_cstep_function_extension',
                     'V293_loststep_function_extension', 'V293_local_function_extension',
                     'P f=Some fn ->Q f=Some fn', 'inversion Step', 'induction Trace',
                     'eapply stmt_step', 'apply ostc_step', 'eapply rt1n_trans']:
            self.assertIn(text, source)
        self.assertNotIn('Require Import CertiOS.audit.', source)
        self.assertIn('positive traces only', read('function-boundary.json')['extension_scope'])

    def test_bridge_consumes_local_trace_not_global_or_store_oracle(self):
        source = (R / P).read_text().split('Theorem V293_dly_trace_switch_global :', 1)[1]
        statement, proof = source.split('Proof.', 1)
        inputs, outputs = statement.split('exists Mf,', 1)
        self.assertIn('V293_local_steps P', inputs)
        self.assertIn('P f=Some(V293_dly_function', inputs)
        for token in ['V293_global_steps', 'lpstep', 'store(', 'ProgSim', 'SWINV']:
            self.assertNotIn(token, inputs)
        for token in ['V293_global_steps', 'lpstep', 'inner##outer', 'store(Tptr tp)', 'b<>bc']:
            self.assertIn(token, outputs)
        for token in ['V293_local_steps_global', 'V293_sched_switch_commit',
                      'V293_global_trans', 'V293_local_function_extension', 'rewrite Bind']:
            self.assertIn(token, proof)

    def test_nonempty_closed_instance_both_ie_wrap_and_resources(self):
        source = (R / Q).read_text()
        statement = source.split('Theorem DGglobal_switch:', 1)[1].split('Proof.', 1)[0]
        self.assertEqual(statement.split('exists bs byblock Mcut Mf,', 1)[0].strip(), 'forall c enabled,')
        for token in ['V293_global_steps DGprog DWclient', 'V293_task_records Mf', 'V293_byteval 4',
                      'Vint32(Int.add c Int.one)', 'Vint32(Int.repr 99)', 'V293_bytes_writable Mf bs',
                      'get Mf(byblock,0%Z)=None', 'DScontinuation##DGouter',
                      'get DGtasks OwnershipWaiting=Some DWready',
                      'get(DWenvs bs)OwnershipWaiting=Some DEle',
                      'get(DWaux enabled)OwnershipReady=Some(false,nil,[enabled])']:
            self.assertIn(token, statement)
        for token in ['destruct(DWblocked_run c enabled)', 'DGextends', 'V293_dly_trace_switch_global',
                      'TaskLStMod.set', 'rewrite Aux in Global', 'V293_task_record_frame',
                      'Theorem DGboth_IE', 'DGglobal_switch Int.zero true', 'DGglobal_switch Int.zero false',
                      'Theorem DGglobal_wrap', 'Int.repr Int.max_unsigned', 'rewrite DWcounter_wrap']:
            self.assertIn(token, source)

    def test_single_helper_binding_ablation_is_only_early_linkage(self):
        source = (R / Q).read_text()
        for token in ['if Z.eq_dec f 113%Z then None else DGprogram f',
                      'Lemma DGablation_only_helper', 'forall f,f<>113%Z ->DGwithout_helper f=DGprogram f',
                      'Theorem DGhelper_boundary:forall ks st,',
                      'loststep DGprogram(curs(sfexec 113%Z nil nil),(kenil,ks))st',
                      'loststep DGwithout_helper(curs(sfexec 113%Z nil nil),(kenil,ks))st',
                      'eapply sfexec_step', 'V293_missing_port_has_no_step']:
            self.assertIn(token, source)
        protocol = read('protocol.json')
        self.assertTrue(protocol['prospective'])
        self.assertIn('not evidence for downstream', protocol['ablation']['expected'])
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])

    def test_recursive_trust_and_two_source_stable_compiles(self):
        roots = []
        for p in [C, P, Q]:
            source = (R / p).read_text()
            self.assertNotRegex(source, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', source, re.M)]
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(x['exit'] == 0 for x in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']), {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        for name, p in [('code', C), ('production', P), ('probe', Q)]:
            for i in [1, 2]:
                result = read(f'stable-{name}-{i}.json')
                self.assertEqual(result['exit'], 0)
                self.assertEqual(result['initial_source_sha256'], sha(R / p))
                self.assertEqual(result['source_sha256'], sha(R / p))

    def test_frozen_history_append_only_registration_and_bytecode(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in read('baseline.json')['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        project = (R / '_CoqProject').read_bytes()
        self.assertTrue(project.startswith((D / '_CoqProject.baseline').read_bytes() + (C + '\n' + P + '\n').encode()))
        for p in [C, P]:
            self.assertEqual(project.splitlines().count(p.encode()), 1)
        self.assertEqual({str(p.relative_to(R)): sha(p) for p in R.rglob('*.pyc')}, read('bytecode-baseline.json'))

    def test_scope_does_not_promote_global_trace_to_global_invariant(self):
        boundary = read('function-boundary.json')
        self.assertFalse(boundary['full_api_proved'])
        self.assertFalse(boundary['priority_cache_synchronized'])
        self.assertTrue(all(x['located'] and not x['full_target_linked'] for x in boundary['stages'].values()))
        self.assertIn('after cpu_sr initializer', boundary['entry'])
        self.assertIn('original lpstep closure', boundary['positive_endpoint'])
        doc = (R / 'audit/STAGE321_TIME_DELAY_GLOBAL_SWITCH.md').read_text()
        for token in ['不是完整 API', '不是全局记录不变量', '不是全局 ProgSim',
                      '优先级缓存', 'GOOD_OS', 'uCOS3', '正向存在轨迹', '早期调用链接门']:
            self.assertIn(token, doc)
        for name in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / name).read_bytes().endswith((D / (name + '.baseline')).read_bytes()))


if __name__ == '__main__':
    unittest.main()
