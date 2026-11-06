"""第338步接口及证据回归；数学有效性由 Coq 编译和递归 coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage338-time-source-ready-call'
OLD = R / 'audit/logs/stage337-time-source-connection'
P = 'certiucos/v293/proofs/V293TimeSourceReadyCall.v'
Q = 'audit/probes/V293TimeSourceReadyCallProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class TimeSourceReadyCallTests(unittest.TestCase):
    def test_protocol_frozen_and_single_factor_bounded(self):
        self.assertEqual((D / 'protocol.sha256').read_text().split(),
                         [sha(D / 'protocol.json'), 'protocol.json'])
        p = read('protocol.json')
        self.assertTrue(p['prospective'])
        self.assertIn('only abstract clock slot', p['ablation']['factor'])
        self.assertIn('not a mutant operational execution', p['ablation']['scope'])

    def test_real_caller_inputs_no_execution_or_store_oracles(self):
        text = (R / P).read_text()
        for mode in ['get', 'set']:
            part = text.split(f'Theorem V293_source_time_{mode}_ready_call :', 1)[1].split('\nQed.', 1)[0]
            pre = part.split('  exists Mc Mf,', 1)[0]
            self.assertIn('(ge,caller,M,ir,(enabled,si,ci),O,', pre)
            self.assertIn('V293_time_ready_core br bg bp bn ** CurTid t', pre)
            self.assertIn('fresh M bt -> fresh M bs -> bt<>bs', pre)
            self.assertNotRegex(pre, r'\b(?:store|V293_local_steps|freels|spec_step)\b')
            self.assertIn(f'V293_time_{mode}_call_entry', part)
            self.assertIn(f'V293_time_{mode}_body_refinement', part)
            self.assertIn('eapply V293_local_trans', part)

    def test_linearization_heap_bound_to_both_real_paths(self):
        text = (R / P).read_text()
        for mode in ['get', 'set']:
            part = text.split(f'Theorem V293_source_time_{mode}_ready_call :', 1)[1].split('Proof.', 1)[0]
            self.assertEqual(part.count('V293_local_steps P'), 3)
            self.assertEqual(part.count('((ge,V293_time_call_locals ticks saved bt bs,Mc),ir,(false,si,enabled::ci))'), 2)
            self.assertIn('freels(getaddr(V293_time_call_locals ticks saved bt bs))Mc Mf', part)
            self.assertIn('(ge,caller,Mf,ir,(enabled,si,ci)', part)

    def test_source_program_and_strong_builder_reuse(self):
        p, q = (R / P).read_text(), (R / Q).read_text()
        self.assertIn('Definition SRprogram := V293_source_time_program', q)
        self.assertNotIn('V293_local_steps Cprogram', q)
        for mode in ['Get', 'Set']:
            self.assertIn(f'eapply V293_Time{mode}_ready_api_contract; eassumption', p)
        self.assertIn('V293_time_ready_names_good', p)
        self.assertIn('Theorem SRsource_ready_component', q)

    def test_nonempty_inputs_both_IE_and_eight_freed_bytes(self):
        q = (R / Q).read_text()
        for mode in ['get', 'set']:
            part = q.split(f'Theorem SR{mode}_nonempty_both_IE :', 1)[1].split('\nQed.', 1)[0]
            self.assertIn('forall caller ks ct clock enabled', part)
            self.assertIn('SRinput caller enabled ct clock', part)
            self.assertIn('eapply SRremoved;exact Freed', part)
            self.assertIn('get Mf(160%positive,Z.of_nat k)=None /\\ get Mf(161%positive,Z.of_nat k)=None', part)

    def test_late_control_keeps_real_execution_and_same_heap(self):
        q = (R / Q).read_text()
        part = q.split('Theorem SRset_stale_abstract_control :', 1)[1].split('\nQed.', 1)[0]
        self.assertIn('SRset caller ks ct clock enabled n Mf', part)
        self.assertIn('load Tint32 Mf(150%positive,0%Z)=Some(Vint32 n)', part)
        self.assertIn('SRstate caller enabled Mf(TRabstract ct n)(END None) |= SRcore ** CurTid ct', part)
        self.assertIn('~ SRstate caller enabled Mf(TRabstract ct clock)(END None) |= SRcore ** CurTid ct', part)
        self.assertIn('pose proof(SRclock', part)
        self.assertIn('congruence.', part)
        self.assertNotIn('Cprogram', part)

    def test_repeated_compilation_and_recursive_trust(self):
        for label, source in [('proof', P), ('probe', Q)]:
            for i in [1, 2]:
                row = read(f'stable-{label}-{i}.json')
                self.assertEqual(row['exit'], 0)
                self.assertEqual(row['initial_source_sha256'], sha(R / source))
                self.assertEqual(row['source_sha256'], sha(R / source))
        trust = read('trust.json')
        roots = [Path(p).stem + '.' + n for p in [P, Q] for n in
                 re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', (R / p).read_text(), re.M)]
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']),
                             {'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        for p in [P, Q]:
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
        self.assertNotIn('Require Import CertiOS.audit.', (R / P).read_text())

    def test_fresh_source_replay_distinct_from_resource_control(self):
        for i in [1, 2]:
            replay = read(f'replay-{i}/report.json')
            self.assertTrue(replay['passed'] and replay['gcc_clang_agreement'])
            self.assertEqual([c['exit'] for c in replay['checks']], [0, 1, 1])
            self.assertTrue(all(c['decoder_accepted'] for c in replay['checks']))
            self.assertEqual(replay['sources'], {'OSTimeGet': 'OSTime', 'OSTimeSet': 'ticks'})
            self.assertEqual(replay['inputs'], json.loads((OLD / 'replay-1/report.json').read_text())['inputs'])
            self.assertTrue(all(sha(R / p) == h for p, h in replay['inputs'].items()))

    def test_old_inputs_frozen_and_project_only_appended(self):
        self.assertEqual([p for p, h in read('baseline.json').items()
                          if not (R / p).is_file() or sha(R / p) != h], [])
        old = json.loads((OLD / 'checkpoint-evidence-manifest.json').read_text())
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject'}
        self.assertEqual([p for p, row in old.items() if p not in mutable
                          and sha(R / p) != row['sha256']], [])
        prefix = (D / '_CoqProject.baseline').read_bytes() + (P + '\n').encode()
        current = (R / '_CoqProject').read_bytes()
        self.assertTrue(current.startswith(prefix))
        self.assertTrue(all(n.startswith('certiucos/v293/') and n.endswith('.v')
                            for n in current[len(prefix):].decode().splitlines()))
        for n in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / n).read_bytes().endswith((D / (n + '.baseline')).read_bytes()))

    def test_document_claims_bounded(self):
        doc = (R / 'audit/STAGE338_TIME_SOURCE_READY_CALL.md').read_text()
        for term in ['不是经验证C前端', 'ADR0005', '不是运行时突变程序', 'GOOD_OS', 'K1–K4',
                     'uCOS3', '两个CPU hook仍缺实现', '总目标保持active', '旧覆盖清单不改写']:
            self.assertIn(term, doc)
