"""入口契约及证据回归；逻辑有效性由 Coq 与递归 coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage257-sched-call-entry-progsim'
PROD = 'certiucos/v293/proofs/V293SchedCallEntryProgSim.v'
PROBE = 'audit/probes/V293SchedCallEntryProgSimProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class SchedCallEntryProgSimTests(unittest.TestCase):
    def test_original_relation_and_all_successor_family(self):
        self.assertEqual(sha(D / 'protocol.json'), (D / 'protocol.sha256').read_text().strip())
        src = (R / PROD).read_text()
        self.assertNotIn('CertiOS.audit.', src)
        all_steps = theorem(src, 'V293_os_family_all_successors')
        for term in ['lpstep P T cst S t Tf cf Sf tf ->', 'inversion H',
                     'cstep(pumerge po pi)', 'set les t le\'', 'tf=t']:
            self.assertIn(term, all_steps)
        bridge = theorem(src, 'V293_os_family_progsim')
        for term in ['apply simulation.prog_sim', 'V293_os_family_all_successors',
                     'V293_os_family_no_output', 'V293_os_family_no_abort']:
            self.assertIn(term, bridge)
        self.assertIn('lpstep P', theorem(src, 'V293_os_family_progress'))
        self.assertIn('LocalStep', theorem(src, 'V293_os_family_no_abort'))

    def test_actual_call_four_steps_and_universal_body_obligation(self):
        src = (R / PROD).read_text()
        main = theorem(src, 'V293_sched_call_entry_progsim')
        statement = main.split('Proof.', 1)[0]
        for term in ['forall b,fresh M b ->', 'Some((false,si,cs):localst)',
                     'get les t=Some caller', 'InOS(SKIP,(kenil,ks))',
                     'set les t(set emp y(b,Tint8):env)', 'allocb M b 0%Z 1',
                     'kcall f(V293_OSSchedNew_body unmap group rows high y)caller ks']:
            self.assertIn(term, statement)
        self.assertEqual(statement.count('ProgSim'), 2)
        for term in ['V293_call_nil_successor', 'V293_sched_exec_successor',
                     'V293_byte_alloc_successor', 'V293_alloc_end_successor',
                     'memory_has_fresh_block M', 'apply Post;exact F']:
            self.assertIn(term, main)
        self.assertEqual(main.count('eapply V293_os_family_progsim'), 4)
        self.assertNotIn('cstepstar', main)
        alloc = theorem(src, 'V293_byte_alloc_step')
        self.assertIn('salloclv_step', alloc)
        self.assertNotIn('store ', alloc)

    def test_two_real_successors_and_independent_prefix(self):
        src = (R / PROBE).read_text()
        self.assertIn('CGentry', theorem(src, 'CEtyped_heap'))
        progress = theorem(src, 'CEall_fresh_global_progress')
        self.assertNotIn('ProgSim', progress)
        self.assertIn('V293_byte_alloc_step', progress)
        classify = theorem(src, 'CEall_global_successors')
        self.assertIn('V293_os_family_all_successors', classify)
        self.assertIn('V293_byte_alloc_successor', classify)
        two = theorem(src, 'CEtwo_fresh_successors')
        for term in ['lpstep', 'CELb b1<>CELb b2', 'CEMb b1<>CEMb b2',
                     'V293_ready_fresh_avoiding CEM [b1]', 'V293_success_fresh_none']:
            self.assertIn(term, two)
        unique = theorem(src, 'CEunique_allocation_rejected')
        self.assertIn('~exists C\' m\'', unique)
        self.assertEqual(unique.count('V293_byte_alloc_step'), 2)
        prefix = theorem(src, 'CEactual_prefix_all_fresh')
        for term in ['forall b,fresh CEM b ->', 'cstepstar CGprogram',
                     'get(CELb b)120%Z=None', 'Some(true,Undef)', 'sfexec_step']:
            self.assertIn(term, prefix)
        self.assertNotIn('ProgSim', prefix)
        self.assertIn('V293_sched_call_entry_progsim', theorem(src, 'CEactual_call_entry'))

    def test_stable_compiles_and_recursive_trust(self):
        roots = []
        stable = read('stable-compiles.json')
        for key, p in [('production', PROD), ('probe', PROBE)]:
            src = (R / p).read_text()
            self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
            result = read(stable[key] + '.json')
            self.assertEqual(result['exit'], 0)
            self.assertEqual(result['initial_source_sha256'], sha(R / p))
            self.assertEqual(result['source_sha256'], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        for label in stable['repeat_passes']:
            self.assertEqual(read(label + '.json')['exit'], 0)
        self.assertEqual(len(roots), 20)
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})
        self.assertEqual(read('build.json')['exit'], 0)
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(PROD), 1)

    def test_chinese_scope_and_historical_document_tails(self):
        doc = (R / 'audit/STAGE257_SCHED_CALL_ENTRY_PROGSIM.md').read_text()
        for term in ['不是 `GOOD_OS`', '不是 `WFInt`', '不是任意 client', 'IE=false',
                     '后续模拟', 'ADR-0010', 'K1–K4 未闭合', 'uCOS3 未开始',
                     '未提交／推送', '所有合法新鲜块', '尚未独立建立']:
            self.assertIn(term, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- sched-call-entry-progsim-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
        identity = read('source-identity.json')
        self.assertTrue(identity['passed'])
        for p, h in identity['files'].items():
            self.assertEqual(sha(R / p), h)
