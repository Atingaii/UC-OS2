"""接口和证据身份回归；数学证明由真实 Coq/coqchk 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage255-handoff-progsim'
PROD = 'certiucos/v293/proofs/V293HandoffProgSim.v'
PROBE = 'audit/probes/V293HandoffProgSimProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


def theorem(src, name):
    return src.split(name + ' :', 1)[1].split('Qed.', 1)[0]


class HandoffProgSimTests(unittest.TestCase):
    def test_protocol_and_unchanged_original_inputs(self):
        self.assertEqual(sha(D / 'protocol.json'), (D / 'protocol.sha256').read_text().strip())
        for p, h in read('baseline.json')['files'].items():
            if p not in ['README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d']:
                self.assertEqual(sha(R / p), h, p)
        dep = (R / '.Makefile.coq.d').read_bytes().splitlines(keepends=True)
        added = [line for line in dep if b'certiucos/v293/proofs/V293HandoffProgSim' in line]
        self.assertEqual(len(added), 3)
        previous = b''.join(line for line in dep if line not in added)
        self.assertEqual(hashlib.sha256(previous).hexdigest(), read('baseline.json')['files']['.Makefile.coq.d'])
        self.assertTrue(read('generated-dependency-change.json')['unchanged_previous_bytes'])
        before, after = (R / '_CoqProject').read_bytes().split((PROD + '\n').encode(), 1)
        self.assertEqual(hashlib.sha256(before).hexdigest(), read('baseline.json')['files']['_CoqProject'])
        self.assertNotIn((PROD + '\n').encode(), after)
        for p, h in read('source-identity.json')['files'].items():
            self.assertEqual(sha(R / p), h, p)

    def test_original_all_successors_outputs_and_abort(self):
        src = (R / PROD).read_text()
        self.assertNotIn('CertiOS.audit.', src)
        for name in ['V293_os_silent_progress', 'V293_os_silent_all_successors',
                     'V293_os_silent_no_output', 'V293_os_silent_no_abort',
                     'V293_store_cstep_unique']:
            self.assertIn(name + ' :', src)
        pull = theorem(src, 'V293_os_silent_progsim')
        for term in ['apply simulation.prog_sim', 'V293_os_silent_all_successors',
                     'V293_os_silent_no_output', 'V293_os_silent_no_abort']:
            self.assertIn(term, pull)
        copy = theorem(src, 'V293_handoff_copy_progsim')
        for i in range(7):
            self.assertIn('assert(S' + str(i) + ':cstep', copy)
        for term in ['cstep_idmove_deter', 'V293_store_cstep_unique', 'V293_context_inos']:
            self.assertIn(term, copy)
        bridge = theorem(src, 'V293_handoff_progsim')
        statement = bridge.split('Proof.', 1)[0]
        self.assertIn('hpstepstar ph Th cst O Thf cst Of ->', statement)
        self.assertEqual(statement.count('ProgSim'), 2)
        self.assertIn('Some((false,si,cs):localst)', statement)
        self.assertNotIn('SWINVt', statement)
        self.assertIn('V293_handoff_copy_progsim', bridge)
        self.assertIn('V293_switch_progsim', bridge)

    def test_typed_same_pending_nonterminal_and_independent_post(self):
        src = (R / PROBE).read_text()
        self.assertIn('Definition HPpending:=CGpending ## CGouter.', src)
        actual = theorem(src, 'HPactual_handoff_simulation')
        for term in ['CGlocal_ready', 'V293_handoff_copy_execution', 'HPpending',
                     'V293_ready_storage_switch_step', 'apply GHrejected',
                     'apply HPschedule', 'eapply HPbridge']:
            self.assertIn(term, actual)
        self.assertNotIn('ProgSim', actual.split('exists M Mc Mf,', 1)[0])
        self.assertIn('~IsEnd V293_skip_client_code', theorem(src, 'HPtarget_not_ended'))
        self.assertIn('HPfinite_simulation', theorem(src, 'HPpost'))
        sim = theorem(src, 'HPfinite_simulation')
        self.assertEqual(sim.count('eapply HPclient_pull'), 2)
        self.assertIn('eapply SPterminal', sim)
        for name in ['HPclient_all', 'HPclient_no_output', 'HPclient_no_abort']:
            self.assertIn(name, theorem(src, 'HPclient_pull'))

    def test_separate_single_factor_controls(self):
        src = (R / PROBE).read_text()
        self.assertIn('RIabstract OwnershipWaiting', theorem(src, 'HPzero_high_match_rejected'))
        self.assertIn('~lintstep', theorem(src, 'HPdisabled_no_interrupt'))
        self.assertIn('(false,nil,nil)', theorem(src, 'HPdisabled_no_interrupt'))
        self.assertIn('HPboundary_aux true', theorem(src, 'HPenabled_interrupt'))
        self.assertIn('eapply pint_step', theorem(src, 'HPenabled_interrupt'))
        ablation = read('import-ablation-results.json')
        self.assertTrue(ablation['single_factor'] and ablation['proof_statements_and_bodies_unchanged'])
        self.assertTrue(all(r['exit'] == 0 and r['removal_retained'] for r in ablation['results']))
        review = read('adversarial-review.json')
        for k in ['same_pending_copy_switch', 'independent_finite_client_global_post',
                  'typed_nonterminal_witness', 'guard_rejection_preserved', 'high_current_control',
                  'independent_IE_boundary_control']:
            self.assertTrue(review[k], k)

    def test_actual_stable_compiles_and_recursive_trust(self):
        roots = []
        for key, p in [('production', PROD), ('probe', PROBE)]:
            src = (R / p).read_text()
            self.assertIsNone(re.search(r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b', src))
            c = read(read('stable-compiles.json')[key] + '.json')
            self.assertEqual(c['exit'], 0)
            self.assertEqual(c['initial_source_sha256'], c['source_sha256'])
            self.assertEqual(c['source_sha256'], sha(R / p))
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', src, re.M)]
        self.assertEqual(len(roots), 29)
        for n in read('stable-compiles.json')['repeat_passes']:
            self.assertEqual(read(n + '.json')['exit'], 0)
        trust = read('trust.json')
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], 29)
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertTrue(set(trust['assumptions']) <= {
            'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'})

    def test_chinese_scope_and_preserved_document_tails(self):
        doc = (R / 'audit/STAGE255_HANDOFF_PROGSIM.md').read_text()
        for term in ['不是任意 client', '不是 `WFInt`', '不是 `GOOD_OS`', 'ADR-0010',
                     'K1–K4 未闭合', 'uCOS3 未开始', '未提交／推送', 'CGpending ## CGouter',
                     '高层调度匹配', 'IE=false']:
            self.assertIn(term, doc)
        for p in ['README.md', 'VERIFICATION_STATUS.md']:
            tail = (R / p).read_bytes().split(b'<!-- handoff-progsim-checkpoint-end -->\n\n', 1)[1]
            self.assertEqual(hashlib.sha256(tail).hexdigest(), read('baseline.json')['files'][p])
        review = read('adversarial-review.json')
        for k in ['arbitrary_clients', 'arbitrary_suspended_TaskSim_contract_proved',
                  'full_continuation_prefix_to_return', 'WFInt', 'GOOD_OS', 'uCOS3_started',
                  'raw_external_port_refinement', 'unrestricted_interrupt_interleavings']:
            self.assertFalse(review[k], k)
        for p, h in review['source_sha256'].items():
            self.assertEqual(sha(R / p), h)
