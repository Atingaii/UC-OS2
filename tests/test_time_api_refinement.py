"""时间 API 临界抽象步与精确返回资源回归；语义结论由 Coq 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage181-time-api-refinement'
PROD = 'certiucos/v293/proofs/V293TimeAPIRefinement.v'
PROBE = 'audit/probes/V293TimeAPIRefinementProbe.v'


def statement(src, name):
    return src.split('Theorem ' + name + ' :', 1)[1].split('Proof.', 1)[0]


class TimeAPIRefinementTests(unittest.TestCase):
    def test_fixed_source_and_previous_evidence(self):
        base = json.loads((D / 'baseline.json').read_text())['files']
        for p in ('certiucos/v293/proofs/V293TimeAccess.v',
                  'certiucos/v293/proofs/V293TimeAPILifecycle.v',
                  'audit/probes/V293TimeAPILifecycleProbe.v',
                  'framework/logic/inferules.v',
                  'audit/logs/stage180-time-api-lifecycle/checkpoint-evidence-manifest.json'):
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), base[p])
        source = json.loads((D / 'source-check.json').read_text())
        data = (R / source['actual_file']).read_bytes()
        self.assertEqual(hashlib.sha256(data).hexdigest(), source['file_sha256'])
        for row in source['functions'].values():
            lo, hi = row['lines']
            part = b''.join(data.splitlines(keepends=True)[lo-1:hi])
            self.assertEqual(hashlib.sha256(part).hexdigest(), row['sha256'])
        identity = json.loads((D / 'protocol-identity.json').read_text())
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(), identity['protocol.json'])

    def test_derived_abstract_step_and_exact_return_contract(self):
        src = (R / PROD).read_text()
        for name in ('V293_time_set_body_refinement', 'V293_time_get_body_refinement'):
            stmt = statement(src, name)
            self.assertIn('GoodFunAsrt R -> can_change_aop R ->', stmt)
            self.assertIn('exists Mz Mc Mf', stmt)
            self.assertIn('spec_step sd', stmt)
            self.assertIn('V293_time_ready_core br bg bp bn ** R', stmt)
            self.assertIn('(ge,caller,Mf,ir,(enabled,si,ci)', stmt)
            self.assertIn('freels(getaddr(V293_time_call_locals', stmt)
            self.assertIn('(false,si,enabled::ci)', stmt)
            self.assertNotIn('evalval', stmt)
            self.assertLess(stmt.index('->'), stmt.index('spec_step sd'))
        for token in ('V293_shared_replace_slot', 'V293_time_set_transition',
                      'V293_time_get_transition', 'V293_time_owned_return',
                      'V293_tick_free_owned', 'sfreeend_step', 'srete_step',
                      'V293_time_cell_raw', 'good_fun_asrt_absop'):
            self.assertIn(token, src)
        self.assertNotIn('CertiOS.audit.', src)
        for p in (PROD, PROBE):
            self.assertNotRegex((R / p).read_text(), r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')

    def test_same_actual_call_preserves_exact_caller_resource(self):
        src = (R / PROBE).read_text()
        for name, call in (('Rset_actual_refinement', 'CsetExec'), ('Rget_actual_refinement', 'CgetExec')):
            stmt = statement(src, name)
            self.assertIn(call + ' caller ks ct clock', stmt)
            self.assertIn('Ccore ** J', stmt)
            self.assertIn('Rfinal caller Mf', stmt)
            self.assertIn('Ccore ** CurTid ct', stmt)
            self.assertIn('freels(getaddr JLE)Mc Mf', stmt)
        for token in ('V293_time_set_call_entry Cprogram', 'V293_time_get_call_entry Cprogram',
                      '(Ccore ** CurTid ct)', 'Jcore_and_current', 'Rnamed',
                      'Cpack_set', 'Cpack_get', 'exact Prefix | exact Suffix'):
            self.assertIn(token, src)
        self.assertNotIn('Lowned', src)
        self.assertIn('spec_step V293_scheduler V293_time_get_action(TRabstract ct clock)(END(Some(Vint32 clock)))(TRabstract ct clock)', src)

    def test_single_factor_controls_and_real_frees(self):
        src = (R / PROBE).read_text()
        ghost = statement(src, 'Rset_ghost_omission_control')
        self.assertIn('Rcritical Mc(TRabstract ct n)(END None) |= Ccore ** Atrue', ghost)
        self.assertIn('~ Rcritical Mc(TRabstract ct clock)(END None) |= Ccore ** Atrue', ghost)
        self.assertIn('load Tint32 Mc(150%positive,0%Z)=Some(Vint32 n)', ghost)
        self.assertNotIn('JsetPre', ghost)
        args = statement(src, 'Rset_two_argument_control')
        for token in ('LsetExec caller ks ct clock n Mn', 'LsetExec caller ks ct clock bad Mb',
                      'Rfinal caller Mn(TRabstract ct n)', 'Rfinal caller Mb(TRabstract ct bad)',
                      'get(TRabstract ct n)ostmid=Some(ostm n)',
                      'load Tint32 Mb(150%positive,0%Z)<>Some(Vint32 n)'):
            self.assertIn(token, args)
        getter = statement(src, 'Rget_return_control')
        for token in ('get Mf(160%positive,Z.of_nat k)=None',
                      'get Mf(161%positive,Z.of_nat k)=None',
                      'Rfinal caller Mf(TRabstract ct clock)', 'freels(getaddr JLE)Mc Mf'):
            self.assertIn(token, getter)
        self.assertIn('V293_freeb_removed', src)
        self.assertEqual(len(json.loads((D / 'protocol.json').read_text())['controls']), 4)

    def test_stable_compilation_and_recursive_trust(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        roots = []
        for key, p in (('body', PROD), ('probe', PROBE)):
            row = json.loads((D / (stable[key] + '.json')).read_text())
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(row['source_sha256'], hashlib.sha256((R / p).read_bytes()).hexdigest())
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem) (\w+)\s*:', (R / p).read_text(), re.M)]
        trust = json.loads((D / 'trust.json').read_text())
        self.assertTrue(trust['passed'])
        self.assertTrue(trust['recursive'])
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertEqual([r['exit'] for r in trust['commands']], [0, 0])
        old = json.loads((D.parent / 'stage180-time-api-lifecycle/trust.json').read_text())
        self.assertEqual(set(trust['allowed']), set(old['allowed']))
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
