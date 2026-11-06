"""结构回归不能取代 Coq；不把受限路径提升为整函数环境。"""
from pathlib import Path
import hashlib
import json
import re
import unittest
R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage205-interrupt-exit-nondispatch'
PROD = 'certiucos/v293/proofs/V293OSIntExitNondispatch.v'
PROBE = 'audit/probes/V293OSIntExitNondispatchProbe.v'
def read(n):
    return json.loads((D / n).read_text())
def statement(src, name):
    return src.split(name + ' :', 1)[1].split('Proof.', 1)[0]
class InterruptExitNondispatchTests(unittest.TestCase):
    def test_source_identity_and_prospective_protocol(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        self.assertEqual([x['function']['name'] for x in source['functions']],
                         ['OSIntEnter', 'OSIntExit', 'OS_SchedNew'])
        for x in source['functions']:
            self.assertTrue(x['reconstructed_repaired_source_matches'])
            self.assertTrue(x['temporary_source_removed_on_context_exit'])
            self.assertEqual(hashlib.sha256((D / (x['function']['name'] + '.configured.c.txt')).read_bytes()).hexdigest(),
                             x['function']['preprocessed_definition_sha256'])
        for p, h in source['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
            self.assertEqual(h, read('baseline.json')['files'][p])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])
        old = R / 'audit/logs/stage204-interrupt-exit-environment/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_full_body_without_hidden_middle_or_dispatch_proof(self):
        src = (R / PROD).read_text()
        stmt = statement(src, 'V293_OSIntExit_nondispatch_body')
        self.assertEqual(stmt.count('InfRules'), 1)
        for token in ('(run=1 -> 2<=nest \\/ 0<locked)', '[|result=None|]',
                      'OS[ir,enabled,si,ci]', 'V293_exit_quiet_depth run nest',
                      'V293_exit_boundary_body', '(Vint32 Int.zero)'):
            self.assertIn(token, stmt)
        for token in ('V293_time_zero', 'V293_tick_known_ift_hoare', 'apply ret_rule',
                      'V293_OSIntExit_quiet_critical'):
            self.assertIn(token, src)
        self.assertNotIn('BuildPreI', stmt)
        self.assertNotIn('WFFunEnv', stmt)
        self.assertNotIn('CertiOS.audit.', src)

    def test_critical_resources_not_goodfrm_or_assumed_body(self):
        src = (R / PROD).read_text()
        stmt = statement(src, 'V293_OSIntExit_quiet_critical')
        self.assertEqual(stmt.count('InfRules'), 1)
        self.assertIn('GoodFrm R', stmt)
        self.assertNotIn('GoodFrm (OS', src)
        self.assertIn('apply V293_time_critical', src)
        self.assertIn('intro extra', src)
        self.assertIn('apply V293_OSIntExit_disabled_hoare', src)
        self.assertIn('V293_star_env_l', src)
        self.assertIn('V293_star_CurLINV_l', src)

    def test_nonempty_pre_and_tail_only_ablation(self):
        src = (R / PROBE).read_text()
        for name in ('QNdata_owned', 'QNpre_nonempty', 'QNbody', 'QNdepth_cases',
                     'QNtail_exit', 'QNtail_without_exit', 'QNtail_both_ie'):
            self.assertRegex(src, r'(?:Lemma|Theorem) ' + name + ' :')
        stmt = statement(src, 'QNpre_nonempty')
        self.assertIn('forall enabled si ci run nest old', stmt)
        self.assertIn('OS[(fun _=>false),enabled,si,ci]', stmt)
        self.assertIn('RCbig_owned', src)
        self.assertIn('apply excrit_step', src)
        self.assertIn('enabled::ci=ci', src)
        self.assertIn('~((ge,le,M,ir,(false,si,enabled::ci),O,aop)', src)
        self.assertNotIn('cstepstar', src)
        self.assertNotIn('loststep', statement(src, 'QNbody'))

    def test_stable_compiles_recursive_trust_and_no_new_holes(self):
        roots = []
        for kind, p in (('body', PROD), ('probe', PROBE)):
            src = (R / p).read_text()
            label = read('stable-compiles.json')[kind]
            row = read(label + '.json')
            h = hashlib.sha256((R / p).read_bytes()).hexdigest()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(h, row['initial_source_sha256'])
            self.assertEqual(h, row['source_sha256'])
            self.assertEqual(h, hashlib.sha256((D / (label + '.v.snapshot.txt')).read_bytes()).hexdigest())
            self.assertNotRegex(src, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', src, re.M)]
        trust = read('trust.json')
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertEqual(list(read('assumptions-by-root.json')), roots)
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
        self.assertTrue(all(x['exit'] == 0 for x in trust['commands']))
