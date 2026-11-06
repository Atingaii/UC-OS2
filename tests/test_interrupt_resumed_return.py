"""挂起返回连接的结构回归；执行语义由独立 Coq 正控/消融核验。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage201-interrupt-resumed-return'
PROD = 'certiucos/v293/proofs/V293OSIntExitResumedReturn.v'
PROBE = 'audit/probes/V293OSIntExitResumedReturnProbe.v'


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return src.split(name + ' :', 1)[1].split('Proof.', 1)[0]


class InterruptResumedReturnTests(unittest.TestCase):
    def test_exact_source_and_frozen_protocol(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        self.assertEqual([x['function']['name'] for x in source['functions']], ['OSIntExit', 'OS_SchedNew'])
        for x in source['functions']:
            self.assertTrue(x['reconstructed_repaired_source_matches'])
            self.assertTrue(x['temporary_source_removed_on_context_exit'])
            p = D / (x['function']['name'] + '.configured.c.txt')
            self.assertEqual(hashlib.sha256(p.read_bytes()).hexdigest(), x['function']['preprocessed_definition_sha256'])
        for p, h in source['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
            self.assertEqual(h, read('baseline.json')['files'][p])
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(), read('protocol-identity.json')['protocol.json'])
        old = R / 'audit/logs/stage200-interrupt-switch-boundary/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_continuous_call_switch_return_without_execution_oracle(self):
        src = (R / PROD).read_text()
        stmt = statement(src, 'V293_OSIntExit_call_switch_resume')
        pre = stmt.split('exists bs next nh Msw Mret,', 1)[0]
        for token in ('cstepstar', 'V293_global_steps', 'V293_local_steps', 'store ', 'free ',
                      'evalval', 'fresh M', 'InOS'):
            self.assertNotIn(token, pre)
        for token in ('po f=Some', 'get T ct=Some(curs(scall f nil)',
                      'get T next=Some(SKIP', 'get les next=Some(V293_cpu_lenv saved nb)',
                      'get aus next=Some(na,nsi,ne::nci)', 'nb<>bc ->nb<>bcur ->nb<>bcount',
                      'V293_highest_ready tasks next', '(T,(ge,les,M,ir,aus),ct)',
                      'next(SKIP,(kenil,ntail))', 'next(ne,nsi,nci)',
                      'free Tint32 nb Msw=Some Mret', 'get Mret(nb,i)=None',
                      'get Mret(bs,Z.of_nat k)=Some(true,v)', 'Some(false,si,enabled::ci)'):
            self.assertIn(token, stmt)
        for token in ('V293_OSIntExit_boundary_switch true', 'V293_int_exit_pending_return',
                      'V293_cpu_release', 'V293_sched_global_return', 'V293_global_trans',
                      'V293_saved_cell_context', 'Fresh(nb,0%Z)0%Z eq_refl'):
            self.assertIn(token, src)
        self.assertNotIn('CertiOS.audit.', src)

    def test_independent_allocated_fixture_and_both_ie_controls(self):
        src = (R / PROBE).read_text()
        for token in ('Lemma RXfresh : fresh(SXmemory 1 6)RXblock', 'RXblock := 7000%positive',
                      'V293_cpu_initialized_frame', '(BXindependent_entry ci)',
                      'V293_OSIntExit_call_switch_resume', '(RXframe_entry ci M Store)',
                      'BXdomain(RXpending tail)', 'Lemma RXpending_bindings :',
                      'Some(Vptr OwnershipReady)', 'Some(V293_byteval 4)', 'Some(Vint32(Int.repr 20))',
                      'Some(false,nil,enabled::ci)', 'get Mret(bs,Z.of_nat k)=Some(true,v)'):
            self.assertIn(token, src)
        stmt = statement(src, 'RXboth_initial_IE')
        self.assertIn('exists M,', stmt)
        self.assertIn('free Tint32 RXblock M=Some(SXmemory 1 6)', stmt)
        self.assertIn('RXreturned M false ci ne nci tail cst /\\ RXreturned M true ci ne nci tail cst', stmt)
        stmt = statement(src, 'RXboth_target_IE')
        self.assertIn('RXreturned M enabled ci false nci tail cst /\\ RXreturned M enabled ci true nci tail cst', stmt)

    def test_single_factor_saved_bit_and_separate_explicit_exint(self):
        src = (R / PROBE).read_text()
        stmt = statement(src, 'RXstack_top_ablation')
        self.assertEqual(stmt.count('V293_global_steps(BXglobal true)cst'), 2)
        self.assertEqual(stmt.count('(RXtasks tail,(BXge,RXenvs,M,(fun _=>false),'), 2)
        for token in ('free Tint32 RXblock M=Some Mf', 'Mf=SXmemory 1 6',
                      'OwnershipReady(false,nil,negb enabled::ci)',
                      'OwnershipReady(enabled,nil,negb enabled::ci)', 'OwnershipReady(negb enabled,nil,ci)'):
            self.assertIn(token, stmt)
        self.assertNotIn('exint', stmt)
        stmt = statement(src, 'RXexplicit_exint')
        for token in ('forall enabled cst', 'Mf=SXmemory 1 6', 'RXtasks RXint_tail',
                      'OwnershipReady(true,nil,nil)', 'set emp 909%Z(701%positive,Tint8)',
                      'get Mf(RXblock,j)=None'):
            self.assertIn(token, stmt)
        prod = (R / PROD).read_text()
        self.assertIn('eapply exint_step;reflexivity', prod)
        self.assertIn('Lemma V293_bare_kint_no_local_step :', prod)
        self.assertIn('~loststep P(SKIP,(kenil,kint interrupted ike interrupted_le tail))', prod)
        self.assertIn('eapply V293_bare_kint_no_local_step;exact Step', src)
        # GoodInvAsrt permits ISR-stack dependence; no arbitrary R preservation across pop.
        self.assertNotIn('(ge,interrupted_le,Mf,ir,(true,si,ci),O,op)|=R',
                         statement(prod, 'V293_int_exit_pending_exint'))

    def test_stable_compiles_dynamic_roots_and_no_new_holes(self):
        stable = read('stable-compiles.json')
        roots = []
        for kind, p in (('body', PROD), ('probe', PROBE)):
            src = (R / p).read_text()
            row = read(stable[kind] + '.json')
            h = hashlib.sha256((R / p).read_bytes()).hexdigest()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(h, row['initial_source_sha256'])
            self.assertEqual(h, row['source_sha256'])
            self.assertEqual(h, hashlib.sha256((D / (stable[kind] + '.v.snapshot.txt')).read_bytes()).hexdigest())
            self.assertNotRegex(src, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', src, re.M)]
        trust = read('trust.json')
        self.assertTrue(trust['passed'] and trust['recursive'])
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], len(roots))
        self.assertEqual(list(read('assumptions-by-root.json')), roots)
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
        self.assertTrue(all(x['exit'] == 0 for x in trust['commands']))
