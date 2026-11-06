"""地址新鲜性的结构回归；语义和 GoodI 反例由 Coq 检查。"""
from pathlib import Path
import hashlib
import json
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage131-tcb-site-freshness'
SOURCE = 'certiucos/v293/proofs/V293TCBSiteFreshness.v'
PROBE = 'audit/probes/V293TCBSiteFreshnessProbe.v'


class TCBSiteFreshnessTests(unittest.TestCase):
    def setUp(self):
        self.source = (R / SOURCE).read_text()
        self.probe = (R / PROBE).read_text()

    def section(self, name, probe=False):
        return (self.probe if probe else self.source).split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_hole_free_and_registered_once(self):
        for text in [self.source, self.probe]:
            self.assertNotRegex(text, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.', self.source)
        self.assertEqual((R / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

    def test_allocator_membership_is_used_before_original_suffix(self):
        body = self.section('V293_OS_TCBInit_site_fresh_body')
        for text in ['V293_OS_TCBInit_site_free_body_with_success',
                     'intros b off next NodeMember NodeBound NextTyped',
                     'V293_tcb_allocated_fields', 'V293_tcb_site_reserved_distinct',
                     'exact Outside', 'exact NodeMember',
                     'V293_OS_TCBInit_owned_suffix_after_first_hook']:
            self.assertIn(text, body)
        self.assertLess(body.index('V293_tcb_site_reserved_distinct'),
                        body.index('V293_OS_TCBInit_owned_suffix_after_first_hook'))
        self.assertIn('apply astar_l_apure_intro;[exact H|', body)

    def test_static_guard_replaces_universal_state_oracle(self):
        for name in ['V293_OS_TCBInit_site_fresh_body', 'V293_OS_TCBInit_site_fresh_joint_body',
                     'V293_OS_TCBInit_site_fresh_internal_resources',
                     'V293_OS_TCBInit_site_fresh_internal_contract']:
            body = self.section(name)
            sig = body.split('Proof.', 1)[0]
            self.assertIn('~In reserved(V293_tcb_table_sites tcbtable)', sig)
            self.assertNotIn('forall b off next s', sig)
            self.assertNotIn('Fresh', body)

    def test_same_joint_inv_and_six_borrow_return_sites(self):
        body = self.section('V293_OS_TCBInit_site_fresh_joint_body')
        self.assertIn('V293_create_joint_inv tcbtable bf table bh bg br bn nesting reserved', body)
        for name in ['free', 'priority', 'publication']:
            self.assertEqual(body.count('V293_create_joint_borrow_' + name), 2)
        self.assertIn('GoodI(V293_create_joint_inv',
                      self.section('V293_OS_TCBInit_site_fresh_internal_contract'))

    def test_exact_builders_and_existing_specs_retained(self):
        body = self.section('V293_OS_TCBInit_site_fresh_internal_contract')
        for text in ['BuildPreI', 'BuildRetI', 'V293_tcb_shared_fpre', 'V293_tcb_shared_fpost',
                     'P f=Some(V293_TCBInit_function hi hc)', 'V293_tcb_internal_buildp',
                     'V293_OS_TCBInit_site_fresh_internal_resources']:
            self.assertIn(text, body)
        self.assertNotIn('Definition V293_tcb_shared_fpre', self.source)
        self.assertNotIn('Definition V293_tcb_shared_fpost', self.source)

    def test_independent_address_controls(self):
        for name in ['SFReservedAccepted', 'SFReservedOutside', 'SFAllThirteenDistinct',
                     'SFAliasRejected', 'SFAliasMember', 'SFAliasHasNoOutside',
                     'SFSameBlockAccepted', 'SFSameBlockOutside']:
            body = self.section(name, True)
            self.assertNotIn('V293_tcb_site_reserved_distinct', body)
            self.assertNotIn('V293_tcb_site_reserved_other_block', body)
        self.assertIn('SFGuard(82%positive,Int.zero)=false', self.section('SFAliasRejected', True))
        self.assertIn('SFGuard(82%positive,Int.one)=true', self.section('SFSameBlockAccepted', True))

    def test_godi_obstruction_uses_real_initialization_and_extension(self):
        body = self.section('SFPhysicalInvNotGoodI', True)
        for text in ['forall sd li,~GoodI SFPhysicalInv sd li', 'CPActualInitialization',
                     'V293_create_joint_noisr_core', 'map_join_pos',
                     'sig curtid(oscurt FPTid)', 'NoExtension', 'map_get_sig']:
            self.assertIn(text, body)
        finding = json.loads((D / 'goodi-review-finding.json').read_text())
        self.assertEqual(finding['kind'], 'adversarial finding, not a prospective ablation')
        self.assertFalse(finding['old_evidence_rewritten'])

    def test_stable_compiles_and_honest_limits(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('proof', SOURCE), ('probe', PROBE)]:
            label = stable[kind]
            row = json.loads((D / (label + '.json')).read_text())
            data = (R / path).read_bytes()
            self.assertEqual(row['exit'], 0)
            self.assertEqual(row['source_sha256'], hashlib.sha256(data).hexdigest())
            self.assertEqual(row['initial_source_sha256'], row['source_sha256'])
            self.assertEqual(data, (D / (label + '.v.snapshot.txt')).read_bytes())
        doc = (R / 'audit/STAGE131_TCB_SITE_FRESHNESS.md').read_text()
        for text in ['无法满足 GoodI', '不是生产全局Inv', '单因素', '联合可满足',
                     'WFIFun', 'GOOD_OS', 'uCOS3', '423', '后验']:
            self.assertIn(text, doc)


if __name__ == '__main__':
    unittest.main()
