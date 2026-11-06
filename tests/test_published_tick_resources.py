"""发布来源与零延时资源；文本检查只约束证据，不能替代Coq。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage336-published-tick-resources'
P = 'certiucos/v293/proofs/V293PublishedTickResources.v'
Q = 'audit/probes/V293PublishedTickResourcesProbe.v'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda n: json.loads((D / n).read_text())


class PublishedTickResourcesTests(unittest.TestCase):
    def test_source_identity_and_real_writes(self):
        rows = read('source-identities.json')
        self.assertEqual({r['name'] for r in rows}, {'OS_TCBInit', 'OSTimeTick'})
        self.assertEqual(read('source-replay.json')['exit'], 0)
        inventory = json.loads((R / 'audit/repaired-source-inventory.json').read_text())
        for row in rows:
            self.assertIn(row, inventory['functions'])
            self.assertEqual(sha(D / (row['name'] + '.source.c.snapshot.txt')), row['source_lines_sha256'])
            data = (D / (row['name'] + '.configured.c.snapshot.txt')).read_bytes()
            self.assertEqual(hashlib.sha256(data[:-1]).hexdigest(), row['preprocessed_definition_sha256'])
        source = (D / 'OS_TCBInit.configured.c.snapshot.txt').read_text()
        for token in ['ptcb->OSTCBDly = 0u;', 'ptcb->OSTCBNext = OSTCBList;', 'OSTCBList = ptcb;',
                      'OSTCBInitHook(ptcb);', 'OSTaskCreateHook(ptcb);']:
            self.assertIn(token, source)

    def test_continuous_creation_keeps_hook_obligations(self):
        s = (R / P).read_text()
        stmt, proof = s.split('Theorem V293_TCBInit_returns_published_zero_under_hooks :', 1)[1].split('Proof.', 1)
        inputs, outputs = stmt.split(' exists Mf,', 1)
        self.assertEqual(inputs.count('V293_records_hook_return'), 2)
        self.assertIn('V293_tcb_init_old_fields bt base old', inputs)
        for token in ['load ', 'store ', 'evalval', 'V293_local_steps', 'cstepstar', 'TaskSim']:
            self.assertNotIn(token, inputs)
        for token in ['V293_OS_TCBInit_prefix_return_records_under_hooks',
                      'TasksAway CellsAway Hook1 Hook2 Entry', 'V293_published_tick_extract']:
            self.assertIn(token, proof)
        for token in ['V293_TCBInit_prefix', 'V293_TCBInit_success_suffix hi hc',
                      '((ge,caller,Mf),ir,(enabled,si,ci))', 'V293_published_tick_owned',
                      'V293_tcb_function_addresses', 'get Mf (b,Z.of_nat k)=None']:
            self.assertIn(token, outputs)
        self.assertNotIn('Require Import CertiOS.audit.', s)
        self.assertNotRegex(s, r'Require Import CertiOS\.(?:ucos|os_code|os_proof)\.')

    def test_joint_resources_and_actual_scan(self):
        s = (R / P).read_text()
        self.assertIn('firstn 1 (tl links)++skipn 3 links', s)
        own = s.split('Definition V293_published_tick_owned', 1)[1].split('Lemma ', 1)[0]
        for token in ['V293_tick_zero_node', 'V293_owned_task_records', 'V293_rdy_raw_cells spares',
                      'V293_published_link_spares links', 'V293_rdy_raw_cells tail Atrue']:
            self.assertIn(token, own)
        scan = s.split('Theorem V293_published_head_then_zero_iteration', 1)[1].split('(* The initialization', 1)[0]
        for token in ['V293_ready_tick_head_execution', 'V293_tick_zero_iteration_owned_execution',
                      'sseq(sassign(evar ptcb)(evar head))(V293_tick_iteration', 'exact HeadExec',
                      'exact TickExec', 'HeadOutside', 'TickOutside', 'get Mf(b,i)=get M(b,i)']:
            self.assertIn(token, scan)

    def test_concrete_creation_and_unconditional_scan(self):
        self.assertEqual(sha(R / 'audit/probes/V293InitPublishRecordsProbe.v'),
                         '5d192456b308bc665cb36f22d66cc06363f0765c2ad0ab46e70cbc246810ce3d')
        self.assertEqual(sha(R / 'audit/probes/V293TCBInitTickZeroProbe.v'),
                         '1c3192c50a72c1879e38fcf360fbee1ccb8684c45af082487b778566b12e9099')
        s = (R / Q).read_text()
        creation = s.split('Theorem PTcreation_under_hooks', 1)[1].split('Definition PTcells', 1)[0]
        self.assertIn('ChainSpatialEntry', creation)
        self.assertIn('V293_TCBInit_returns_published_zero_under_hooks', creation)
        self.assertIn('ChainHooks P f hi hc ks enabled si ci false ->', creation)
        self.assertIn('ChainHooks P f hi hc ks enabled si ci true ->', creation)
        scan = s.split('Theorem PTactual_head_then_tick :', 1)[1].split('Lemma PTdelay', 1)[0]
        self.assertTrue(scan.startswith(' forall P ks enabled,exists Mh Mf,'))
        self.assertNotIn(' ->', scan.split('Proof.', 1)[0].split('(forall b i,', 1)[0])
        self.assertIn('PTvalid Int.zero', scan)
        self.assertIn('V293_published_head_then_zero_iteration', scan)

    def test_prospective_single_factor_contract_ablation(self):
        self.assertEqual(sha(D / 'protocol.json'), '9633d1ad8be013c979f19093a704ccff506959dd2a9f192ddb9b908905cf4b94')
        self.assertEqual((D / 'protocol.sha256').read_text().split(), [sha(D / 'protocol.json'), 'protocol.json'])
        protocol = read('protocol.json')
        self.assertTrue(protocol['prospective'])
        self.assertEqual(protocol['ablation']['factor'], 'remove only runtime-zero preservation across the hook boundary')
        self.assertIn('not an executed mutant hook', protocol['ablation']['scope'])
        s = (R / Q).read_text()
        cells = s.split('Definition PTcells d:', 1)[1].split('Definition PTmemory', 1)[0]
        self.assertIn('::TZcells d', cells)
        self.assertEqual(cells.count(' d'), 1)
        for token in ['Theorem PThook_zero_resource_necessary', 'PTowned(Int.repr 3)',
                      'rewrite PTdelay in Zero;discriminate', 'Theorem PTzero_gate_passes',
                      'Theorem PTsingle_factor_outside', 'apply TZsingle_factor_outside;exact Outside',
                      'get(PTmemory d1)(b,i)=get(PTmemory d2)(b,i)']:
            self.assertIn(token, s)

    def test_recursive_check_and_repeat_compilation(self):
        roots = []
        for p in [P, Q]:
            s = (R / p).read_text()
            self.assertNotRegex(s, r'\b(?:Admitted|admit|Axiom|Parameter|Conjecture|Abort|Show|idtac)\b')
            roots += [Path(p).stem + '.' + n for n in re.findall(r'^(?:Lemma|Theorem|Corollary) (\w+)\s*:', s, re.M)]
            self.assertEqual(read('trust-inputs.json')[p], sha(R / p))
        trust = read('trust.json')
        self.assertEqual(len(roots), 11)
        self.assertEqual(trust['roots'], roots)
        self.assertEqual(trust['roots_printed'], 11)
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

    def test_history_and_bounded_claims(self):
        mutable = {'README.md', 'VERIFICATION_STATUS.md', '_CoqProject', '.Makefile.coq.d'}
        self.assertEqual([p for p, h in read('baseline.json')['files'].items()
                          if p not in mutable and (not (R / p).is_file() or sha(R / p) != h)], [])
        for n in ['README.md', 'VERIFICATION_STATUS.md']:
            self.assertTrue((R / n).read_bytes().endswith((D / (n + '.baseline')).read_bytes()))
        prefix = (D / '_CoqProject.baseline').read_bytes() + (P + '\n').encode()
        current = (R / '_CoqProject').read_bytes()
        self.assertTrue(current.startswith(prefix))
        self.assertTrue(all(line.startswith('certiucos/v293/') and line.endswith('.v')
                            for line in current[len(prefix):].decode().splitlines()))
        doc = (R / 'audit/STAGE336_PUBLISHED_TICK_RESOURCES.md').read_text()
        for token in ['GOOD_OS', 'K1–K4', 'uCOS3', '总目标保持active', '手工源码模型',
                      '不是合法ISR', '不是无条件完整OS_TCBInit', '不是完整OSTimeTick',
                      '两个CPU hook契约仍开放', '不是执行突变hook']:
            self.assertIn(token, doc)
