"""结构回归；语义由实际 Coq 定理和内核检查承担，不声称语义 TDD。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

R = Path(__file__).resolve().parents[1]
D = R / 'audit/logs/stage216-ready-storage-invariant'
SOURCES = {'body': 'certiucos/v293/proofs/V293ReadyStorageInvariant.v',
           'probe': 'audit/probes/V293ReadyStorageInvariantProbe.v'}


def read(name):
    return json.loads((D / name).read_text())


def statement(src, name):
    return re.split(r'\b' + re.escape(name) + r'\s*:', src, maxsplit=1)[1].split('Proof.', 1)[0]


class ReadyStorageInvariantTests(unittest.TestCase):
    def test_frozen_sources_and_prospective_protocol(self):
        source = read('source-check.json')
        self.assertTrue(source['passed'])
        self.assertEqual([x['function']['name'] for x in source['functions']],
                         ['OSIntEnter', 'OSIntExit', 'OS_SchedNew', 'OS_Sched'])
        for row in source['functions']:
            self.assertTrue(row['reconstructed_repaired_source_matches'])
            self.assertEqual(hashlib.sha256((D / (row['function']['name'] + '.configured.c.txt')).read_bytes()).hexdigest(),
                             row['function']['preprocessed_definition_sha256'])
        for p, h in source['files'].items():
            self.assertEqual(hashlib.sha256((R / p).read_bytes()).hexdigest(), h)
        self.assertEqual(hashlib.sha256((D / 'protocol.json').read_bytes()).hexdigest(),
                         read('protocol-identity.json')['protocol.json'])
        old = R / 'audit/logs/stage215-dynamic-exit-snapshot/checkpoint-evidence-manifest.json'
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), source['previous_manifest_sha256'])

    def test_one_invariant_and_exact_resource_equivalence(self):
        src = (R / SOURCES['body']).read_text()
        self.assertIn('V293_ready_core br bg bp ** V293_ready_storage_extra', src)
        self.assertIn('V293_dispatch_cell target tp ** V293_storage cells', src)
        self.assertIn('V293_ready_storage_core_precise', src)
        self.assertIn('V293_ready_storage_core_aux', src)
        self.assertIn('GoodI V293_ready_storage_inv V293_scheduler V293_shared_li',
                      statement(src, 'V293_ready_storage_good'))
        equivalent = statement(src, 'V293_ready_storage_switch_resources')
        self.assertIn('<==>', equivalent)
        self.assertIn('SWINVt (V293_ready_inv br bg bp) t ** V293_ready_storage_extra', equivalent)
        self.assertNotIn('InfRules', equivalent)
        self.assertNotIn('CertiOS.audit.', src)

    def test_original_switch_and_selection_not_assumed(self):
        src = (R / SOURCES['body']).read_text()
        stmt = statement(src, 'V293_ready_storage_switch_step')
        self.assertIn('exists Mf,', stmt)
        self.assertIn('lpstep', stmt)
        self.assertIn('store(Tptr tp)M(bc,0%Z)(Vptr next)=Some Mf', stmt)
        self.assertIn('SWINVt V293_ready_storage_inv next ** R', stmt)
        self.assertIn('get Mf(c,i)=get M(c,i)', stmt)
        self.assertIn('V293_ready_switch_step br bg bp', src)
        stmt = statement(src, 'V293_ready_storage_selected')
        for token in ('V293_ready_rel lo hi entries tasks', 'V293_ready_loads(getmem s)',
                      'get tasks t=Some', 'load(Tptr V293_tcb_type)', 'V293_scheduler(getabst s)t'):
            self.assertIn(token, stmt)

    def test_nonempty_prefix_single_byte_ablation_and_cache_boundary(self):
        src = (R / SOURCES['probe']).read_text()
        self.assertIn('V293_local_steps CGprogram', statement(src, 'PPnonempty'))
        self.assertIn('CGlocal_ready true enabled ci', src)
        stmt = statement(src, 'PPactual_switch')
        self.assertIn('lpstep', stmt)
        self.assertIn('SWINVt PPinv OwnershipReady ** PPprivate', stmt)
        self.assertIn('~V293_cache_current', stmt)
        stmt = statement(src, 'PPbitmap_control')
        for token in ('SWINVt PPinv OwnershipWaiting ** PPprivate',
                      'store Tint8 Mgood(80%positive,0%Z)',
                      'get Mbad a=get Mgood a', 'V293_storage PPcells',
                      'V293_owned_task_records OwnershipTasks',
                      'forall t R,~CGstate OwnershipWaiting Mbad'):
            self.assertIn(token, stmt)
        self.assertIn('V293_owned_byte_update', src)
        self.assertIn('V293_put_byte_store with(old:=old)', src)

    def test_stable_compiles_and_recursive_kernel_check(self):
        roots = []
        for kind, p in SOURCES.items():
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
        self.assertTrue(all(c['exit'] == 0 for c in trust['commands']))
        self.assertLessEqual(set(trust['assumptions']), set(trust['allowed']))
