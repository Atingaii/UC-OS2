"""初始化同内存空闲池接口的结构回归；语义依赖 Coq/coqchk 而非字符串。"""
from pathlib import Path
import hashlib
import json
import unittest

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293InitTCBFinitePool.v'
PROBE = 'audit/probes/V293InitTCBFinitePoolProbe.v'
D = ROOT / 'audit/logs/stage126-init-tcb-finite-pool'


class InitTCBFinitePoolTests(unittest.TestCase):
    def setUp(self):
        self.source = (ROOT / SOURCE).read_text()
        self.probe = (ROOT / PROBE).read_text()

    def section(self, name, probe=False):
        return (self.probe if probe else self.source).split(name + ' :', 1)[1].split('Qed.', 1)[0]

    def test_no_holes_or_audit_import(self):
        for content in [self.source, self.probe]:
            self.assertNotRegex(content, r'\b(?:Axiom|Parameter|Conjecture|Admitted|admit|Abort|Show)\b')
        self.assertNotIn('CertiOS.audit.', self.source)
        self.assertNotIn('CertiOS.audit.', self.probe)
        self.assertEqual((ROOT / '_CoqProject').read_text().splitlines().count(SOURCE), 1)

    def test_zero_bytes_fold_actual_full_payload(self):
        zero = self.section('V293_init_zero_typed_owned')
        self.assertIn('V293_zero_bytes_memory', zero)
        payload = self.section('V293_tcb_init_zero_payload')
        for item in ['repeat(Vint32 Int.zero)20', 'repeat(Vint32 Int.zero)32',
                     'V293_tcb_free_payload b base ** R', 'V293_init_zero_run_fold']:
            self.assertIn(item, payload)
        self.assertIn('V293_storage(map(fun c=>fst c)cells)', self.section('V293_init_raw_storage'))

    def test_fixed_pool_derives_membership(self):
        fold = self.section('V293_tcb_init_linked_pool')
        signature = fold.split('Proof.')[0]
        self.assertNotIn('In(', signature)
        for item in ['V293_tcb_linked_next bt', 'V293_tcb_untouched_cells bt 0 13',
                     'V293_tcb_site_free_pool bt bf ** R', 'apply in_map_iff', 'exists i.', 'apply in_seq']:
            self.assertIn(item, fold)

    def test_real_original_call_same_returned_memory(self):
        whole = self.section('V293_OS_InitTCBList_call_finite_pool')
        pre, post = whole.split('exists Mf,', 1)
        pre = pre.split('Proof.')[0]
        self.assertNotIn('V293_tcb_site_free_pool', pre)
        self.assertNotIn('cstepstar', pre)
        self.assertIn('(curs (scall f nil),(kenil,ks)) (ge,caller,M)', post)
        self.assertIn('(ge,caller,Mf,ir,aux,O,op) |=', post)
        self.assertIn('V293_OS_InitTCBList_call_return', whole)
        self.assertIn('apply V293_tcb_call_result_pool;exact Returned', whole)
        self.assertIn('exact Freed', whole)
        for item in ['fresh M bi', 'fresh M bn', 'fresh M b1', 'fresh M b2', 'Away Owned']:
            self.assertIn(item, whole)

    def test_rest_retains_heads_priorities_and_frame(self):
        rest = self.source.split('Definition V293_init_tcb_pool_rest', 1)[1].split('Lemma ', 1)[0]
        self.assertIn('Amapsto(bl,0)(Tptr V293_tcb_type)true Vnull', rest)
        self.assertIn('V293_null_pointer_cells bp 0 13++frame', rest)
        result = self.section('V293_tcb_call_result_pool')
        self.assertIn('V293_raw_cells_append', result)
        self.assertIn('V293_tcb_init_linked_pool', result)

    def test_independent_nonempty_actual_entry_and_direct_interface(self):
        self.assertIn('V293_encoded_memory 82%positive 0 true (repeat Undef 728)', self.probe)
        self.assertIn('V293_encoded_memory 84%positive 0 true', self.probe)
        entry = self.section('IPLiteralEntry', probe=True)
        self.assertIn('V293_encoded_memory_join', self.probe)
        self.assertNotIn('V293_tcb_call_result_pool', entry)
        stable = self.section('IPStableInterfaceChecked', probe=True)
        self.assertIn('V293_OS_InitTCBList_call_finite_pool', stable)
        self.assertIn('IPAway IPLiteralEntry', stable)
        actual = self.section('IPActualCallFinitePool', probe=True)
        self.assertIn('IPConcreteExecution ks', actual)
        self.assertIn('exact Raw', actual)
        self.assertIn('load(Tcom_ptr 410)Mf(82%positive,692)', actual)

    def test_physical_single_factor_reachability_ablation(self):
        reach = self.section('IPActualThirteenReachable', probe=True)
        for item in ['IPWalk 12 M', 'IPWalk 13 M', 'Int.repr 672', 'Some Vnull']:
            self.assertIn(item, reach)
        ablation = self.section('IPFirstNextNullAblation', probe=True)
        for item in ['store(Tcom_ptr 410)M(82%positive,20)Vnull=Some Bad',
                     'get Bad(b,j)=get M(b,j)', '24<=j', 'V293_storebytes_outside',
                     'load(Tcom_ptr 410)Bad(82%positive,76)', 'IPWalk 12 Bad',
                     'IPWalk 1 M', 'IPWalk 1 Bad', 'V293_tick_raw_slot_update']:
            self.assertIn(item, ablation)
        self.assertNotIn('~(IPState Bad |= V293_tcb_site_free_pool', ablation)

    def test_stable_evidence_and_bounded_scope(self):
        stable = json.loads((D / 'stable-compiles.json').read_text())
        for kind, path in [('proof', SOURCE), ('probe', PROBE)]:
            label = stable[kind]
            record = json.loads((D / (label + '.json')).read_text())
            data = (ROOT / path).read_bytes()
            self.assertEqual(record['exit'], 0)
            self.assertEqual(record['initial_source_sha256'], record['source_sha256'])
            self.assertEqual(hashlib.sha256(data).hexdigest(), record['source_sha256'])
            self.assertEqual(data, (D / (label + '.v.snapshot.txt')).read_bytes())
        self.assertLessEqual((D / 'protocol.json').stat().st_mtime_ns,
                             (D / 'proof01.v.snapshot.txt').stat().st_mtime_ns)
        doc = (ROOT / 'audit/STAGE126_INIT_TCB_FINITE_POOL.md').read_text()
        for item in ['不是生产全局Inv', 'token freshness', 'WFIFun', 'GOOD_OS', 'uCOS3', '上界', '同一份']:
            self.assertIn(item, doc)
        rows = json.loads((ROOT / 'audit/coverage.json').read_text())['rows']
        self.assertEqual([sum(bool(row[k]) for row in rows) for k in
                          ['located', 'modeled', 'specified', 'local_hoare', 'component_linked', 'full_target_linked']],
                         [94, 1, 1, 1, 1, 0])


if __name__ == '__main__':
    unittest.main()
