"""启动到真实 CurTid 的结构约束；语义证明及对照由 Coq 检查。"""
from pathlib import Path
import hashlib
import json
import re
import unittest

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / 'audit/logs/stage77-start-current'
PROOF = ROOT / 'certiucos/v293/proofs/V293StartCurrent.v'
PROBE = ROOT / 'audit/probes/V293StartCurrentProbe.v'


class StartCurrentTests(unittest.TestCase):
    def test_production_reserved_binding_and_no_new_axioms(self):
        source = PROOF.read_text()
        self.assertIn(str(PROOF.relative_to(ROOT)), (ROOT / '_CoqProject').read_text().splitlines())
        self.assertNotRegex(re.sub(r'\(\*.*?\*\)', '', source, flags=re.S),
                            r'\b(Axiom|Parameter|Admitted|admit|Conjecture)\b')
        self.assertNotIn('CertiOS.audit', source)
        self.assertIn('GV_separate_rw_frm', source)
        self.assertIn('V293_rdy_cell_out', source)
        self.assertIn('get ge OSTCBCur=Some (bu,Tptr V293_tcb_type)', source)

    def test_actual_call_not_preexisting_current_task_or_port_oracle(self):
        source = PROOF.read_text()
        for name in ['V293_OSStart_call_establishes_current', 'V293_OSStart_highest_establishes_current']:
            signature = source.split('Theorem ' + name + ' : ', 1)[1].split('Proof.', 1)[0]
            entry, post = signature.split('exists ', 1)
            self.assertNotIn('CurTid', entry)
            self.assertNotIn('CurLINV', entry)
            self.assertIn('sfexec port nil nil', post)
            self.assertNotRegex(signature, r'P\s+port\s*=')
            self.assertIn('CurTid target ** CurTid target', post)
        self.assertIn('V293_OSStart_highest_ready_call_to_port', source)

    def test_literal_entry_and_same_memory_observations(self):
        source = PROBE.read_text()
        for name in ['CurrentLiteralEntry', 'CurrentNoInitialTask', 'CurrentColdCall',
                     'CurrentHighestCall', 'CurrentPostReads', 'CurrentSameMf']:
            self.assertIn('Theorem ' + name, source)
        self.assertIn('Theorem CurrentPortMissing : CurrentProgram 902%Z=None.', source)
        self.assertIn('Some Vnull', source)
        self.assertIn('load Tint8 Mf (85%positive,0%Z)=Some(Vint32 Int.zero)', source)
        result = json.loads((LOG / 'probe06.json').read_text())
        self.assertEqual(result['exit'], 0)
        self.assertEqual(hashlib.sha256(PROBE.read_bytes()).hexdigest(), result['source_sha256'])

    def test_binding_ablation_is_not_early_call_rejection(self):
        plan = json.loads((LOG / 'binding-control-plan.json').read_text())
        self.assertTrue(plan['frozen_before_probe_compilation'])
        self.assertIn('actual completed call to port', plan['same_in_both'])
        self.assertIn('StartProgram', plan['same_in_both'][0])
        source = PROBE.read_text()
        self.assertIn('Theorem CurrentAliasCall', source)
        self.assertIn('Theorem CurrentDecoyCall', source)
        self.assertIn('Theorem CurrentBindingOnlyFactor', source)
        self.assertIn('forall t, ~ StartState Mf |= CurTid t ** Atrue', source)

    def test_postcondition_control_changes_only_one_target(self):
        plan = json.loads((LOG / 'post-control-plan.json').read_text())
        self.assertTrue(plan['frozen_before_compilation'])
        p = (LOG / 'Positive.v.snapshot.txt').read_text()
        w = (LOG / 'WrongCurrent.v.snapshot.txt').read_text()
        self.assertEqual(p.count(plan['old']), 1)
        self.assertEqual(p.replace(plan['old'], plan['new'], 1), w)
        for name, source, expected in [('Positive', p, 0), ('WrongCurrent', w, 1)]:
            row = json.loads((LOG / (name + '.json')).read_text())
            self.assertEqual(row['exit'], expected)
            self.assertEqual(row['source_sha256'], hashlib.sha256(source.encode()).hexdigest())
        output = (LOG / 'WrongCurrent.log').read_text()
        self.assertIn('CurrentColdCall', output)
        self.assertIn('expected to have type', output)
