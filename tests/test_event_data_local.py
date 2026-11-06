"""Protocol checks; semantic claims require the actual Coq logs and kernel checks."""
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import unittest

ROOT=Path(__file__).resolve().parents[1]
LOG=ROOT/'audit/logs/stage26-event-data'


def driver():
    s=importlib.util.spec_from_file_location('event_data_gate',ROOT/'scripts/check-v293-event-data.py')
    m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


class EventDataTests(unittest.TestCase):
    def test_existing_prefix_other_sources_and_historical_evidence_exact(self):
        g=driver();b=json.loads((LOG/'baseline.json').read_text())
        self.assertEqual(len(b['active']),166)
        self.assertEqual(sha(ROOT/g.BEFORE),g.BEFORE_SHA)
        self.assertTrue((ROOT/g.SOURCE).read_bytes().startswith((ROOT/g.BEFORE).read_bytes()))
        for p,h in {**b['protected'],**b['historical'],**{p:h for p,h in b['active'].items() if p!=g.SOURCE}}.items():
            self.assertEqual(sha(ROOT/p),h,p)

    def test_exact_field_layout_and_full_typed_load_footprints(self):
        s=(ROOT/driver().SOURCE).read_text();s=s[len((ROOT/driver().BEFORE).read_text()):]
        for x in ['field_offset 2%Z V293_event_fields = Some (Int.repr 4)',
                  'field_offset 3%Z V293_event_fields = Some (Int.repr 8)',
                  'Int.unsigned count <= 65535','load Tint16 M (be,(base+8)%Z)',
                  'load (Tptr Tvoid) M (be,(base+4)%Z)','| _ => False',
                  'delta + Z.of_nat (typelen tp) <= 10','intros k K. apply Frame. left. lia.']:
            self.assertIn(x,s)
        self.assertNotIn('Axiom ',s);self.assertNotIn('Admitted',s)

    def test_general_adapter_same_entry_all_old_outputs_same_witness(self):
        g=driver();s=(ROOT/g.SOURCE).read_text();old=(ROOT/g.BEFORE).read_text()
        def header(source,name):
            a=source.index('Theorem '+name+' :');return source[a:source.index('Proof.',a)]
        original=g.TARGET.removesuffix('_data');a=header(old,original);b=header(s,g.TARGET)
        self.assertEqual(a.replace(original,g.TARGET,1).split('  exists ',1)[0],b.split('  exists ',1)[0])
        self.assertIn(a.split('  exists ',1)[1].rstrip()[:-1]+' /\\',b)
        proof=s[s.index('Proof.',s.index('Theorem '+g.TARGET+' :')):]
        self.assertEqual(proof.count(original+' P'),1)
        self.assertIn("exists Mf. exists Os'. exists OO'",proof)
        self.assertIn('apply V293_event_sem_mbox_data_frame. exact Header',proof)

    def test_literal_probe_builds_new_header_before_full_execution(self):
        p=(ROOT/driver().PROBE).read_text()
        for x in ['Definition expected_sem_mbox_data','Definition EventDataProbeMemory',
                  '72%positive 9%Z (encode_val (Tptr Tvoid) Vnull)',
                  '72%positive 13%Z (encode_val Tint16 (Vint32 Int.zero))',
                  'expected_event_data_contract V293_success_tail_fixture_program',
                  'apply DataPreserved. exact EventDataProbeData','EventDataReturnRejectsChangedCount',
                  'EventDataWideCountRejectsZero','EventDataMailboxRejectsNull',
                  'EventDataProbeExecution sc now op ir enabled si ci']:
            self.assertIn(x,p)
        self.assertEqual(p.count('Print Assumptions '),9)
        self.assertNotIn('EventReturnProbeExecution ',p)

    def test_prospective_single_content_factor_entire_proof_unchanged(self):
        g=driver();positive,negative=g.controls((ROOT/g.SOURCE).read_text())
        suffix=lambda s:s[s.index('Proof.',s.index('Theorem '+g.TARGET+' :')):]
        for name,s in negative.items():self.assertEqual(suffix(s),suffix(positive),name)
        self.assertIn('abssem (Int.add n Int.one)',negative['ChangedSemCount'])
        self.assertIn('absmbox _ => absmbox Vnull',negative['NullMailboxMessage'])

    def test_fresh_configured_identity_and_two_old_rejections_preserved(self):
        c=json.loads((LOG/'configured-source/result.json').read_text())
        self.assertEqual(c['function']['preprocessed_definition_sha256'],'c29b633e71cf54c2d244eb87c7a5910a1f2973e6cd23d7a23769070b24bc2dbf')
        d=lambda s:Counter(re.findall(r'^(?:FAIL|ERROR): .*$',s,re.M))
        old=d((ROOT/'audit/logs/stage26-event-return-frame/full-tests-post-docs.log').read_text())
        new=d((LOG/'full-tests-before-new-tests.log').read_text())
        self.assertFalse(old-new);self.assertEqual(sum((new-old).values()),2)
        self.assertIn('failures=303, errors=1',(LOG/'full-tests-before-new-tests.log').read_text())

    def test_seventeen_actual_checks_and_all_frozen_inputs(self):
        g=driver();r=json.loads((LOG/'gate02/result.json').read_text())
        self.assertTrue(r['passed']);self.assertTrue(r['inputs_unchanged']);self.assertTrue(r['temporary_tree_removed'])
        self.assertTrue(r['old_prefix_unchanged']);self.assertEqual(len(r['checks']),17)
        for p,h in r['inputs'].items():self.assertEqual(sha(ROOT/p),h,p)
        for name,row in r['checks'].items():
            self.assertEqual(row['exit_code'],1 if name.startswith('negative-') else 0,name)
            if name.startswith('negative-'):
                self.assertTrue(row['proof_suffix_unchanged']);self.assertFalse(row['downstream_credit'])
                self.assertGreater(row['error_line'],row['target_proof_line'])
        for name in ['Production-coqchk','Probe-coqchk','PositiveRoots-coqchk']:self.assertIn(name,r['checks'])

    def test_actual_assumptions_independent_prefix_and_literal_counterexamples(self):
        g=driver();r=json.loads((LOG/'gate02/result.json').read_text());checker=g.module('check-v293-task-prio-rekey.py')
        self.assertEqual(checker.checked_assumptions((LOG/'gate02/PositiveRoots.log').read_text(),4),r['positive_assumptions'])
        self.assertEqual(checker.checked_assumptions((LOG/'gate02/V293EventDataProbe.log').read_text(),9),r['probe_assumptions'])
        positive=(LOG/'gate02/PositiveRoots.v.snapshot.txt').read_text()
        prefix=(LOG/'gate02/FrozenPrefix.v.snapshot.txt').read_text()
        self.assertIn('Require Import EventDataGate.FrozenPrefix.',positive)
        self.assertNotIn('Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.',positive)
        self.assertNotIn('Theorem '+g.TARGET+' :',prefix)
        self.assertEqual((LOG/'gate02/Production.v.snapshot.txt').read_bytes(),(ROOT/g.SOURCE).read_bytes())


if __name__=='__main__':unittest.main()
