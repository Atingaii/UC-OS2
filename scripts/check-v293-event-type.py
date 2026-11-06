#!/usr/bin/env python3
"""Check ECB header preservation across the real nonnull event substatement only."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293CriticalReturn.v'
PROBE = 'audit/probes/V293EventTypeProbe.v'
PREFIX_BYTES = 394826
PREFIX_SHA = '6efff6628f97496864f7874e32a53d58b4b56615d6465738463827c9c1873eae'
TARGET = 'V293_event_nonnull_type_execution'
ROOTS = ['V293_event_type_field_layout', 'V293_event_type_matches_frame',
         'V293_event_rekey_byte_frame', TARGET, 'V293_event_rekey_changes_wait_byte']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT/'scripts'/name)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def parts(source):
    raw = source.encode()
    prefix = raw[:PREFIX_BYTES]
    assert hashlib.sha256(prefix).hexdigest() == PREFIX_SHA
    suffix = raw[PREFIX_BYTES:].decode()
    imports = '\n'.join(dict.fromkeys(l for l in prefix.decode().splitlines()
                                     if l.startswith('Require Import ')))
    harness = ('Require Import EventTypeGate.FrozenPrefix.\n'+imports+
               '\nImport ListNotations.\nLocal Open Scope nat_scope.\nLocal Opaque HalfPermMap.set.\n')
    return prefix.decode(), suffix, harness


def control(source):
    _, suffix, harness = parts(source)
    original = harness+suffix
    start = original.index('Theorem '+TARGET+' :')
    proof_start = original.index('Proof.', start)
    header, proof = original[:proof_start], original[proof_start:]
    old = '  V293_event_type_matches Mf be base data.'
    new = '  V293_event_type_matches Mf be base (absmbox Vnull).'
    assert header.count(old) == 1
    changed = header.replace(old, new)+proof
    assert changed[changed.index('Proof.', changed.index('Theorem '+TARGET+' :')):] == proof
    return changed, original


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output-dir', type=Path, required=True)
    out = p.parse_args().output_dir.resolve()
    out.mkdir(parents=True, exist_ok=False)
    source = (ROOT/SOURCE).read_text()
    prefix, suffix, harness = parts(source)
    negative, positive = control(source)
    prints = '\n'+''.join('Print Assumptions '+n+'.\n' for n in ROOTS)
    inputs = {str(p.relative_to(ROOT)): sha(p) for d in ['framework','tactics','certiucos/v293']
              for p in (ROOT/d).rglob('*.v')}
    probes = ['audit/probes/V293SuccessCompleteReturnProbe.v',
              'audit/probes/V293SuccessEntryWitnessProbe.v',
              'audit/probes/V293ReadyGeneralEntryProbe.v',
              'audit/probes/V293WaitEventOwnedProbe.v',
              'audit/probes/V293WaitPayloadProbe.v',
              'audit/probes/V293EventQueueProbe.v', PROBE]
    for path in [*probes, '_CoqProject','scripts/check-v293-event-type.py',
                 'scripts/check-v293-critical-elaboration.py','scripts/check-v293-task-prio-rekey.py',
                 'csrc/repairs/FROZEN_SOURCE.json','audit/coverage.json']:
        inputs[path] = sha(ROOT/path)
    tree = Path(tempfile.mkdtemp(prefix='v293-event-type-gate-'))
    files = {'FrozenPrefix': prefix, 'PositiveRoots': positive+prints, 'HeaderChanged': negative}
    for n,s in files.items():
        (tree/(n+'.v')).write_text(s)
        (out/(n+'.v.snapshot.txt')).write_text(s)
    (out/'Production.v.snapshot.txt').write_text(source)
    (out/'Probe.v.snapshot.txt').write_bytes((ROOT/PROBE).read_bytes())
    proof_line = negative[:negative.index('Proof.', negative.index('Theorem '+TARGET+' :'))].count('\n')+1
    protocol = {'label':'HeaderChanged','factor':'only final physical kind binding becomes mailbox',
                'negative_sha256':sha(tree/'HeaderChanged.v'),
                'positive_sha256':hashlib.sha256(positive.encode()).hexdigest(),
                'proof_suffix_unchanged':True,'target_proof_line':proof_line,
                'downstream_credit':False,'credit':'fixed-proof sensitivity only, not C mutation or unprovability'}
    (out/'control-protocol.json').write_text(json.dumps(protocol,indent=2)+'\n')
    report = {'inputs':inputs,'checks':{},'passed':False,
              'scope':'same original M -> pointer store Me -> real nonnull event substatement Mf, preserve original outputs plus precise ECB byte frame and matching type',
              'limits':'not prefix/coordinates/primitive update/return/free, not connected to actual abstract events map or queue root, not init/global invariant/GOOD_OS'}
    coq = os.environ.get('COQBIN','')
    flags = ['-q','-R',str(ROOT),'CertiOS','-Q',str(tree),'EventTypeGate']

    def run(label,command):
        start = time.monotonic()
        with (out/(label+'.log')).open('w') as log:
            result = subprocess.run(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,timeout=1200)
        return {'label':label,'exit_code':result.returncode,'seconds':time.monotonic()-start,'log':label+'.log'}

    def keep(row):
        report['checks'][row['label']] = row
        (out/'result.partial.json').write_text(json.dumps(report,indent=2)+'\n')
        return row

    def check(label,command):
        row=keep(run(label,command)); assert row['exit_code']==0, row
        return row

    try:
        # Independent compiler processes; neither imports the other's result.
        with ThreadPoolExecutor(max_workers=2) as pool:
            jobs = [pool.submit(run,'Production',[coq+'coqc',*flags,str(ROOT/SOURCE)]),
                    pool.submit(run,'FrozenPrefix',[coq+'coqc',*flags,str(tree/'FrozenPrefix.v')])]
            results = [keep(j.result()) for j in jobs]
            assert all(r['exit_code']==0 for r in results), results
        check('PositiveRoots',[coq+'coqc',*flags,str(tree/'PositiveRoots.v')])
        for path in probes:
            check(Path(path).stem,[coq+'coqc',*flags,str(ROOT/path)])
        checker = module('check-v293-task-prio-rekey.py')
        report['positive_assumptions'] = checker.checked_assumptions((out/'PositiveRoots.log').read_text(),len(ROOTS))
        report['probe_assumptions'] = checker.checked_assumptions((out/'V293EventTypeProbe.log').read_text(),4)
        assert sha(tree/'HeaderChanged.v') == protocol['negative_sha256']
        row = keep(run('negative-HeaderChanged',[coq+'coqc',*flags,str(tree/'HeaderChanged.v')]))
        match = re.search(r'line (\d+)',(out/row['log']).read_text())
        assert row['exit_code']==1 and match and int(match[1])>proof_line
        row.update(protocol,error_line=int(match[1]))
        commands = [
          ('Production-coqchk',[coq+'coqchk','-silent','-R',str(ROOT),'CertiOS','CertiOS.certiucos.v293.proofs.V293CriticalReturn']),
          ('Probe-coqchk',[coq+'coqchk','-silent','-R',str(ROOT),'CertiOS','CertiOS.audit.probes.V293EventTypeProbe']),
          ('PositiveRoots-coqchk',[coq+'coqchk','-silent','-R',str(ROOT),'CertiOS','-Q',str(tree),'EventTypeGate','EventTypeGate.PositiveRoots'])]
        with ThreadPoolExecutor(max_workers=3) as pool:
            jobs=[pool.submit(run,n,c) for n,c in commands]
            results=[keep(j.result()) for j in jobs]
            assert all(r['exit_code']==0 for r in results), results
        report['passed']=True
    finally:
        module('check-v293-critical-elaboration.py').cleanup(tree,out/'temporary-cleanup.json')
        report['temporary_tree_removed']=not tree.exists()
        report['inputs_unchanged']=all(sha(ROOT/p)==h for p,h in inputs.items())
        (out/'result.json').write_text(json.dumps(report,indent=2)+'\n')
    assert report['inputs_unchanged']
    print(json.dumps({'passed':report['passed'],'checks':len(report['checks']),'output_dir':str(out)},indent=2))


if __name__=='__main__':
    main()
