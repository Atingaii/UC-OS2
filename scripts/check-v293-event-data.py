#!/usr/bin/env python3
"""Actual same-execution SEM/MBOX header-data preservation checks, no GOOD_OS credit."""
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

ROOT=Path(__file__).resolve().parents[1]
SOURCE='certiucos/v293/proofs/V293CriticalReturn.v'
PROBE='audit/probes/V293EventDataProbe.v'
BEFORE='audit/logs/stage26-event-data/Before.v.snapshot.txt'
BEFORE_SHA='c9a9fcee4386465d90729366537ee47b964c9de91770ffa26ea5383b8f71ebef'
BASELINE='audit/logs/stage26-event-data/baseline.json'
TARGET='V293_critical_event_queue_execution_event_frame_data'
ROOTS=['V293_event_data_field_layout','V293_event_header_load_frame',
       'V293_event_sem_mbox_data_frame',TARGET]
PROBES=['audit/probes/'+n+'.v' for n in [
 'V293SuccessCompleteReturnProbe','V293SuccessEntryWitnessProbe','V293ReadyGeneralEntryProbe',
 'V293WaitEventOwnedProbe','V293WaitPayloadProbe','V293EventQueueProbe','V293EventTypeProbe',
 'V293EventReturnFrameProbe','V293EventDataProbe']]
HELPERS=['scripts/check-v293-task-prio-rekey.py','scripts/check-v293-critical-elaboration.py']


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def module(name):
    s=importlib.util.spec_from_file_location(name,ROOT/'scripts'/name)
    m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


def parts(s):
    a=s.index('Theorem '+TARGET+' :')
    imports='\n'.join(dict.fromkeys(x for x in s[:a].splitlines() if x.startswith('Require Import ')))
    return s[:a],('Require Import EventDataGate.FrozenPrefix.\n'+imports+
       '\nImport ListNotations.\nLocal Open Scope nat_scope.\nLocal Opaque HalfPermMap.set.\n'+s[a:])


def controls(s):
    _,positive=parts(s);a=positive.index('Theorem '+TARGET+' :');b=positive.index('Proof.',a)
    header,proof=positive[:b],positive[b:]
    old='V293_event_sem_mbox_data Mf be ebase data).'
    assert header.count(old)==1
    changes={
      'ChangedSemCount':'(match data with abssem n => abssem (Int.add n Int.one) | d => d end)',
      'NullMailboxMessage':'(match data with absmbox _ => absmbox Vnull | d => d end)'}
    negatives={n:header.replace(old,'V293_event_sem_mbox_data Mf be ebase '+replacement+').')+proof
               for n,replacement in changes.items()}
    for x in negatives.values():assert x[x.index('Proof.',x.index('Theorem '+TARGET+' :')):]==proof
    return positive,negatives


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output-dir',type=Path,required=True)
    out=p.parse_args().output_dir.resolve();out.mkdir(parents=True,exist_ok=False)
    source=(ROOT/SOURCE).read_text();before=(ROOT/BEFORE).read_text()
    assert sha(ROOT/BEFORE)==BEFORE_SHA and source.startswith(before)
    prefix,_=parts(source);positive,negative=controls(source)
    inputs={str(f.relative_to(ROOT)):sha(f) for d in ['framework','tactics','certiucos/v293'] for f in (ROOT/d).rglob('*.v')}
    protected=json.loads((ROOT/BASELINE).read_text())['protected']
    for path in [*PROBES,*protected,*HELPERS,BEFORE,BASELINE,'scripts/check-v293-event-data.py']:inputs[path]=sha(ROOT/path)
    tree=Path(tempfile.mkdtemp(prefix='v293-event-data-gate-'))
    prints='\n'+''.join('Print Assumptions '+n+'.\n' for n in ROOTS)
    for name,data in {'FrozenPrefix':prefix,'PositiveRoots':positive+prints,**negative}.items():
        (tree/(name+'.v')).write_text(data);(out/(name+'.v.snapshot.txt')).write_text(data)
    for path,label in [(SOURCE,'Production'),(PROBE,'Probe')]:
        (out/(label+'.v.snapshot.txt')).write_bytes((ROOT/path).read_bytes())
    line=positive[:positive.index('Proof.',positive.index('Theorem '+TARGET+' :'))].count('\n')+1
    protocol={n:{'proof_suffix_unchanged':True,'target_proof_line':line,'downstream_credit':False,
      'positive_sha256':hashlib.sha256(positive.encode()).hexdigest(),'negative_sha256':sha(tree/(n+'.v')),
      'credit':'single final content-factor fixed-Proof sensitivity only; separate semantic probes, not C mutation/unprovability/global invariant'} for n in negative}
    (out/'control-protocol.json').write_text(json.dumps(protocol,indent=2)+'\n')
    report={'inputs':inputs,'checks':{},'passed':False,'old_prefix_unchanged':True,
      'scope':'same full return/free witness, SEM/MBOX header-data linked to same actual abstract ECB query, conditional on entry relation',
      'limits':'no queue backing-storage/mutex-owner/current consistency/init/shared-invariant/API-ISR/normal scheduling/GOOD_OS credit'}
    coq=os.environ.get('COQBIN','');flags=['-q','-R',str(ROOT),'CertiOS','-Q',str(tree),'EventDataGate']
    def run(n,c):
        start=time.monotonic()
        with (out/(n+'.log')).open('w') as f:r=subprocess.run(c,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,timeout=1800)
        return {'label':n,'command':c,'exit_code':r.returncode,'seconds':time.monotonic()-start,'log':n+'.log'}
    def keep(r):report['checks'][r['label']]=r;(out/'result.partial.json').write_text(json.dumps(report,indent=2)+'\n');return r
    def check(n,c):
        r=keep(run(n,c));assert r['exit_code']==0,r
    try:
        with ThreadPoolExecutor(max_workers=2) as pool:
            futures=[pool.submit(run,'Production',[coq+'coqc',*flags,str(ROOT/SOURCE)]),
                     pool.submit(run,'FrozenPrefix',[coq+'coqc',*flags,str(tree/'FrozenPrefix.v')])]
            results=[keep(f.result()) for f in futures];assert all(r['exit_code']==0 for r in results),results
        check('PositiveRoots',[coq+'coqc',*flags,str(tree/'PositiveRoots.v')])
        for path in PROBES:check(Path(path).stem,[coq+'coqc',*flags,str(ROOT/path)])
        checker=module(HELPERS[0].split('/')[-1]);report['positive_assumptions']=checker.checked_assumptions((out/'PositiveRoots.log').read_text(),len(ROOTS))
        report['probe_assumptions']=checker.checked_assumptions((out/'V293EventDataProbe.log').read_text(),9)
        for name in negative:
            assert sha(tree/(name+'.v'))==protocol[name]['negative_sha256']
            r=keep(run('negative-'+name,[coq+'coqc',*flags,str(tree/(name+'.v'))]))
            match=re.search(r'line (\d+)',(out/r['log']).read_text())
            assert r['exit_code']==1 and match and int(match[1])>line,r
            r.update(protocol[name],error_line=int(match[1]))
        cmds=[('Production-coqchk',[coq+'coqchk','-silent','-R',str(ROOT),'CertiOS','CertiOS.certiucos.v293.proofs.V293CriticalReturn']),
          ('Probe-coqchk',[coq+'coqchk','-silent','-R',str(ROOT),'CertiOS','CertiOS.audit.probes.V293EventDataProbe']),
          ('PositiveRoots-coqchk',[coq+'coqchk','-silent','-R',str(ROOT),'CertiOS','-Q',str(tree),'EventDataGate','EventDataGate.PositiveRoots'])]
        with ThreadPoolExecutor(max_workers=3) as pool:
            results=[keep(f.result()) for f in [pool.submit(run,n,c) for n,c in cmds]]
            assert all(r['exit_code']==0 for r in results),results
        report['passed']=True
    finally:
        module(HELPERS[1].split('/')[-1]).cleanup(tree,out/'temporary-cleanup.json')
        report['temporary_tree_removed']=not tree.exists();report['inputs_unchanged']=all(sha(ROOT/path)==h for path,h in inputs.items())
        (out/'result.json').write_text(json.dumps(report,indent=2)+'\n')
    assert report['inputs_unchanged'];print(json.dumps({'passed':report['passed'],'checks':len(report['checks']),'inputs':len(inputs)}))


if __name__=='__main__':main()
