#!/usr/bin/env python3
"""Check the same complete blocked-scheduler return/free witness and ECB frame."""
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
PROBE='audit/probes/V293EventReturnFrameProbe.v'
TARGET='V293_critical_event_queue_execution_event_frame'
ORIGINALS=['V293_task_prio_prefix_event_update_preserves_writable',
 'V293_task_prio_coordinates_update_execution_writable',
 'V293_critical_event_update_execution_writable','V293_critical_event_return_tcb_frame',
 'V293_critical_wait_payload_execution','V293_critical_event_queue_execution']
ROOTS=[n+'_event_frame' for n in ORIGINALS]+['V293_event_rekey_byte_frame','V293_event_type_matches_frame']
BEFORE='audit/logs/stage26-event-return-frame/Before.v.snapshot.txt'
BEFORE_SHA='18c385b26da990e0e50f0606121b2399fdd32fcf89ee577bebb4bc9b8296dcb1'
PROBES=['audit/probes/'+n+'.v' for n in [
 'V293SuccessCompleteReturnProbe','V293SuccessEntryWitnessProbe','V293ReadyGeneralEntryProbe',
 'V293WaitEventOwnedProbe','V293WaitPayloadProbe','V293EventQueueProbe','V293EventTypeProbe',
 'V293EventReturnFrameProbe']]


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def module(name):
    spec=importlib.util.spec_from_file_location(name,ROOT/'scripts'/name)
    result=importlib.util.module_from_spec(spec);spec.loader.exec_module(result);return result


def statement(s,name):
    a=s.index('Theorem '+name+' :');return s[a:s.index('Proof.',a)]


def parts(s):
    a=s.index('Theorem '+TARGET+' :')
    imports='\n'.join(dict.fromkeys(l for l in s[:a].splitlines() if l.startswith('Require Import ')))
    harness=('Require Import EventReturnFrameGate.FrozenPrefix.\n'+imports+
      '\nImport ListNotations.\nLocal Open Scope nat_scope.\nLocal Opaque HalfPermMap.set.\n')
    return s[:a],harness+s[a:]


def controls(s):
    _,positive=parts(s);a=positive.index('Theorem '+TARGET+' :');b=positive.index('Proof.',a)
    header,proof=positive[:b],positive[b:]
    changes={
      'WrittenByteFramed':('  (forall i, (i < ebase+10 \\/ ebase+12 < i)%Z -> get Mf (be,i) = get M (be,i))',
                          '  (forall i, True -> get Mf (be,i) = get M (be,i))'),
      'MailboxSubstituted':('V293_event_type_matches Mf be ebase data).',
                            'V293_event_type_matches Mf be ebase (absmbox Vnull)).')}
    result={}
    for name,(old,new) in changes.items():
        assert header.count(old)==1,(name,header.count(old))
        changed=header.replace(old,new)+proof
        assert changed[changed.index('Proof.',changed.index('Theorem '+TARGET+' :')):]==proof
        result[name]=changed
    return positive,result


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output-dir',type=Path,required=True)
    out=p.parse_args().output_dir.resolve();out.mkdir(parents=True,exist_ok=False)
    s=(ROOT/SOURCE).read_text();before=(ROOT/BEFORE).read_text();assert sha(ROOT/BEFORE)==BEFORE_SHA
    # Old entry and exit statements are byte-identical, not weakened compatibility claims.
    for n in ORIGINALS: assert statement(s,n)==statement(before,n),n
    prefix,_=parts(s);positive,negative=controls(s)
    prints='\n'+''.join('Print Assumptions '+n+'.\n' for n in ROOTS)
    inputs={str(p.relative_to(ROOT)):sha(p) for d in ['framework','tactics','certiucos/v293'] for p in (ROOT/d).rglob('*.v')}
    protected=json.loads((ROOT/'audit/logs/stage26-event-return-frame/baseline.json').read_text())['protected']
    for path in [*PROBES,*protected,BEFORE,'scripts/check-v293-event-return-frame.py']:
        inputs[path]=sha(ROOT/path)
    tree=Path(tempfile.mkdtemp(prefix='v293-event-return-frame-gate-'))
    files={'FrozenPrefix':prefix,'PositiveRoots':positive+prints,**negative}
    for name,data in files.items():
        (tree/(name+'.v')).write_text(data);(out/(name+'.v.snapshot.txt')).write_text(data)
    for path,label in [(SOURCE,'Production'),(PROBE,'Probe')]:
        (out/(label+'.v.snapshot.txt')).write_bytes((ROOT/path).read_bytes())
    line=positive[:positive.index('Proof.',positive.index('Theorem '+TARGET+' :'))].count('\n')+1
    protocol={n:{'target_proof_line':line,'proof_suffix_unchanged':True,'downstream_credit':False,
       'negative_sha256':sha(tree/(n+'.v')),'positive_sha256':hashlib.sha256(positive.encode()).hexdigest(),
       'credit':'fixed-proof postcondition sensitivity only; independent full-return semantic controls are in probe'} for n in negative}
    (out/'control-protocol.json').write_text(json.dumps(protocol,indent=2)+'\n')
    report={'inputs':inputs,'checks':{},'passed':False,'old_public_statements_identical':True,
       'scope':'one actual complete blocked-scheduler return/free witness; retain all original outputs plus ECB fine byte frame and kind preservation for data from same abstract ECB lookup',
       'limits':'not initialization/global shared invariant/current-task consistency/API-ISR preservation/unblocked scheduling/GOOD_OS; kind consistency at entry is conditional, not established globally'}
    coq=os.environ.get('COQBIN','');flags=['-q','-R',str(ROOT),'CertiOS','-Q',str(tree),'EventReturnFrameGate']
    def run(n,c):
        start=time.monotonic()
        with (out/(n+'.log')).open('w') as log:
            r=subprocess.run(c,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,timeout=1800)
        return {'label':n,'exit_code':r.returncode,'seconds':time.monotonic()-start,'log':n+'.log'}
    def keep(row):
        report['checks'][row['label']]=row;(out/'result.partial.json').write_text(json.dumps(report,indent=2)+'\n');return row
    def check(n,c):
        row=keep(run(n,c));assert row['exit_code']==0,row
    try:
        with ThreadPoolExecutor(max_workers=2) as pool:
            jobs=[pool.submit(run,'Production',[coq+'coqc',*flags,str(ROOT/SOURCE)]),
                  pool.submit(run,'FrozenPrefix',[coq+'coqc',*flags,str(tree/'FrozenPrefix.v')])]
            results=[keep(j.result()) for j in jobs];assert all(r['exit_code']==0 for r in results),results
        check('PositiveRoots',[coq+'coqc',*flags,str(tree/'PositiveRoots.v')])
        for path in PROBES:check(Path(path).stem,[coq+'coqc',*flags,str(ROOT/path)])
        checker=module('check-v293-task-prio-rekey.py')
        report['positive_assumptions']=checker.checked_assumptions((out/'PositiveRoots.log').read_text(),len(ROOTS))
        report['probe_assumptions']=checker.checked_assumptions((out/'V293EventReturnFrameProbe.log').read_text(),5)
        for n in negative:
            assert sha(tree/(n+'.v'))==protocol[n]['negative_sha256']
            row=keep(run('negative-'+n,[coq+'coqc',*flags,str(tree/(n+'.v'))]))
            match=re.search(r'line (\d+)',(out/row['log']).read_text())
            assert row['exit_code']==1 and match and int(match[1])>line,row
            row.update(protocol[n],error_line=int(match[1]))
        commands=[('Production-coqchk',[coq+'coqchk','-silent','-R',str(ROOT),'CertiOS','CertiOS.certiucos.v293.proofs.V293CriticalReturn']),
         ('Probe-coqchk',[coq+'coqchk','-silent','-R',str(ROOT),'CertiOS','CertiOS.audit.probes.V293EventReturnFrameProbe']),
         ('PositiveRoots-coqchk',[coq+'coqchk','-silent','-R',str(ROOT),'CertiOS','-Q',str(tree),'EventReturnFrameGate','EventReturnFrameGate.PositiveRoots'])]
        with ThreadPoolExecutor(max_workers=3) as pool:
            results=[keep(j.result()) for j in [pool.submit(run,n,c) for n,c in commands]]
            assert all(r['exit_code']==0 for r in results),results
        report['passed']=True
    finally:
        module('check-v293-critical-elaboration.py').cleanup(tree,out/'temporary-cleanup.json')
        report['temporary_tree_removed']=not tree.exists();report['inputs_unchanged']=all(sha(ROOT/p)==h for p,h in inputs.items())
        (out/'result.json').write_text(json.dumps(report,indent=2)+'\n')
    assert report['inputs_unchanged'];print(json.dumps({'passed':report['passed'],'checks':len(report['checks']),'output_dir':str(out)},indent=2))


if __name__=='__main__':main()
