#!/usr/bin/env python3
"""Same-return spatial current ownership; not full invariant or GOOD_OS credit."""
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
PROBE='audit/probes/V293CurrentOwnershipProbe.v'
BEFORE='audit/logs/stage26-current-ownership/Before.v.snapshot.txt'
BEFORE_SHA='5b134f38afad34e6de8027c9d32dc0c1816417ae23e14d5f6301b26def9fb72c'
BASELINE='audit/logs/stage26-current-ownership/baseline.json'
TARGET='V293_critical_event_current_owned_execution'
ROOTS=['V293_ptomvallist_other_block','V293_owned_block_frame','V293_current_owned_frame','V293_current_fields_reconstruct',TARGET]
PROBES=['audit/probes/'+n+'.v' for n in [
 'V293SuccessCompleteReturnProbe','V293SuccessEntryWitnessProbe','V293ReadyGeneralEntryProbe',
 'V293WaitEventOwnedProbe','V293WaitPayloadProbe','V293EventQueueProbe','V293EventTypeProbe',
 'V293EventReturnFrameProbe','V293EventDataProbe','V293CurrentConsistencyProbe','V293CurrentOwnershipProbe']]
HELPERS=['scripts/check-v293-task-prio-rekey.py','scripts/check-v293-critical-elaboration.py']


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def module(name):
    s=importlib.util.spec_from_file_location(name,ROOT/'scripts'/name)
    m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m


def parts(s):
    prefix=(ROOT/BEFORE).read_text();assert s.startswith(prefix)
    imports='\n'.join(dict.fromkeys(x for x in prefix.splitlines() if x.startswith('Require Import ')))
    return prefix,('Require Import CurrentOwnershipGate.FrozenPrefix.\n'+imports+
       '\nImport ListNotations.\nLocal Open Scope nat_scope.\nLocal Opaque HalfPermMap.set.\n'+s[len(prefix):])


def controls(s):
    _,positive=parts(s)
    a=positive.index('Theorem '+TARGET+' :');b=positive.index('Proof.',a)
    h,p=positive[:b],positive[b:]
    old='(CurTid abstract_current ** V293_shared_fields abstract_current'
    # Only the final spatial postcondition; leave the entry ownership intact.
    split=h.index("  exists Mf Os' OO',",a)
    assert h[split:].count(old)==1
    changed=h[:split]+h[split:].replace(old,'(CurTid (bt,Int.repr base) ** V293_shared_fields abstract_current',1)+p
    target='Lemma V293_owned_block_frame :'
    c=positive.index(target);d=positive.index('Proof.',c)
    clause='(forall i, get after (b,i) = get before (b,i)) ->'
    assert positive[c:d].count(clause)==1
    dropped=positive[:c]+positive[c:d].replace(clause,'(forall i : Z, True) ->',1)+positive[d:]
    negatives={'DroppedBlockFrame':dropped,'ChangedCurrent':changed}
    for name,data in negatives.items():
        marker=target if name=='DroppedBlockFrame' else 'Theorem '+TARGET+' :'
        start=lambda x:x.index('Proof.',x.index(marker))
        assert data[start(data):]==positive[start(positive):]
    return positive,negatives


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output-dir',type=Path,required=True)
    out=p.parse_args().output_dir.resolve();out.mkdir(parents=True,exist_ok=False)
    source=(ROOT/SOURCE).read_text();before=(ROOT/BEFORE).read_text()
    assert sha(ROOT/BEFORE)==BEFORE_SHA and source.startswith(before)
    prefix,_=parts(source);positive,negative=controls(source)
    inputs={str(f.relative_to(ROOT)):sha(f) for d in ['framework','tactics','certiucos/v293'] for f in (ROOT/d).rglob('*.v')}
    protected=json.loads((ROOT/BASELINE).read_text())['protected']
    for path in [*PROBES,*protected,*HELPERS,BEFORE,BASELINE,'scripts/check-v293-current-ownership.py']:inputs[path]=sha(ROOT/path)
    tree=Path(tempfile.mkdtemp(prefix='v293-current-ownership-gate-'))
    prints='\n'+''.join('Print Assumptions '+n+'.\n' for n in ROOTS)
    for name,data in {'FrozenPrefix':prefix,'PositiveRoots':positive+prints,**negative}.items():
        (tree/(name+'.v')).write_text(data);(out/(name+'.v.snapshot.txt')).write_text(data)
    for path,label in [(SOURCE,'Production'),(PROBE,'Probe')]:
        (out/(label+'.v.snapshot.txt')).write_bytes((ROOT/path).read_bytes())
    protocol={n:{'proof_suffix_unchanged':True,'target_proof_line':positive[:positive.index('Proof.',positive.index('Lemma V293_owned_block_frame :' if n=='DroppedBlockFrame' else 'Theorem '+TARGET+' :'))].count('\n')+1,'downstream_credit':False,
      'positive_sha256':hashlib.sha256(positive.encode()).hexdigest(),'negative_sha256':sha(tree/(n+'.v')),
      'credit':'one block-frame premise or final current-owned pointer factor; entire target Proof suffix fixed; not C mutation, global unprovability or full invariant'} for n in negative}
    (out/'control-protocol.json').write_text(json.dumps(protocol,indent=2)+'\n')
    report={'inputs':inputs,'checks':{},'passed':False,'old_prefix_unchanged':True,
      'scope':'same full return/free Mf/OO, actual entry CurTid read-half retained, final existing shared core reconstructed',
      'limits':'shared core is not full ready/TCB/event invariant; no init/API-ISR/unlocked scheduling/C frontend/GOOD_OS credit'}
    coq=os.environ.get('COQBIN','');flags=['-q','-R',str(ROOT),'CertiOS','-Q',str(tree),'CurrentOwnershipGate']
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
        report['probe_assumptions']=checker.checked_assumptions((out/'V293CurrentOwnershipProbe.log').read_text(),7)
        for name in negative:
            assert sha(tree/(name+'.v'))==protocol[name]['negative_sha256']
            r=keep(run('negative-'+name,[coq+'coqc',*flags,str(tree/(name+'.v'))]))
            match=re.search(r'line (\d+)',(out/r['log']).read_text())
            assert r['exit_code']==1 and match and int(match[1])>protocol[name]['target_proof_line'],r
            r.update(protocol[name],error_line=int(match[1]))
        cmds=[('Production-coqchk',[coq+'coqchk','-silent','-R',str(ROOT),'CertiOS','CertiOS.certiucos.v293.proofs.V293CriticalReturn']),
          ('Probe-coqchk',[coq+'coqchk','-silent','-R',str(ROOT),'CertiOS','CertiOS.audit.probes.V293CurrentOwnershipProbe']),
          ('PositiveRoots-coqchk',[coq+'coqchk','-silent','-R',str(ROOT),'CertiOS','-Q',str(tree),'CurrentOwnershipGate','CurrentOwnershipGate.PositiveRoots'])]
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
