#!/usr/bin/env python3
"""Original-memory finite success paths to real guarded call and complete return."""
import argparse
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
PROBE = 'audit/probes/V293SuccessCompleteReturnProbe.v'
PREFIX_BYTES = 166699
PREFIX_SHA = '2019d05a00af959cbc948bfa02d930595c62f1919648aeb1635776edbd37c57e'
NULL = 'V293_critical_null_success_return_execution'
EVENT = 'V293_critical_event_success_return_execution'
ROOTS = [NULL, EVENT, 'V293_success_load_free_permission_ablation']
HELPER = 'V293_task_prio_prefix_null_update_execution_writable'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT/'scripts'/name)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def split_source(source):
    raw = source.encode()
    prefix = raw[:PREFIX_BYTES]
    assert hashlib.sha256(prefix).hexdigest() == PREFIX_SHA
    suffix = raw[PREFIX_BYTES:].decode()
    imports = '\n'.join(l for l in prefix.decode().splitlines() if l.startswith('Require Import '))
    harness = ('Require Import CompleteReturnGate.FrozenPrefix.\n'+imports+
               '\nImport ListNotations.\nLocal Open Scope nat_scope.\nLocal Opaque HalfPermMap.set.\n')
    start = suffix.index('Theorem '+NULL+' :')
    return prefix.decode(), harness, suffix[:start], suffix[start:]


def declaration(source, target):
    start = source.index('Theorem '+target+' :')
    return source[start:source.index('\nQed.', start)+6]+'\n'


def controls(source):
    prefix, harness, helpers, roots = split_source(source)
    result = []
    base = harness+'Require Import CompleteReturnGate.Helpers.\n'+declaration(roots, NULL)

    def edit(label, old, new):
        i = base.index('Proof.', base.index('Theorem '+NULL+' :'))
        assert base[:i].count(old) == 1, (label, old)
        changed = base[:i].replace(old, new)+base[i:]
        assert changed[changed.index('Proof.', changed.index('Theorem '+NULL+' :')):] == base[i:]
        result.append((label, changed, NULL, True, base))

    edit('ReadableNotWritable',
         'V293_bytes_writable M c 0%Z (typelen t)',
         '(forall k, k < typelen t -> exists v, get M (c,Z.of_nat k) = Some (true,v) \\/ get M (c,Z.of_nat k) = Some (false,v))')
    edit('NoDupRemoved', 'NoDup (map fst (getaddr le)) ->', 'True ->')
    edit('HeapTableMayBeLocal',
         '(forall c, In c [b;bt;br;bg] -> ~ In c (map fst (getaddr le))) ->',
         '(forall c, In c [bt;br;bg] -> ~ In c (map fst (getaddr le))) ->')
    edit('ReturnOne', '(curs (sskip (Some (Vint32 Int.zero))),(kenil,next))',
         '(curs (sskip (Some (Vint32 Int.one))),(kenil,next))')
    edit('CallerNotRestored', '((ge,caller,Mf),ir,(enabled,si,ci))',
         '((ge,le,Mf),ir,(enabled,si,ci))')
    start = helpers.index('Theorem '+HELPER+' :')
    end = helpers.index('\nQed.', start)+6
    original = harness+helpers[:end]+'\n'
    old = '+ eapply V293_store_writable;exact S2.'
    assert original.count(old) == 1
    changed = original.replace(old, '+ apply V293_writable_refl.')
    result.append(('SecondTableStoreNeutralized', changed, HELPER, False, original))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    out = parser.parse_args().output_dir.resolve()
    out.mkdir(parents=True, exist_ok=False)
    source = (ROOT/SOURCE).read_text()
    prefix, harness, helpers, roots = split_source(source)
    inputs = {str(p.relative_to(ROOT)):sha(p) for d in ['framework','tactics','certiucos/v293']
              for p in sorted((ROOT/d).rglob('*.v'))}
    for p in [PROBE,'_CoqProject','scripts/check-v293-success-complete-return.py',
              'scripts/check-v293-critical-elaboration.py','scripts/check-v293-task-prio-rekey.py',
              'csrc/repairs/FROZEN_SOURCE.json','audit/coverage.json']:
        inputs[p] = sha(ROOT/p)
    tree = Path(tempfile.mkdtemp(prefix='v293-complete-return-gate-'))
    files = {'FrozenPrefix':prefix,'Helpers':harness+helpers,
             'PositiveRoots':harness+'Require Import CompleteReturnGate.Helpers.\n'+roots}
    # Root-specific positives use exactly the same imported helper boundary as negatives.
    files.update({'Positive'+label:harness+'Require Import CompleteReturnGate.Helpers.\n'+declaration(roots,name)
                  for label,name in [('Null',NULL),('Event',EVENT)]})
    for label in ['PositiveRoots','PositiveNull','PositiveEvent']:
        names = ROOTS if label == 'PositiveRoots' else [NULL if label == 'PositiveNull' else EVENT]
        files[label] += '\n'+''.join('Print Assumptions '+n+'.\n' for n in names)
    protocol = []
    for label, text, target, unchanged, original in controls(source):
        files[label] = text
        if label == 'SecondTableStoreNeutralized':
            files['PositiveTableStore'] = original+'\nPrint Assumptions '+HELPER+'.\n'
        protocol.append({'label':label,'target':target,'proof_suffix_unchanged':unchanged,
                         'target_proof_line':text[:text.index('Proof.',text.index('Theorem '+target+' :'))].count('\n')+1,
                         'downstream_credit':False})
    for label,text in files.items():
        (tree/(label+'.v')).write_text(text)
        (out/(label+'.v.snapshot.txt')).write_text(text)
    (out/'Production.v.snapshot.txt').write_text(source)
    for row in protocol:
        row['sha256'] = sha(tree/(row['label']+'.v'))
    (out/'control-protocol.json').write_text(json.dumps(protocol,indent=2)+'\n')
    report = {'inputs':inputs,'checks':{},'passed':False,
              'scope':'same original M -> argument guards/critical entry/SELF/lookup/coordinates/table/bitmap/TCB/event updates -> excrit -> actual guarded scheduler call -> return 0/free all locals/restore caller; finite nonrunning or ISR/locked paths only; NOT unlocked dispatch, raw-port correspondence, shared invariant, whole function entry allocation, initialization, GOOD_OS',
              'dependencies':'existing products; no source-only clean-build or old-gate-replay credit'}
    coq = os.environ.get('COQBIN','')
    flags = ['-q','-R',str(ROOT),'CertiOS','-Q',str(tree),'CompleteReturnGate']
    checker = module('check-v293-task-prio-rekey.py')

    def run(label,command):
        start = time.monotonic()
        with (out/(label+'.log')).open('w') as log:
            r = subprocess.run(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,timeout=1200)
        row = {'exit_code':r.returncode,'seconds':time.monotonic()-start,'log':label+'.log'}
        report['checks'][label] = row
        (out/'result.partial.json').write_text(json.dumps(report,indent=2)+'\n')
        return row
    try:
        for label,path in [('production',SOURCE),('probe',PROBE)]:
            assert run(label+'-coqc',[coq+'coqc','-q','-R',str(ROOT),'CertiOS',path])['exit_code'] == 0
        report['probe_assumptions'] = checker.checked_assumptions((out/'probe-coqc.log').read_text(), len(ROOTS))
        for label,mod in [('production','certiucos.v293.proofs.V293CriticalReturn'),('probe','audit.probes.V293SuccessCompleteReturnProbe')]:
            assert run(label+'-coqchk',[coq+'coqchk','-silent','-R',str(ROOT),'CertiOS','CertiOS.'+mod])['exit_code'] == 0
        for label in ['FrozenPrefix','Helpers','PositiveRoots','PositiveNull','PositiveEvent','PositiveTableStore']:
            assert run(label,[coq+'coqc',*flags,str(tree/(label+'.v'))])['exit_code'] == 0
            if label.startswith('Positive'):
                report.setdefault('positive_assumptions',{})[label] = checker.checked_assumptions((out/(label+'.log')).read_text(), len(ROOTS) if label == 'PositiveRoots' else 1)
        assert run('PositiveRoots-coqchk',[coq+'coqchk','-silent','-R',str(ROOT),'CertiOS','-Q',str(tree),'CompleteReturnGate','CompleteReturnGate.PositiveRoots'])['exit_code'] == 0
        for entry in protocol:
            label = entry['label']
            assert sha(tree/(label+'.v')) == entry['sha256']
            row = run('negative-'+label,[coq+'coqc',*flags,str(tree/(label+'.v'))])
            match = re.search(r'line (\d+)',(out/row['log']).read_text())
            assert row['exit_code'] == 1 and match and int(match[1]) > entry['target_proof_line'], row
            row.update(entry,error_line=int(match[1]))
        report['passed'] = True
    finally:
        module('check-v293-critical-elaboration.py').cleanup(tree,out/'temporary-cleanup.json')
        report['temporary_tree_removed'] = not tree.exists()
        report['inputs_unchanged'] = all(sha(ROOT/p) == h for p,h in inputs.items())
        (out/'result.json').write_text(json.dumps(report,indent=2)+'\n')
    assert report['inputs_unchanged']
    print(json.dumps({'passed':report['passed'],'checks':len(report['checks']),'output_dir':str(out)},indent=2))


if __name__ == '__main__':
    main()
