#!/usr/bin/env python3
"""Finite guarded scheduler call/return gate; not unlocked dispatch or GOOD_OS."""
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
PROBE = 'audit/probes/V293SuccessSchedReturnProbe.v'
MARKER = '(* Success tail and the real scheduler call.'
CALL = 'V293_success_sched_call_execution'
SCHEDULE = 'V293_success_schedule_execution'
TAIL = 'V293_success_tail_return_execution'
ROOTS = [CALL, SCHEDULE, TAIL, 'V293_critical_null_schedule_execution',
         'V293_critical_event_schedule_execution', 'V293_success_tail_return_witness']
PREFIX_SHA = '7ce3552f82e96b602c8e89b92e0bcc979c95e477100e51cdce313e57c970d7dc'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT/'scripts'/name)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def split_source(source):
    before_marker, suffix = source.split(MARKER, 1)
    prefix = before_marker[:-1]
    assert before_marker == prefix+'\n'
    assert len(prefix.encode()) == 123526
    assert hashlib.sha256(prefix.encode()).hexdigest() == PREFIX_SHA
    imports = '\n'.join(line for line in prefix.splitlines() if line.startswith('Require Import '))
    harness = ('Require Import SuccessSchedGate.FrozenPrefix.\n'+imports+
               '\nImport ListNotations.\nLocal Open Scope nat_scope.\nLocal Opaque HalfPermMap.set.\n')
    return prefix, harness+MARKER+suffix


def projection(source, target):
    _, suffix = split_source(source)
    start = suffix.index('Theorem '+target+' :')
    return suffix[:suffix.index('\nQed.', start)+6]+'\n'


def controls(source):
    base = module('check-v293-critical-elaboration.py')
    result = []

    def edit(label, target, transform):
        original = projection(source, target)
        i = original.index('Proof.', original.index('Theorem '+target+' :'))
        changed = transform(original[:i])+original[i:]
        assert changed != original
        assert changed[changed.index('Proof.', changed.index('Theorem '+target+' :')):] == original[i:]
        result.append((label, changed, target, original))

    def definition(text, start, end, old, new):
        i, j = text.index(start), text.index(end, text.index(start))
        return text[:i]+base.replace_once(text[i:j], old, new)+text[j:]

    edit('RunningZero', SCHEDULE, lambda text: definition(text,
        'Definition V293_task_prio_running ', 'Definition V293_task_prio_schedule ',
        '(econst32 Int.one)', '(econst32 Int.zero)'))
    edit('WrongCall', SCHEDULE, lambda text: definition(text,
        'Definition V293_task_prio_schedule ', 'Definition V293_task_prio_success_tail ',
        '(scall sched nil)', '(scall (let original : fid := sched in 999999999%Z) nil)'))

    def no_binding(text):
        i = text.index('Theorem '+CALL+' :')
        old = 'P sched = Some (V293_OSSched_success_function saved interrupt lock schednew table high target current counter) ->'
        return text[:i]+base.replace_once(text[i:], old, '(let original : function := V293_OSSched_success_function saved interrupt lock schednew table high target current counter in True) ->')
    edit('NoFunctionBinding', CALL, no_binding)
    edit('ExitSti', CALL, lambda text: definition(text,
        'Definition V293_OSSched_success_body ', 'Definition V293_OSSched_success_function ',
        '(sprim excrit)', '(sprim sti)'))
    edit('ReturnOne', TAIL, lambda text: definition(text,
        'Definition V293_task_prio_success_tail ', 'Lemma V293_success_allocb_outside ',
        '(srete (econst32 Int.zero))', '(srete (econst32 Int.one))'))

    def wrong_caller(text):
        i = text.index('Theorem '+TAIL+' :')
        return text[:i]+base.replace_once(text[i:], '((ge,caller,Mf),ir,(enabled,si,ci))',
                                        '((ge,le,Mf),ir,(enabled,si,ci))')
    edit('CallerNotRestored', TAIL, wrong_caller)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', required=True, type=Path)
    out = parser.parse_args().output_dir.resolve()
    out.mkdir(parents=True, exist_ok=False)
    source = (ROOT/SOURCE).read_text()
    prefix, suffix = split_source(source)
    inputs = {str(p.relative_to(ROOT)): sha(p) for d in ['framework', 'tactics', 'certiucos/v293']
              for p in sorted((ROOT/d).rglob('*.v'))}
    for path in [PROBE, '_CoqProject', 'scripts/check-v293-success-sched-return.py',
                 'scripts/check-v293-critical-elaboration.py', 'scripts/check-v293-task-prio-rekey.py',
                 'csrc/repairs/FROZEN_SOURCE.json', 'audit/coverage.json']:
        inputs[path] = sha(ROOT/path)
    tree = Path(tempfile.mkdtemp(prefix='v293-success-sched-gate-'))
    (tree/'FrozenPrefix.v').write_text(prefix)
    (out/'FrozenPrefix.v.snapshot.txt').write_text(prefix)
    (out/'Production.v.snapshot.txt').write_text(source)
    positives = [('PositiveAll', suffix, ROOTS)]
    positives += [('Positive'+label, projection(source, root), [root])
                  for label,root in [('Call',CALL), ('Schedule',SCHEDULE), ('Tail',TAIL)]]
    for label, text, roots in positives:
        text += '\n'+''.join('Print Assumptions '+r+'.\n' for r in roots)
        (tree/(label+'.v')).write_text(text)
        (out/(label+'.v.snapshot.txt')).write_text(text)
    protocol = []
    for label, text, target, original in controls(source):
        (tree/(label+'.v')).write_text(text)
        (out/(label+'.v.snapshot.txt')).write_text(text)
        protocol.append({'label':label, 'target':target, 'sha256':sha(tree/(label+'.v')),
                         'target_proof_line':text[:text.index('Proof.', text.index(target+' :'))].count('\n')+1,
                         'proof_suffix_unchanged':True, 'downstream_credit':False})
    (out/'control-protocol.json').write_text(json.dumps(protocol, indent=2)+'\n')
    report = {'inputs':inputs, 'checks':{}, 'passed':False,
              'scope':'explicit-macro finite non-running/ISR/locked traces; updates reach guarded call, separate tail reaches return/free/caller; NOT one whole-API root, unlocked dispatch, shared invariant, raw port, concurrency, initialization, GOOD_OS',
              'dependencies':'existing products, no clean-build credit'}
    coq = os.environ.get('COQBIN', '')
    checker = module('check-v293-task-prio-rekey.py')

    def run(label, command):
        start = time.monotonic()
        with (out/(label+'.log')).open('w') as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, timeout=600)
        row = {'exit_code':result.returncode, 'seconds':time.monotonic()-start, 'log':label+'.log'}
        report['checks'][label] = row
        (out/'result.partial.json').write_text(json.dumps(report, indent=2)+'\n')
        return row
    try:
        for label, path in [('production',SOURCE), ('probe',PROBE)]:
            assert run(label+'-coqc', [coq+'coqc', '-q', '-R', str(ROOT), 'CertiOS', path])['exit_code'] == 0
        report['probe_assumptions'] = checker.checked_assumptions((out/'probe-coqc.log').read_text(), len(ROOTS))
        for label, mod in [('production','certiucos.v293.proofs.V293CriticalReturn'),
                           ('probe','audit.probes.V293SuccessSchedReturnProbe')]:
            assert run(label+'-coqchk', [coq+'coqchk', '-silent', '-R', str(ROOT), 'CertiOS', 'CertiOS.'+mod])['exit_code'] == 0
        flags = ['-q', '-R', str(ROOT), 'CertiOS', '-Q', str(tree), 'SuccessSchedGate']
        assert run('FrozenPrefix', [coq+'coqc', *flags, str(tree/'FrozenPrefix.v')])['exit_code'] == 0
        report['positive_assumptions'] = {}
        for label, text, roots in positives:
            assert run(label, [coq+'coqc', *flags, str(tree/(label+'.v'))])['exit_code'] == 0
            report['positive_assumptions'][label] = checker.checked_assumptions((out/(label+'.log')).read_text(), len(roots))
        assert run('PositiveAll-coqchk', [coq+'coqchk','-silent','-R',str(ROOT),'CertiOS','-Q',str(tree),'SuccessSchedGate','SuccessSchedGate.PositiveAll'])['exit_code'] == 0
        for entry in protocol:
            label = entry['label']
            assert sha(tree/(label+'.v')) == entry['sha256']
            row = run('negative-'+label, [coq+'coqc', *flags, str(tree/(label+'.v'))])
            match = re.search(r'line (\d+)', (out/row['log']).read_text())
            assert row['exit_code'] == 1 and match and int(match[1]) > entry['target_proof_line'], row
            row.update(entry, error_line=int(match[1]))
        report['passed'] = True
    finally:
        module('check-v293-critical-elaboration.py').cleanup(tree, out/'temporary-cleanup.json')
        report['temporary_tree_removed'] = not tree.exists()
        report['inputs_unchanged'] = all(sha(ROOT/p) == h for p,h in inputs.items())
        (out/'result.json').write_text(json.dumps(report, indent=2)+'\n')
    assert report['inputs_unchanged']
    print(json.dumps({'passed':report['passed'], 'checks':len(report['checks']), 'output_dir':str(out)}, indent=2))


if __name__ == '__main__':
    main()
