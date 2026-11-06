#!/usr/bin/env python3
"""Check actual ECB waiter-list correspondence on the same complete event-return heap."""
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
PROBE = 'audit/probes/V293EventQueueProbe.v'
PREFIX_BYTES = 379633
PREFIX_SHA = 'c7e749a65e8274e4b83ebc60bf254cc04b9dfbade7e47649b33d1383bdf86cba'
TARGET = 'V293_critical_event_queue_execution'
ROOTS = ['V293_event_wait_queue_rekey', 'V293_event_queue_priorities_bound', TARGET]


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
    harness = ('Require Import EventQueueGate.FrozenPrefix.\n'+imports+
               '\nImport ListNotations.\nLocal Open Scope nat_scope.\nLocal Opaque HalfPermMap.set.\n')
    return prefix.decode(), suffix, harness


def controls(source):
    _, suffix, harness = parts(source)
    original = harness+suffix
    i = original.index('Proof.', original.index('Theorem '+TARGET+' :'))
    header, proof = original[:i], original[i:]
    result = []
    for label, old, new, obligation in [
        ('WaiterDropped',
         '    (be,Int.repr ebase) reason data waiters /\\',
         '    (be,Int.repr ebase) reason data nil /\\',
         'final ECB queue must retain the actual waiter list'),
        ('EventDataChanged',
         '    (be,Int.repr ebase) reason data waiters /\\',
         '    (be,Int.repr ebase) reason (absmbox Vnull) waiters /\\',
         'final ECB lookup must retain its typed event data')]:
        assert header.count(old) == 1
        changed = header.replace(old, new)+proof
        assert changed[changed.index('Proof.', changed.index('Theorem '+TARGET+' :')):] == proof
        result.append((label, changed, original, obligation))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    out = parser.parse_args().output_dir.resolve()
    out.mkdir(parents=True, exist_ok=False)
    source = (ROOT/SOURCE).read_text()
    prefix, suffix, harness = parts(source)
    inputs = {str(p.relative_to(ROOT)): sha(p) for d in ['framework', 'tactics', 'certiucos/v293']
              for p in sorted((ROOT/d).rglob('*.v'))}
    probes = ['audit/probes/V293SuccessCompleteReturnProbe.v',
              'audit/probes/V293SuccessEntryWitnessProbe.v',
              'audit/probes/V293ReadyGeneralEntryProbe.v',
              'audit/probes/V293WaitEventOwnedProbe.v',
              'audit/probes/V293WaitPayloadProbe.v', PROBE]
    for p in [*probes, '_CoqProject', 'scripts/check-v293-event-queue.py',
              'scripts/check-v293-critical-elaboration.py', 'scripts/check-v293-task-prio-rekey.py',
              'csrc/repairs/FROZEN_SOURCE.json', 'audit/coverage.json']:
        inputs[p] = sha(ROOT/p)
    tree = Path(tempfile.mkdtemp(prefix='v293-event-queue-gate-'))
    files = {'FrozenPrefix': prefix, 'PositiveRoots': harness+suffix+
             '\n'+''.join('Print Assumptions '+n+'.\n' for n in ROOTS)}
    protocol = []
    for label, changed, original, obligation in controls(source):
        files[label] = changed
        protocol.append({'label': label, 'target': TARGET,
                         'sha256': hashlib.sha256(changed.encode()).hexdigest(),
                         'positive_sha256': hashlib.sha256(original.encode()).hexdigest(),
                         'target_proof_line': changed[:changed.index('Proof.', changed.index('Theorem '+TARGET+' :'))].count('\n')+1,
                         'proof_suffix_unchanged': True, 'downstream_credit': False,
                         'intended_obligation': obligation,
                         'credit': 'fixed-proof sensitivity only; not C mutation or unprovability'})
    for name, content in files.items():
        (tree/(name+'.v')).write_text(content)
        (out/(name+'.v.snapshot.txt')).write_text(content)
    (out/'Production.v.snapshot.txt').write_text(source)
    (out/'Probe.v.snapshot.txt').write_bytes((ROOT/PROBE).read_bytes())
    (out/'control-protocol.json').write_text(json.dumps(protocol, indent=2)+'\n')
    report = {'inputs': inputs, 'checks': {}, 'passed': False,
              'scope': 'same return heap and owned abstract step: typed actual ECB lookup, bidirectional waiter-list/task membership, final physical event bitmap corresponds to same retained ECB list; previous payload and returns retained',
              'limits': 'physical OSEventType/data/count/pointer and physical/abstract current binding open; duplicate-free list not established; scheduler blocked; not full invariant/forward simulation/API/init/GOOD_OS; historical evidence unchanged, no old-gate replay credit'}
    coq = os.environ.get('COQBIN', '')
    flags = ['-q', '-R', str(ROOT), 'CertiOS', '-Q', str(tree), 'EventQueueGate']

    def run(label, command):
        start = time.monotonic()
        with (out/(label+'.log')).open('w') as log:
            r = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, timeout=1200)
        row = {'exit_code': r.returncode, 'seconds': time.monotonic()-start, 'log': label+'.log'}
        report['checks'][label] = row
        (out/'result.partial.json').write_text(json.dumps(report, indent=2)+'\n')
        return row

    try:
        for label, path in [('production', SOURCE), *[(Path(p).stem, p) for p in probes]]:
            assert run(label+'-coqc', [coq+'coqc', '-q', '-R', str(ROOT), 'CertiOS', path])['exit_code'] == 0
        checker = module('check-v293-task-prio-rekey.py')
        report['probe_assumptions'] = checker.checked_assumptions((out/'V293EventQueueProbe-coqc.log').read_text(), 4)
        for label, name in [('production', 'certiucos.v293.proofs.V293CriticalReturn'),
                            ('probe', 'audit.probes.V293EventQueueProbe')]:
            assert run(label+'-coqchk', [coq+'coqchk', '-silent', '-R', str(ROOT), 'CertiOS', 'CertiOS.'+name])['exit_code'] == 0
        assert run('FrozenPrefix', [coq+'coqc', *flags, str(tree/'FrozenPrefix.v')])['exit_code'] == 0
        assert run('PositiveRoots', [coq+'coqc', *flags, str(tree/'PositiveRoots.v')])['exit_code'] == 0
        report['positive_assumptions'] = checker.checked_assumptions((out/'PositiveRoots.log').read_text(), len(ROOTS))
        assert run('PositiveRoots-coqchk', [coq+'coqchk', '-silent', '-R', str(ROOT), 'CertiOS',
                   '-Q', str(tree), 'EventQueueGate', 'EventQueueGate.PositiveRoots'])['exit_code'] == 0
        for entry in protocol:
            label = entry['label']
            assert sha(tree/(label+'.v')) == entry['sha256']
            row = run('negative-'+label, [coq+'coqc', *flags, str(tree/(label+'.v'))])
            match = re.search(r'line (\d+)', (out/row['log']).read_text())
            assert row['exit_code'] == 1 and match and int(match[1]) > entry['target_proof_line']
            row.update(entry, error_line=int(match[1]))
        report['passed'] = True
    finally:
        module('check-v293-critical-elaboration.py').cleanup(tree, out/'temporary-cleanup.json')
        report['temporary_tree_removed'] = not tree.exists()
        report['inputs_unchanged'] = all(sha(ROOT/p) == h for p, h in inputs.items())
        (out/'result.json').write_text(json.dumps(report, indent=2)+'\n')
    assert report['inputs_unchanged']
    print(json.dumps({'passed': report['passed'], 'checks': len(report['checks']), 'output_dir': str(out)}, indent=2))


if __name__ == '__main__':
    main()
