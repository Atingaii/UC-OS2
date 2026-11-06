#!/usr/bin/env python3
"""Check concrete, simultaneous success entries; no initialization credit."""
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
PROBE = 'audit/probes/V293SuccessEntryWitnessProbe.v'
OLD_PROBE = 'audit/probes/V293SuccessCompleteReturnProbe.v'
PREFIX_BYTES = 264621
PREFIX_SHA = 'e12712865a0eb880c270d1307c0f3e7ccf7db18e99ca17e57a3f7a35da31fc89'
NULL = 'V293_critical_null_success_return_witness'
EVENT = 'V293_critical_event_success_return_witness'
ROOTS = [NULL, EVENT]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT/'scripts'/name)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def declaration(source, name):
    start = source.index('Theorem '+name+' :')
    return source[start:source.index('\nQed.', start)+6]+'\n'


def split_source(source):
    raw = source.encode()
    prefix = raw[:PREFIX_BYTES]
    assert hashlib.sha256(prefix).hexdigest() == PREFIX_SHA
    suffix = raw[PREFIX_BYTES:].decode()
    imports = '\n'.join(l for l in prefix.decode().splitlines() if l.startswith('Require Import '))
    harness = ('Require Import SuccessEntryGate.FrozenPrefix.\n'+imports+
               '\nImport ListNotations.\nLocal Open Scope nat_scope.\nLocal Opaque HalfPermMap.set.\n')
    start = suffix.index('Theorem '+NULL+' :')
    return prefix.decode(), harness, suffix[:start], suffix[start:]


def controls(source):
    _, harness, helpers, roots = split_source(source)
    rows = []
    for label, target, old, new, obligation in [
        ('ReturnOne', NULL, '(sskip (Some (Vint32 Int.zero)))',
         '(sskip (Some (Vint32 Int.one)))', 'final trace returns zero'),
        ('LocalRetained', NULL, 'get Mf (c,Z.of_nat k) = None',
         'get Mf (c,Z.of_nat k) = Some (true,Byte (Byte.repr 6))',
         'all-local deletion observation'),
        ('EventBitmapNeutralized', EVENT,
         'V293_event_bitmap_loads Mf 72%positive 5%Z 64 0 1',
         'V293_event_bitmap_loads Mf 72%positive 5%Z 0 0 1',
         'final event bitmap observation'),
    ]:
        original = harness+helpers+declaration(roots, target)
        i = original.index('Proof.', original.index('Theorem '+target+' :'))
        assert original[:i].count(old) == 1
        changed = original[:i].replace(old, new)+original[i:]
        assert changed[changed.index('Proof.', changed.index('Theorem '+target+' :')):] == original[i:]
        rows.append((label, target, changed, original, obligation))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    out = parser.parse_args().output_dir.resolve()
    out.mkdir(parents=True, exist_ok=False)
    source = (ROOT/SOURCE).read_text()
    prefix, harness, helpers, roots = split_source(source)
    inputs = {str(p.relative_to(ROOT)): sha(p)
              for d in ['framework', 'tactics', 'certiucos/v293']
              for p in sorted((ROOT/d).rglob('*.v'))}
    for p in [PROBE, OLD_PROBE, '_CoqProject', 'scripts/check-v293-success-entry-witness.py',
              'scripts/check-v293-success-complete-return.py',
              'scripts/check-v293-critical-elaboration.py', 'scripts/check-v293-task-prio-rekey.py',
              'csrc/repairs/FROZEN_SOURCE.json', 'audit/coverage.json']:
        inputs[p] = sha(ROOT/p)
    tree = Path(tempfile.mkdtemp(prefix='v293-success-entry-gate-'))
    files = {'FrozenPrefix': prefix, 'PositiveRoots': harness+helpers+roots}
    for label, name in [('PositiveNull', NULL), ('PositiveEvent', EVENT)]:
        files[label] = harness+helpers+declaration(roots, name)
    for label, names in [('PositiveRoots', ROOTS), ('PositiveNull', [NULL]), ('PositiveEvent', [EVENT])]:
        files[label] += '\n'+''.join('Print Assumptions '+n+'.\n' for n in names)
    protocol = []
    for label, target, changed, original, obligation in controls(source):
        files[label] = changed
        protocol.append({
            'label': label, 'target': target, 'sha256': hashlib.sha256(changed.encode()).hexdigest(),
            'positive_sha256': hashlib.sha256(original.encode()).hexdigest(),
            'proof_suffix_unchanged': True,
            'target_proof_line': changed[:changed.index('Proof.', changed.index('Theorem '+target+' :'))].count('\n')+1,
            'intended_obligation': obligation, 'downstream_credit': False,
            'interpretation': 'fixed-proof output-contract sensitivity only; not C mutation or unprovability',
        })
    for name, text in files.items():
        (tree/(name+'.v')).write_text(text)
        (out/(name+'.v.snapshot.txt')).write_text(text)
    (out/'Production.v.snapshot.txt').write_text(source)
    # Freeze the single-factor protocol before executing any positive/negative tool.
    (out/'control-protocol.json').write_text(json.dumps(protocol, indent=2)+'\n')
    coq = os.environ.get('COQBIN', '')
    flags = ['-q', '-R', str(ROOT), 'CertiOS', '-Q', str(tree), 'SuccessEntryGate']
    report = {'inputs': inputs, 'checks': {}, 'passed': False,
              'scope': 'each concrete NULL/event entry simultaneously meets the full return root; SELF=255, old=8, new=6, ready and event rows=0/1, OSRunning=1, ISR=1, lock=0; all 11 locals/17 bytes freed; final heap observations; arbitrary IE/stacks/ir',
              'limits': 'no initialization/reachability/shared invariant/unlocked dispatch/whole function allocation/GOOD_OS or source-only clean build credit'}

    def run(label, command):
        start = time.monotonic()
        with (out/(label+'.log')).open('w') as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, timeout=1200)
        row = {'exit_code': result.returncode, 'seconds': time.monotonic()-start, 'log': label+'.log'}
        report['checks'][label] = row
        (out/'result.partial.json').write_text(json.dumps(report, indent=2)+'\n')
        return row

    try:
        for label, path in [('production', SOURCE), ('old-probe', OLD_PROBE), ('probe', PROBE)]:
            assert run(label+'-coqc', [coq+'coqc', '-q', '-R', str(ROOT), 'CertiOS', path])['exit_code'] == 0
        checker = module('check-v293-task-prio-rekey.py')
        report['probe_assumptions'] = checker.checked_assumptions((out/'probe-coqc.log').read_text(), 2)
        for label, name in [('production', 'certiucos.v293.proofs.V293CriticalReturn'),
                            ('probe', 'audit.probes.V293SuccessEntryWitnessProbe')]:
            assert run(label+'-coqchk', [coq+'coqchk', '-silent', '-R', str(ROOT), 'CertiOS', 'CertiOS.'+name])['exit_code'] == 0
        for label in ['FrozenPrefix', 'PositiveRoots', 'PositiveNull', 'PositiveEvent']:
            assert run(label, [coq+'coqc', *flags, str(tree/(label+'.v'))])['exit_code'] == 0
            if label.startswith('Positive'):
                report.setdefault('positive_assumptions', {})[label] = checker.checked_assumptions(
                    (out/(label+'.log')).read_text(), 2 if label == 'PositiveRoots' else 1)
        assert run('PositiveRoots-coqchk', [coq+'coqchk', '-silent', '-R', str(ROOT), 'CertiOS',
                                          '-Q', str(tree), 'SuccessEntryGate', 'SuccessEntryGate.PositiveRoots'])['exit_code'] == 0
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
