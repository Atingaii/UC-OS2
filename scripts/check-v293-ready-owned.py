#!/usr/bin/env python3
"""Check a framed ready primitive paired with one concrete NULL success trace."""
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
PROBE = 'audit/probes/V293ReadyOwnedProbe.v'
PREFIX_BYTES = 302952
PREFIX_SHA = 'fb8047b322b3b9207c3badfcd5570374ffe76c65615e85dfa01a1cdc056eea31'
OWNED = 'V293_ready_prio_owned_step'
BRANCH = 'V293_ready_prio_branch_relations'
COMPLETE = 'V293_critical_ready_owned_success'
ROOTS = [OWNED, BRANCH, COMPLETE, 'V293_ready_prio_stale_bitmap_rejected',
         'V293_ready_prio_moving_not_highest']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT/'scripts'/name)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def declaration(source, name):
    i = source.index('Theorem '+name+' :')
    return source[i:source.index('\nQed.', i)+6]+'\n'


def parts(source):
    raw = source.encode()
    prefix = raw[:PREFIX_BYTES]
    assert hashlib.sha256(prefix).hexdigest() == PREFIX_SHA
    suffix = raw[PREFIX_BYTES:].decode()
    imports = '\n'.join(l for l in prefix.decode().splitlines() if l.startswith('Require Import '))
    harness = ('Require Import ReadyOwnedGate.FrozenPrefix.\n'+imports+
               '\nImport ListNotations.\nLocal Open Scope nat_scope.\nLocal Opaque HalfPermMap.set.\n')
    return prefix.decode(), suffix, harness


def isolated(source, target):
    _, suffix, harness = parts(source)
    i = suffix.index('Theorem '+target+' :')
    return harness+suffix[:i]+declaration(suffix, target)


def controls(source):
    result = []
    for label, target, old, new, first in [
        ('NoAbstractWrite', OWNED,
         "O' = set O abstcblsid (abstcblist\n      (set tasks next (Int.repr (Z.of_nat new),rdy,message)))",
         "O' = O", 'post-state abstract-map identity; not subsequent frame or relation checks'),
        ('ReadyNotUpdated', COMPLETE, "V293_bitmap_tasks 80 0 tasks'",
         "V293_bitmap_tasks 16 1 tasks'", 'post-state bitmap relation; not all earlier mechanisms'),
        ('TableNotUpdated', COMPLETE, "V293_priority_table entries' tasks'",
         "V293_priority_table V293_prefix_fixture_entries tasks'", 'post-state table relation; not all earlier mechanisms'),
    ]:
        original = isolated(source, target)
        i = original.index('Proof.', original.index('Theorem '+target+' :'))
        assert original[:i].count(old) == 1
        changed = original[:i].replace(old, new)+original[i:]
        assert changed[changed.index('Proof.', changed.index('Theorem '+target+' :')):] == original[i:]
        result.append((label, target, changed, original, first))
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
              'audit/probes/V293SuccessEntryWitnessProbe.v', PROBE]
    for p in [*probes, '_CoqProject', 'scripts/check-v293-ready-owned.py',
              'scripts/check-v293-success-entry-witness.py', 'scripts/check-v293-success-complete-return.py',
              'scripts/check-v293-critical-elaboration.py', 'scripts/check-v293-task-prio-rekey.py',
              'csrc/repairs/FROZEN_SOURCE.json', 'audit/coverage.json']:
        inputs[p] = sha(ROOT/p)
    tree = Path(tempfile.mkdtemp(prefix='v293-ready-owned-gate-'))
    files = {'FrozenPrefix': prefix, 'PositiveRoots': harness+suffix}
    positive = {'PositiveRoots': ROOTS}
    for label, name in [('PositiveOwned', OWNED), ('PositiveBranch', BRANCH), ('PositiveComplete', COMPLETE)]:
        files[label] = isolated(source, name)
        positive[label] = [name]
    for label, names in positive.items():
        files[label] += '\n'+''.join('Print Assumptions '+n+'.\n' for n in names)
    protocol = []
    for label, target, changed, original, first in controls(source):
        files[label] = changed
        protocol.append({'label': label, 'target': target, 'sha256': hashlib.sha256(changed.encode()).hexdigest(),
                         'positive_sha256': hashlib.sha256(original.encode()).hexdigest(),
                         'target_proof_line': changed[:changed.index('Proof.', changed.index('Theorem '+target+' :'))].count('\n')+1,
                         'proof_suffix_unchanged': True, 'downstream_credit': False,
                         'intended_obligation': first,
                         'credit': 'fixed-proof sensitivity only; not C mutation or unprovability'})
    for name, content in files.items():
        (tree/(name+'.v')).write_text(content)
        (out/(name+'.v.snapshot.txt')).write_text(content)
    (out/'Production.v.snapshot.txt').write_text(source)
    (out/'Probe.v.snapshot.txt').write_bytes((ROOT/PROBE).read_bytes())
    (out/'control-protocol.json').write_text(json.dumps(protocol, indent=2)+'\n')
    report = {'inputs': inputs, 'checks': {}, 'passed': False,
              'scope': 'general framed ready-only abstract primitive and branch relation; one NULL-event full success fixture paired with owned task update in same final heap; semantic stale-map and wrong-selection counterexamples',
              'limits': 'not full API specification or forward simulation; no ready_inv/full TCB-event invariant, initialization, reachability, normal unlocked scheduler, full function, GOOD_OS or clean-build credit'}
    coq = os.environ.get('COQBIN', '')
    flags = ['-q', '-R', str(ROOT), 'CertiOS', '-Q', str(tree), 'ReadyOwnedGate']

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
        report['probe_assumptions'] = checker.checked_assumptions((out/'V293ReadyOwnedProbe-coqc.log').read_text(), 4)
        for label, name in [('production', 'certiucos.v293.proofs.V293CriticalReturn'),
                            ('probe', 'audit.probes.V293ReadyOwnedProbe')]:
            assert run(label+'-coqchk', [coq+'coqchk', '-silent', '-R', str(ROOT), 'CertiOS', 'CertiOS.'+name])['exit_code'] == 0
        assert run('FrozenPrefix', [coq+'coqc', *flags, str(tree/'FrozenPrefix.v')])['exit_code'] == 0
        for label, names in positive.items():
            assert run(label, [coq+'coqc', *flags, str(tree/(label+'.v'))])['exit_code'] == 0
            report.setdefault('positive_assumptions', {})[label] = checker.checked_assumptions((out/(label+'.log')).read_text(), len(names))
        assert run('PositiveRoots-coqchk', [coq+'coqchk', '-silent', '-R', str(ROOT), 'CertiOS',
                   '-Q', str(tree), 'ReadyOwnedGate', 'ReadyOwnedGate.PositiveRoots'])['exit_code'] == 0
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
