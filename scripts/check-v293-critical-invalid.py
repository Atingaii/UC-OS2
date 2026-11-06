#!/usr/bin/env python3
"""Check early 42 guard/free/caller execution, not whole-API or GOOD_OS."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time
import importlib.util

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293CriticalReturn.v'
PROBE = 'audit/probes/V293CriticalInvalidProbe.v'
ERROR = 'V293_invalid_critical_return'
ROOTS = ['V293_evaluated_return_execution', ERROR, 'V293_invalid_critical_witness']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT/'scripts'/name)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def projection(source):
    definitions = source[:source.index('Theorem V293_critical_prefix_normalization :')]
    closure = source[source.index('(* Standard reflexive/transitive closure'):
                     source.index('(* Same program for both initial IE states;')]
    additions = source[source.index('(* Complete a return whose expression has ALREADY') :]
    return module('check-v293-critical-elaboration.py').through_qed(definitions+closure+additions, ERROR)


def controls(source):
    focused = projection(source)
    start = focused.index('Theorem '+ERROR+' :')
    proof = focused.index('Proof.', start)
    a, h, p = focused[:start], focused[start:proof], focused[proof:]
    replace = module('check-v293-critical-elaboration.py').replace_once
    edits = [
        ('WrongReturn', '(Int.repr 42)', '(Int.repr 43)'),
        ('AdmitValidOld', '12 <= old', '0 <= old'),
        ('WrongIE', '((ge,caller,Mf),ir,(enabled,si,ci))', '((ge,caller,Mf),ir,(negb enabled,si,ci))'),
        ('NoWritable', '(forall c t, In (c,t) (getaddr le) -> V293_bytes_writable M c 0%Z (typelen t))', 'True'),
    ]
    result = []
    for label, old, new in edits:
        changed = a+replace(h, old, new)+p
        assert changed[changed.index('Proof.', changed.index('Theorem '+ERROR+' :')):] == p
        assert 'Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn' not in changed
        result.append((label, changed, ERROR, focused))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    out = parser.parse_args().output_dir.resolve()
    out.mkdir(parents=True, exist_ok=False)
    base = module('check-v293-critical-elaboration.py')
    checker = module('check-v293-task-prio-rekey.py')
    source = (ROOT/SOURCE).read_text()
    inputs = {str(p.relative_to(ROOT)): sha(p) for d in ['framework', 'tactics', 'certiucos/v293']
              for p in sorted((ROOT/d).rglob('*.v'))}
    for path in [PROBE, '_CoqProject', 'scripts/check-v293-critical-invalid.py',
                 'scripts/check-v293-critical-elaboration.py', 'scripts/check-v293-task-prio-rekey.py',
                 'csrc/repairs/FROZEN_SOURCE.json', 'audit/coverage.json']:
        inputs[path] = sha(ROOT/path)
    tree = Path(tempfile.mkdtemp(prefix='v293-critical-invalid-'))
    positives = [('PositiveFull', source, ROOTS), ('PositiveGuard', projection(source), [ERROR])]
    cases = controls(source)
    protocol = []
    for label, s, roots in positives:
        s += '\n'+''.join('Print Assumptions '+r+'.\n' for r in roots)
        (tree/(label+'.v')).write_text(s)
        (out/(label+'.v.snapshot.txt')).write_text(s)
    for label, s, target, original in cases:
        (tree/(label+'.v')).write_text(s)
        (out/(label+'.v.snapshot.txt')).write_text(s)
        protocol.append({'label': label, 'target': target,
                         'target_proof_line': s[:s.index('Proof.', s.index('Theorem '+target+' :'))].count('\n')+1,
                         'sha256': sha(tree/(label+'.v')), 'proof_suffix_unchanged': True,
                         'downstream_credit': False})
    (out/'control-protocol.json').write_text(json.dumps(protocol, indent=2)+'\n')
    report = {'inputs': inputs, 'checks': {}, 'passed': False,
              'scope': '42 local finite path; NOT raw-port execution, concurrency, initialization, whole API or GOOD_OS',
              'dependencies': 'existing products, no clean-build credit'}
    coq = os.environ.get('COQBIN', '')
    def run(label, command):
        start = time.monotonic()
        with (out/(label+'.log')).open('w') as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, timeout=600)
        row = {'exit_code': result.returncode, 'seconds': time.monotonic()-start, 'log': label+'.log'}
        report['checks'][label] = row
        (out/'result.partial.json').write_text(json.dumps(report, indent=2)+'\n')
        return row
    try:
        for label, path in [('production', SOURCE), ('probe', PROBE)]:
            assert run(label+'-coqc', [coq+'coqc', '-q', '-R', str(ROOT), 'CertiOS', path])['exit_code'] == 0
        report['probe_assumptions'] = checker.checked_assumptions((out/'probe-coqc.log').read_text(), 3)
        for label, mod in [('production', 'certiucos.v293.proofs.V293CriticalReturn'),
                           ('probe', 'audit.probes.V293CriticalInvalidProbe')]:
            assert run(label+'-coqchk', [coq+'coqchk', '-silent', '-R', str(ROOT), 'CertiOS', 'CertiOS.'+mod])['exit_code'] == 0
        flags = ['-q', '-R', str(ROOT), 'CertiOS', '-Q', str(tree), 'CriticalInvalidControls']
        report['positive_assumptions'] = {}
        for label, s, roots in positives:
            assert run(label, [coq+'coqc', *flags, str(tree/(label+'.v'))])['exit_code'] == 0
            report['positive_assumptions'][label] = checker.checked_assumptions((out/(label+'.log')).read_text(), len(roots))
        for entry in protocol:
            label = entry['label']
            assert sha(tree/(label+'.v')) == entry['sha256']
            row = run('negative-'+label, [coq+'coqc', *flags, str(tree/(label+'.v'))])
            match = re.search(r'line (\d+)', (out/row['log']).read_text())
            assert row['exit_code'] == 1 and match and int(match[1]) > entry['target_proof_line'], row
            row.update(entry, error_line=int(match[1]))
        report['passed'] = True
    finally:
        base.cleanup(tree, out/'temporary-cleanup.json')
        report['temporary_tree_removed'] = not tree.exists()
        report['inputs_unchanged'] = all(sha(ROOT/p) == h for p,h in inputs.items())
        (out/'result.json').write_text(json.dumps(report, indent=2)+'\n')
    assert report['inputs_unchanged']
    print(json.dumps({'passed': report['passed'], 'checks': len(report['checks']), 'output_dir': str(out)}, indent=2))


if __name__ == '__main__':
    main()
