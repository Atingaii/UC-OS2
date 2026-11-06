#!/usr/bin/env python3
"""Check real entry guards to call boundaries; not the port or a full API proof.

Expected types/AST are handwritten in the probe. Single-header controls import
only a freshly compiled pre-extension prefix, never the candidate new roots.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
CODE = 'certiucos/v293/code/V293OSTaskChangePrio.v'
PROOF = 'certiucos/v293/proofs/V293TaskPrioRekey.v'
PROBE = 'audit/probes/V293TaskPrioErrorEntryProbe.v'
MARKER = '\n(* Compose a skip-terminating prefix with an arbitrary real suffix'
ROOTS = ['V293_task_prio_occupied_entry_execution',
         'V293_task_prio_absent_entry_execution',
         'V293_task_prio_reserved_entry_error_execution',
         'V293_task_prio_absent_same_slot_witness',
         'V293_task_prio_reserved_error_witness',
         'V293_task_prio_occupied_error_witness']


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / name)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def changed_header(source, root, old, new):
    """One prospective mutation; preserve every byte from Proof. onward."""
    start = source.index('Theorem ' + root + ' :')
    end = source.index('Proof.', start)
    header = source[start:end]
    assert header.count(old) == 1
    return source[:start] + header.replace(old, new) + source[end:]


def controls(source):
    return [
        ('OccupiedNull', changed_header(source, ROOTS[0],
            'Some (Vptr next) ->', 'Some (let unused := Vptr next in Vnull) ->'), ROOTS[0],
         'only occupied-slot load value changed to NULL; a reducible unused let preserves next type inference'),
        ('AbsentReturn40', changed_header(source, ROOTS[1],
            'Int.repr 41', 'Int.repr 40'), ROOTS[1],
         'only absent final return continuation changed'),
        ('ReservedOffsetOne', changed_header(source, ROOTS[2],
            'Some (Vptr (br,Int.zero)) ->', 'Some (Vptr (br,Int.one)) ->'), ROOTS[2],
         'only original table-slot token offset changed; may reject before guard'),
        ('ReservedReturn41', changed_header(source, ROOTS[2],
            'Int.repr 67', 'Int.repr 41'), ROOTS[2],
         'only reserved final return continuation changed'),
    ]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path)
    args = parser.parse_args()
    out = args.output_dir or ROOT / 'audit/logs/stage26-task-prio-error-entry' / time.strftime('run-%Y%m%d-%H%M%S')
    out.mkdir(parents=True, exist_ok=False)
    coq = os.environ.get('COQBIN', '')
    inputs = {p: sha(ROOT / p) for p in [CODE, PROOF, PROBE,
        'scripts/check-v293-task-prio-error-entry.py', 'scripts/check-v293-critical-args.py',
        'scripts/check-v293-task-prio-rekey.py']}
    checks = {}
    report = {'inputs': inputs, 'checks': checks, 'scope': 'entry93-to-sfexec; no port/return/GOOD_OS credit'}

    def run(label, command):
        start = time.monotonic()
        with (out / (label + '.log')).open('w') as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT,
                                    timeout=600, env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
        row = {'exit_code': result.returncode, 'elapsed_seconds': time.monotonic()-start,
               'log': label + '.log'}
        checks[label] = row
        (out / 'result.partial.json').write_text(json.dumps(report, indent=2)+'\n')
        return row

    proof = (ROOT / PROOF).read_text()
    assert proof.count(MARKER) == 1
    prefix, suffix = proof.split(MARKER)
    suffix = MARKER + suffix
    assert all(root not in prefix for root in ROOTS)
    # Reuse only imports/scope from the existing file, not its new theorems.
    imports = prefix[:prefix.index('Definition V293_bytes_writable')]
    imports += '\nRequire Import ErrorEntryControls.Baseline.\n'
    positive = imports + suffix
    cases = controls(positive)  # Freeze controls before running the positive.
    (out / 'control-protocol.json').write_text(json.dumps([
        {'label': label, 'target': root, 'change': change, 'downstream_credit': False}
        for label, _, root, change in cases], indent=2)+'\n')
    w = Path(tempfile.mkdtemp(prefix='v293-error-entry-controls-'))
    try:
        fresh = module('check-v293-critical-args.py')
        (out / 'fresh-c-identity.json').write_text(json.dumps(fresh.configured_calls(), indent=2)+'\n')
        fresh.check_model((ROOT / CODE).read_text())
        checks['fresh-c-mapping'] = {'exit_code': 0, 'not_a_verified_frontend': True}
        assert run('main-proof-coqc', [coq+'coqc', '-q', '-R', str(ROOT), 'CertiOS', PROOF])['exit_code'] == 0
        assert run('probe-coqc', [coq+'coqc', '-q', '-R', str(ROOT), 'CertiOS', PROBE])['exit_code'] == 0
        for name, path in [('code', 'certiucos.v293.code.V293OSTaskChangePrio'),
                           ('proof', 'certiucos.v293.proofs.V293TaskPrioRekey'),
                           ('probe', 'audit.probes.V293TaskPrioErrorEntryProbe')]:
            assert run(name+'-coqchk', [coq+'coqchk', '-silent', '-R', str(ROOT), 'CertiOS', 'CertiOS.'+path])['exit_code'] == 0
        checker = module('check-v293-task-prio-rekey.py')
        report['probe_assumptions'] = checker.checked_assumptions((out/'probe-coqc.log').read_text(), 7)
        (w/'Baseline.v').write_text(prefix)
        flags = ['-q', '-R', str(ROOT), 'CertiOS', '-Q', str(w), 'ErrorEntryControls']
        assert run('fixed-prefix-coqc', [coq+'coqc', *flags, str(w/'Baseline.v')])['exit_code'] == 0
        report['controls_dependency'] = {'prefix_sha256': sha(w/'Baseline.v'),
            'new_roots_in_prefix': False, 'imports_candidate_proof': False}
        (w/'Positive.v').write_text(positive+'\n'+''.join('Print Assumptions '+root+'.\n' for root in ROOTS))
        assert run('isolated-positive', [coq+'coqc', *flags, str(w/'Positive.v')])['exit_code'] == 0
        report['positive_assumptions'] = checker.checked_assumptions((out/'isolated-positive.log').read_text(), 6)
        for label, source, root, change in cases:
            p = w/(label+'.v')
            p.write_text(source)
            target_proof_line = source[:source.index('Proof.', source.index('Theorem '+root+' :'))].count('\n')+1
            row = run('negative-'+label, [coq+'coqc', *flags, str(p)])
            match = re.search(r'line (\d+)', (out/row['log']).read_text())
            assert row['exit_code'] == 1 and match and int(match[1]) > target_proof_line, row
            row.update(target=root, target_proof_line=target_proof_line,
                       error_line=int(match[1]), change=change, downstream_credit=False)
        report['passed'] = True
    finally:
        manifest = [{'path': str(p), 'size': p.stat().st_size, 'sha256': sha(p)}
                    for p in sorted(w.rglob('*')) if p.is_file()]
        (out/'temporary-cleanup.json').write_text(json.dumps(manifest, indent=2)+'\n')
        for row in manifest:
            p = Path(row['path'])
            assert p.stat().st_size == row['size'] and sha(p) == row['sha256']
        shutil.rmtree(w)
        report['temporary_tree_removed'] = not w.exists()
        report['inputs_unchanged'] = inputs == {p: sha(ROOT/p) for p in inputs}
        (out/'result.json').write_text(json.dumps(report, indent=2)+'\n')
    assert report['inputs_unchanged']
    print(json.dumps({'passed': report['passed'], 'output_dir': str(out)}, indent=2))


if __name__ == '__main__':
    main()
