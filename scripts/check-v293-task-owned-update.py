#!/usr/bin/env python3
"""Check framed TCB stores and the actual five-assignment execution; no whole API/GOOD_OS credit."""
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
SOURCE = 'certiucos/v293/proofs/V293TaskRecordOwnership.v'
PROBE = 'audit/probes/V293TaskOwnedUpdateProbe.v'
FIXTURE = 'audit/probes/V293TaskRecordOwnershipProbe.v'
BASE = 'audit/logs/stage26-task-owned-update/baseline.json'
ROOTS = ['V293_owned_record_cell_update', 'V293_owned_cells_byte_update',
         'V293_owned_task_record_update', 'V293_task_prio_tcb_owned_execution']
PROBE_ROOTS = ['OwnedCellUpdateContract', 'OwnedTaskUpdateContract', 'UpdateEntrySpatial',
               'UpdateLiteralExecution', 'UpdateFinalPriority', 'UpdateFinalFrameLoads',
               'UpdateRejectsStaleOwnership']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def helper(filename):
    spec = importlib.util.spec_from_file_location(filename, ROOT / 'scripts' / filename)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def controls(source):
    assert 'Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.' not in source
    factors = {
        'StaleCellValue': ('Lemma V293_owned_record_cell_update',
            'V293_owned_record_cell (a,tp,replacement) ** R.',
            'V293_owned_record_cell (a,tp,old) ** R.'),
        'StaleTaskPriority': ('Theorem V293_owned_task_record_update',
            'V293_owned_task_record t (Int.repr (Z.of_nat new)) status message ** R.',
            'V293_owned_task_record t priority status message ** R.'),
    }
    negative = {}
    for name, (root, old, new) in factors.items():
        start = source.index(root)
        proof = source.index('Proof.', start)
        header = source[start:proof]
        assert header.count(old) == 1
        changed = header.replace(old, new, 1)
        negative[name] = source[:start] + changed + source[proof:]
        assert negative[name][negative[name].index('Proof.', start):] == source[proof:]
    return negative


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    out = parser.parse_args().output_dir.resolve()
    out.mkdir(parents=True, exist_ok=False)
    source = (ROOT / SOURCE).read_text()
    negative = controls(source)
    baseline = json.loads((ROOT / BASE).read_text())
    assert all(sha(ROOT / p) == h for p, h in baseline['sources'].items() if p != SOURCE)
    assert all(sha(ROOT / p) == h for p, h in baseline['protected'].items())
    before = ROOT / 'audit/logs/stage26-task-owned-update/Before_Ownership.v.snapshot.txt'
    assert sha(before) == baseline['sources'][SOURCE]
    assert (ROOT / SOURCE).read_bytes().startswith(before.read_bytes())
    inputs = {str(p.relative_to(ROOT)): sha(p) for d in ['framework', 'tactics', 'certiucos/v293']
              for p in (ROOT / d).rglob('*.v')}
    helpers = ['check-v293-task-prio-rekey.py', 'check-v293-critical-elaboration.py']
    for p in [PROBE, FIXTURE, BASE, '_CoqProject', *baseline['protected'],
              'audit/logs/stage26-task-owned-update/protocol.json',
              'audit/logs/stage26-task-owned-update/Before_Ownership.v.snapshot.txt',
              'scripts/check-v293-task-owned-update.py', *('scripts/' + n for n in helpers)]:
        inputs[p] = sha(ROOT / p)
    tree = Path(tempfile.mkdtemp(prefix='v293-task-owned-update-'))
    printing = ''.join('\nPrint Assumptions ' + n + '.\n' for n in ROOTS)
    for name, data in {'Positive': source + printing, **negative}.items():
        (tree / (name + '.v')).write_text(data)
        (out / (name + '.v.snapshot.txt')).write_text(data)
    for p, name in [(SOURCE, 'Production'), (PROBE, 'Probe')]:
        (out / (name + '.v.snapshot.txt')).write_bytes((ROOT / p).read_bytes())
    protocol = {name: {'single_factor': name, 'entire_target_proof_suffix_unchanged': True,
                      'downstream_credit': False, 'negative_sha256': sha(tree / (name + '.v')),
                      'target_proof_line': source[:source.index('Proof.', source.index(
                          'Lemma V293_owned_record_cell_update' if name == 'StaleCellValue'
                          else 'Theorem V293_owned_task_record_update'))].count('\n') + 1}
                for name in negative}
    (out / 'control-protocol.json').write_text(json.dumps(protocol, indent=2) + '\n')
    report = {'inputs': inputs, 'checks': [], 'passed': False,
              'limits': 'Actual five TCB assignments with an arbitrary unchanged spatial frame, not whole API/ISR preservation or initialization/GOOD_OS.'}
    prefix = os.environ.get('COQBIN', '')
    flags = ['-q', '-R', str(ROOT), 'CertiOS', '-Q', str(tree), 'OwnedUpdateGate']

    def run(name, command, expected=0):
        start = time.monotonic()
        with (out / (name + '.log')).open('w') as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, timeout=1800)
        item = {'name': name, 'command': command, 'exit_code': result.returncode,
                'expected_exit_code': expected, 'seconds': time.monotonic() - start}
        report['checks'].append(item)
        (out / 'result.partial.json').write_text(json.dumps(report, indent=2) + '\n')
        assert result.returncode == expected, item
        return item

    try:
        run('Production', [prefix + 'coqc', *flags, str(ROOT / SOURCE)])
        run('Positive', [prefix + 'coqc', *flags, str(tree / 'Positive.v')])
        run('Fixture', [prefix + 'coqc', *flags, str(ROOT / FIXTURE)])
        run('Probe', [prefix + 'coqc', *flags, str(ROOT / PROBE)])
        assumptions = helper(helpers[0]).checked_assumptions
        report['positive_assumptions'] = assumptions((out / 'Positive.log').read_text(), len(ROOTS))
        report['probe_assumptions'] = assumptions((out / 'Probe.log').read_text(), len(PROBE_ROOTS))
        for name in negative:
            item = run(name, [prefix + 'coqc', *flags, str(tree / (name + '.v'))], 1)
            error = re.search(r'line (\d+)', (out / (name + '.log')).read_text())
            assert error and int(error[1]) > protocol[name]['target_proof_line']
            item.update(protocol[name], error_line=int(error[1]))
        for name, module in [('Production', 'CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership'),
                             ('Probe', 'CertiOS.audit.probes.V293TaskOwnedUpdateProbe'),
                             ('Positive', 'OwnedUpdateGate.Positive')]:
            run(name + '-coqchk', [prefix + 'coqchk', '-silent', *flags[1:], module])
        report['passed'] = True
    finally:
        helper(helpers[1]).cleanup(tree, out / 'temporary-cleanup.json')
        report['temporary_tree_removed'] = not tree.exists()
        report['inputs_unchanged'] = all(sha(ROOT / p) == h for p, h in inputs.items())
        (out / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
    assert report['inputs_unchanged']
    print(json.dumps({'passed': report['passed'], 'checks': len(report['checks']), 'inputs': len(inputs)}))


if __name__ == '__main__':
    main()
