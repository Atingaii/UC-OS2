#!/usr/bin/env python3
"""Check selected TCB spatial ownership; no API-preservation/GOOD_OS credit."""
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
PROBE = 'audit/probes/V293TaskRecordOwnershipProbe.v'
BASE = 'audit/logs/stage26-task-ownership/baseline.json'
ROOTS = ['V293_owned_record_cell_store', 'V293_owned_task_record_sound', 'V293_owned_task_records_sound',
         'V293_shared_task_records_sound']
PROBE_ROOTS = ['OwnershipContract', 'SharedOwnershipContract', 'OwnershipLiteralSpatial',
               'OwnershipLiteralRecords', 'OwnershipLiteralFields', 'OwnershipSharedLiteralSpatial',
               'OwnershipSharedLiteralRecords', 'OwnershipReadableNotWritable']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def helper(filename):
    spec = importlib.util.spec_from_file_location(filename, ROOT / 'scripts' / filename)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def controls(source):
    # A separate module re-elaborates all definitions and proofs and never
    # imports the candidate module. The old raw-record relation is unchanged.
    assert 'Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.' not in source
    factors = {
        'DroppedPhysicalCell': ('[| rule_type_val_match tp v = true |] ** Amapsto a tp true v.',
                                '[| rule_type_val_match tp v = true |] ** Aemp.'),
        'WrongPriorityOffset': ('[ (a 50%Z,Tint8,V293_byteval p);',
                                '[ (a 55%Z,Tint8,V293_byteval p);'),
    }
    negative = {}
    for name, (old, new) in factors.items():
        assert source.count(old) == 1
        negative[name] = source.replace(old, new, 1)
        # All lemma/theorem statements and every proof are kept, byte for byte.
        suffix = source.index('Lemma V293_record_star_load_l')
        assert negative[name][negative[name].index('Lemma V293_record_star_load_l'):] == source[suffix:]
    return negative


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    out = parser.parse_args().output_dir.resolve()
    out.mkdir(parents=True, exist_ok=False)
    source = (ROOT / SOURCE).read_text()
    negative = controls(source)
    baseline = json.loads((ROOT / BASE).read_text())
    assert all(sha(ROOT / p) == h for p, h in baseline['active'].items())
    assert all(sha(ROOT / p) == h for p, h in baseline['protected'].items() if p != '_CoqProject')
    before = ROOT / 'audit/logs/stage26-task-ownership/Before_CoqProject.snapshot.txt'
    assert sha(before) == baseline['protected']['_CoqProject']
    assert (ROOT / '_CoqProject').read_bytes() == before.read_bytes() + b'\ncertiucos/v293/proofs/V293TaskRecordOwnership.v\n'
    inputs = {str(p.relative_to(ROOT)): sha(p) for d in ['framework', 'tactics', 'certiucos/v293']
              for p in (ROOT / d).rglob('*.v')}
    helpers = ['check-v293-task-prio-rekey.py', 'check-v293-critical-elaboration.py']
    for p in [PROBE, BASE, '_CoqProject', *baseline['protected'],
              'audit/logs/stage26-task-ownership/protocol.json',
              'audit/logs/stage26-task-ownership/Before_CoqProject.snapshot.txt',
              'audit/logs/stage26-task-ownership/build-registration-protocol.json',
              'scripts/check-v293-task-ownership.py', *('scripts/' + n for n in helpers)]:
        inputs[p] = sha(ROOT / p)
    tree = Path(tempfile.mkdtemp(prefix='v293-task-ownership-'))
    printing = ''.join('\nPrint Assumptions ' + n + '.\n' for n in ROOTS)
    for name, data in {'Positive': source + printing, **negative}.items():
        (tree / (name + '.v')).write_text(data)
        (out / (name + '.v.snapshot.txt')).write_text(data)
    for p, name in [(SOURCE, 'Production'), (PROBE, 'Probe')]:
        (out / (name + '.v.snapshot.txt')).write_bytes((ROOT / p).read_bytes())
    protocol = {name: {'single_factor': name, 'all_lemma_statement_and_proof_suffix_unchanged': True,
                      'downstream_credit': False, 'negative_sha256': sha(tree / (name + '.v')),
                      'target_proof_line': source[:source.index('Proof.', source.index(
                          'Lemma V293_owned_record_cell_load' if name == 'DroppedPhysicalCell'
                          else 'Lemma V293_record_layout_sound'))].count('\n') + 1}
                for name in negative}
    (out / 'control-protocol.json').write_text(json.dumps(protocol, indent=2) + '\n')
    report = {'inputs': inputs, 'checks': [], 'passed': False,
              'limits': 'Selected field ownership only; no complete invariant, API/ISR preservation, initialization or GOOD_OS credit.'}
    prefix = os.environ.get('COQBIN', '')
    flags = ['-q', '-R', str(ROOT), 'CertiOS', '-Q', str(tree), 'OwnershipGate']

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
                             ('Probe', 'CertiOS.audit.probes.V293TaskRecordOwnershipProbe'),
                             ('Positive', 'OwnershipGate.Positive')]:
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
