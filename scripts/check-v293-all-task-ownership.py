#!/usr/bin/env python3
"""Same full success-return physical ownership and abstract rekey; no GOOD_OS credit."""
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

ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'certiucos/v293/proofs/V293TaskRecordOwnership.v'
PROBE = 'audit/probes/V293AllTaskOwnershipProbe.v'
BASE = 'audit/logs/stage26-all-task-ownership/baseline.json'
PREFIX = 'audit/logs/stage26-all-task-ownership/Before_Ownership.v.snapshot.txt'
PROTOCOL = 'audit/logs/stage26-all-task-ownership/protocol.json'
ROOTS = ['V293_owned_task_records_update', 'V293_owned_task_records_block_frame',
         'V293_owned_tasks_fields_reconstruct', 'V293_critical_wait_all_records_owned_execution']
PROBE_ROOTS = ['AllEntryJoint', 'AllOwnedFullReturn', 'AllRejectsOldCanonical', 'AllFinalBothWritable']
FIXTURES = ['V293SuccessCompleteReturnProbe','V293SuccessEntryWitnessProbe','V293ReadyGeneralEntryProbe',
            'V293WaitEventOwnedProbe','V293WaitPayloadProbe','V293EventQueueProbe','V293EventTypeProbe',
            'V293EventReturnFrameProbe','V293EventDataProbe','V293CurrentConsistencyProbe',
            'V293CurrentOwnershipProbe','V293TaskRecordsProbe','V293TaskRecordOwnershipProbe','V293ApiTaskOwnershipProbe']
HELPERS = ['check-v293-task-prio-rekey.py', 'check-v293-critical-elaboration.py']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def helper(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / name)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def controls(source):
    assert 'Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.' not in source
    safety = '(forall t value, get tasks t = Some value -> fst t <> bt ->\n    ~ In (fst t) (map fst (getaddr le)) /\\\n    ~ In (fst t) [bo;bc;b;dy;dby;dx;br;bg;bp;be;ny;bi;nby;nbx]) ->'
    post = 'V293_owned_task_records\n      (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat new),wait reason delay,message)) **'
    factors = {
        'DroppedOtherTaskFrame': ('Theorem V293_critical_wait_all_records_owned_execution', safety, 'True ->'),
        'StaleCanonicalTaskMap': ('Theorem V293_critical_wait_all_records_owned_execution', post, 'V293_owned_task_records tasks **'),
    }
    negative = {}
    for name, (root, before, after) in factors.items():
        a = source.index(root)
        b = source.index('Proof.', a)
        header = source[a:b]
        assert header.count(before) == 1
        negative[name] = source[:a] + header.replace(before, after, 1) + source[b:]
        assert negative[name][negative[name].index('Proof.', a):] == source[b:]
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
    assert sha(ROOT / PREFIX) == baseline['sources'][SOURCE]
    assert (ROOT / SOURCE).read_bytes().startswith((ROOT / PREFIX).read_bytes())
    inputs = {p: sha(ROOT / p) for p in baseline['sources']}
    for p in [PROBE, BASE, PREFIX, PROTOCOL, *baseline['protected'],
              'scripts/check-v293-all-task-ownership.py',
              *('scripts/' + x for x in HELPERS),
              *('audit/probes/' + x + '.v' for x in FIXTURES)]:
        inputs[p] = sha(ROOT / p)
    tree = Path(tempfile.mkdtemp(prefix='v293-all-task-ownership-'))
    prints = ''.join('\nPrint Assumptions ' + n + '.\n' for n in ROOTS)
    for name, content in {'Positive': source + prints, **negative}.items():
        (tree / (name + '.v')).write_text(content)
        (out / (name + '.v.snapshot.txt')).write_text(content)
    for p, name in [(SOURCE, 'Production'), (PROBE, 'Probe')]:
        (out / (name + '.v.snapshot.txt')).write_bytes((ROOT / p).read_bytes())
    factors = {name: {'single_factor': name, 'entire_proof_suffix_unchanged': True,
                      'downstream_credit': False, 'negative_sha256': sha(tree / (name + '.v')),
                      'proof_line': source[:source.index('Proof.', source.index(
                          'Theorem V293_critical_wait_all_records_owned_execution'))].count('\n') + 1}
               for name in negative}
    (out / 'control-protocol.json').write_text(json.dumps(factors, indent=2) + '\n')
    report = {'inputs': inputs, 'checks': [], 'passed': False,
              'limits': 'Full canonical selected-field resources and same actual success return/map update; blocked scheduler, no full shared invariant, initialization, ISR, all API entries, GOOD_OS or uCOS3 credit.'}
    prefix = os.environ.get('COQBIN', '')
    flags = ['-q', '-R', str(ROOT), 'CertiOS', '-Q', str(tree), 'AllTaskOwnedGate']

    def run(name, command, expected=0):
        start = time.monotonic()
        with (out / (name + '.log')).open('w') as log:
            proc = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, timeout=1800)
        return {'name': name, 'command': command, 'exit_code': proc.returncode,
                'expected_exit_code': expected, 'seconds': time.monotonic() - start}

    def check(name, command, expected=0):
        item = run(name, command, expected)
        report['checks'].append(item)
        (out / 'result.partial.json').write_text(json.dumps(report, indent=2) + '\n')
        assert item['exit_code'] == expected, item
        return item

    try:
        check('Production', [prefix + 'coqc', *flags, str(ROOT / SOURCE)])
        # Production must finish before a probe imports its .vo. Independent
        # isolated positive/negative files may then be checked concurrently.
        jobs = [('Positive', [prefix + 'coqc', *flags, str(tree / 'Positive.v')], 0),
                ('Probe', [prefix + 'coqc', *flags, str(ROOT / PROBE)], 0)]
        jobs += [(name, [prefix + 'coqc', *flags, str(tree / (name + '.v'))], 1) for name in negative]
        with ThreadPoolExecutor(max_workers=3) as pool:
            futures = [pool.submit(run, name, cmd, expected) for name, cmd, expected in jobs]
            for future in futures:
                item = future.result()
                report['checks'].append(item)
                (out / 'result.partial.json').write_text(json.dumps(report, indent=2) + '\n')
                assert item['exit_code'] == item['expected_exit_code'], item
                if item['name'] in negative:
                    name = item['name']
                    error = re.search(r'line (\d+)', (out / (name + '.log')).read_text())
                    assert error and int(error[1]) > factors[name]['proof_line']
                    item.update(factors[name], error_line=int(error[1]))
        assumptions = helper(HELPERS[0]).checked_assumptions
        report['positive_assumptions'] = assumptions((out / 'Positive.log').read_text(), len(ROOTS))
        report['probe_assumptions'] = assumptions((out / 'Probe.log').read_text(), len(PROBE_ROOTS))
        modules = [('Production', 'CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership'),
                   ('Probe', 'CertiOS.audit.probes.V293AllTaskOwnershipProbe'),
                   ('Positive', 'AllTaskOwnedGate.Positive')]
        # Independent kernel checks; no agents or delegated proof work.
        with ThreadPoolExecutor(max_workers=3) as pool:
            futures = [pool.submit(run, n + '-coqchk', [prefix + 'coqchk', '-silent', *flags[1:], m])
                       for n, m in modules]
            for future in futures:
                item = future.result()
                report['checks'].append(item)
                assert item['exit_code'] == 0, item
        report['passed'] = True
    finally:
        helper(HELPERS[1]).cleanup(tree, out / 'temporary-cleanup.json')
        report['temporary_tree_removed'] = not tree.exists()
        report['inputs_unchanged'] = all(sha(ROOT / p) == h for p, h in inputs.items())
        (out / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
    assert report['inputs_unchanged']
    print(json.dumps({'passed': report['passed'], 'checks': len(report['checks']), 'inputs': len(inputs)}))


if __name__ == '__main__':
    main()
