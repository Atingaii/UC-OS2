#!/usr/bin/env python3
"""Current pointer, all task selected fields and ready/event bytes jointly owned on one success return; no GOOD_OS credit."""
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
PROBE = 'audit/probes/V293JointReturnProbe.v'
BASE = 'audit/logs/stage26-joint-return/baseline.json'
PREFIX = 'audit/logs/stage26-joint-return/Before_Ownership.v.snapshot.txt'
PROTOCOL = 'audit/logs/stage26-joint-return/protocol.json'
ROOTS = ['V293_current_tasks_bytes_joint', 'V293_owned_cells_abstract_empty',
         'V293_current_tasks_bytes_fields_reconstruct', 'V293_critical_wait_joint_owned_execution']
PROBE_ROOTS = ['UnifiedEntryFull', 'UnifiedOwnedFullReturn', 'UnifiedFinalReadAndWritable',
               'UnifiedRejectsWrongCurrent', 'UnifiedRejectsOldCanonical', 'UnifiedUseAllResources',
               'UnifiedBitmapStorePreservesJoint']
FIXTURES = ['V293SuccessCompleteReturnProbe','V293SuccessEntryWitnessProbe','V293ReadyGeneralEntryProbe',
            'V293WaitEventOwnedProbe','V293WaitPayloadProbe','V293EventQueueProbe','V293EventTypeProbe',
            'V293EventReturnFrameProbe','V293EventDataProbe','V293CurrentConsistencyProbe',
            'V293CurrentOwnershipProbe','V293TaskRecordsProbe','V293TaskRecordOwnershipProbe','V293ApiTaskOwnershipProbe','V293AllTaskOwnershipProbe','V293CurrentAllOwnershipProbe','V293BitmapOwnershipProbe']
HELPERS = ['check-v293-task-prio-rekey.py', 'check-v293-critical-elaboration.py']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def helper(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / name)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


CONTROL_ROOTS = {
    'PointerOverlapAllowed': 'Lemma V293_current_tasks_bytes_joint',
    'StaleJointEvent': 'Theorem V293_critical_wait_joint_owned_execution',
}


def controls(source):
    assert 'Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.' not in source
    factors = {
        'PointerOverlapAllowed': (
            '  (forall a n b tp, In (a,n) cells -> get ge OSTCBCur = Some (b,Tptr tp) -> fst a <> b) ->\n', ''),
        'StaleJointEvent': (
            '(fst (V293_ready_rekey_rows elo ehi old new)) (snd (V293_ready_rekey_rows elo ehi old new))',
            'elo ehi'),
    }
    negative = {}
    for name, (before, after) in factors.items():
        a = source.index(CONTROL_ROOTS[name])
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
              'scripts/check-v293-joint-return.py',
              *('scripts/' + x for x in HELPERS),
              *('audit/probes/' + x + '.v' for x in FIXTURES)]:
        inputs[p] = sha(ROOT / p)
    tree = Path(tempfile.mkdtemp(prefix='v293-joint-return-'))
    prints = ''.join('\nPrint Assumptions ' + n + '.\n' for n in ROOTS)
    for name, content in {'Positive': source + prints, **negative}.items():
        (tree / (name + '.v')).write_text(content)
        (out / (name + '.v.snapshot.txt')).write_text(content)
    for p, name in [(SOURCE, 'Production'), (PROBE, 'Probe')]:
        (out / (name + '.v.snapshot.txt')).write_bytes((ROOT / p).read_bytes())
    factors = {name: {'single_factor': name, 'entire_proof_suffix_unchanged': True,
                      'downstream_credit': False, 'negative_sha256': sha(tree / (name + '.v')),
                      'proof_line': negative[name][:negative[name].index('Proof.', negative[name].index(
                          CONTROL_ROOTS[name]))].count('\n') + 1}
               for name in negative}
    (out / 'control-protocol.json').write_text(json.dumps(factors, indent=2) + '\n')
    report = {'inputs': inputs, 'checks': [], 'passed': False,
              'limits': 'One concrete blocked success return jointly owns current pointer, all canonical selected task fields, ready/event bytes and abstract shared_fields; no full priority-table ownership, fullInv, initialization, ISR, all API entries, unlocked scheduler, GOOD_OS, K1-K4 or uCOS3 credit.'}
    prefix = os.environ.get('COQBIN', '')
    flags = ['-q', '-R', str(ROOT), 'CertiOS', '-Q', str(tree), 'JointReturnGate']

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
        for fixture in FIXTURES:
            check('Fixture-' + fixture, [prefix + 'coqc', *flags, str(ROOT / 'audit/probes' / (fixture + '.v'))])
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
                   ('Probe', 'CertiOS.audit.probes.V293JointReturnProbe'),
                   ('Positive', 'JointReturnGate.Positive')]
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
        # Confirm the entire disposable tree before the first deletion.
        rows = [{'path': str(p), 'category': 'isolated gate source and Coq products; source snapshots retained',
                 'size': p.stat().st_size, 'sha256': sha(p)}
                for p in sorted(tree.rglob('*')) if p.is_file()]
        (out / 'temporary-cleanup-plan.json').write_text(json.dumps(rows, indent=2) + '\n')
        assert all(Path(row['path']).stat().st_size == row['size'] and
                   sha(Path(row['path'])) == row['sha256'] for row in rows)
        helper(HELPERS[1]).cleanup(tree, out / 'temporary-cleanup.json')
        report['temporary_tree_removed'] = not tree.exists()
        report['inputs_unchanged'] = all(sha(ROOT / p) == h for p, h in inputs.items())
        (out / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
    assert report['inputs_unchanged']
    print(json.dumps({'passed': report['passed'], 'checks': len(report['checks']), 'inputs': len(inputs)}))


if __name__ == '__main__':
    main()
