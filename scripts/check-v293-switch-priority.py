#!/usr/bin/env python3
"""Check the bounded switch/current-byte obstruction; never full OS_Sched evidence."""
from __future__ import annotations
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
SOURCE = 'certiucos/v293/proofs/V293SwitchPriorityBoundary.v'
PROBE = 'audit/probes/V293SwitchPriorityBoundaryProbe.v'
_spec = importlib.util.spec_from_file_location('priority_local_checks', ROOT / 'scripts/check-v293-storage-prefix.py')
CHECK = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(CHECK)
ROOT_COUNT = 5
SCOPE = 'BOUNDED_POINTER_ONLY_SWITCH_OBSTRUCTION_NOT_READY_INVARIANT_PORT_OR_GOOD_OS'


def checked_assumptions(output):
    if output.count('Axioms:') != ROOT_COUNT:
        raise ValueError('missing actual root assumption output')
    return CHECK.TRUST.check_assumptions(output, CHECK.TRUST.ALLOWED)


def mutations(source):
    def header(declaration, before, after):
        start = source.index(declaration)
        end = source.index('Proof.', start)
        return (source[:start] + CHECK.replace_once(source[start:end], before, after) + source[end:], declaration)
    store = 'Theorem V293_priority_boundary_pointer_store :'
    sync = 'Theorem V293_priority_boundary_explicit_sync :'
    return {
        'pointer_store_omitted_only': header(store,
            '    Some V293_priority_boundary_pointer_memory /\\',
            '    Some V293_priority_boundary_memory /\\'),
        'preserved_byte_wrong_only': header(store,
            '= Some (V293_byteval 4) /\\', '= Some (V293_byteval 12) /\\'),
        'explicit_sync_omitted_only': header(sync,
            '(V293_priority_boundary_task V293_priority_boundary_synchronized_memory)',
            '(V293_priority_boundary_task V293_priority_boundary_pointer_memory)'),
    }


def main():
    out = ROOT / 'audit/logs/stage26-current-priority' / time.strftime('run-%Y%m%d-%H%M%S')
    out.mkdir(parents=True, exist_ok=False)
    paths = sorted({p.relative_to(ROOT).as_posix()
                    for tree in ['framework', 'tactics', 'certiucos/v293']
                    for p in (ROOT / tree).rglob('*.v')} |
                   {PROBE, 'scripts/check-v293-switch-priority.py', 'scripts/check-v293-storage-prefix.py',
                    'scripts/check-memory-trust.py', 'Makefile', '_CoqProject'})
    identity = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths}
    report = {'scope': SCOPE, 'formal_function_evidence_updated': False,
              'kernel_GOOD_OS_proved': False, 'prebuilt_dependency_closure': True,
              'ready_invariant_entry_acceptance_proved': False,
              'input_sha256': identity, 'checks': {}, 'negative_controls': {}, 'passed': False}
    coqbin = os.environ.get('COQBIN', '')

    def run(label, args):
        result = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=600)
        (out / (label + '.log')).write_text(result.stdout)
        report['checks'][label] = {'exit_code': result.returncode,
                                  'log': str((out / (label + '.log')).relative_to(ROOT))}
        return result.returncode, result.stdout

    def passed(label, args):
        code, output = run(label, args)
        if code:
            raise ValueError(f'{label} failed; inspect {out}')
        return output

    work = None
    try:
        version = passed('version', [coqbin + 'coqc', '--version'])
        if not re.search(r'version 8\.18\.0(?: |$)', version, re.MULTILINE):
            raise ValueError('Coq 8.18.0 required')
        passed('source', [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS', SOURCE])
        output = passed('interface-assumptions', [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS', PROBE])
        report['actual_assumptions_union'] = checked_assumptions(output)
        passed('coqchk', [coqbin + 'coqchk', '-silent', '-R', '.', 'CertiOS',
                         'CertiOS.certiucos.v293.proofs.V293SwitchPriorityBoundary'])
        source = (ROOT / SOURCE).read_text()
        work = Path(tempfile.mkdtemp(prefix='v293-switch-priority-'))
        cases = {'positive_same_environment': (source, None), **mutations(source)}
        for label, (candidate, declaration) in cases.items():
            case = work / label
            case.mkdir()
            path = case / Path(SOURCE).name
            path.write_text(candidate)
            args = [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS', '-R', str(case),
                    'CertiOS.certiucos.v293.proofs', str(path)]
            if declaration is None:
                passed(label, args)
                output = passed(label + '-interface', [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS',
                    '-R', str(case), 'CertiOS.certiucos.v293.proofs', PROBE])
                if checked_assumptions(output) != report['actual_assumptions_union']:
                    raise ValueError('positive copy assumptions differ')
            else:
                code, output = run(label, args)
                report['negative_controls'][label] = CHECK.check_rejection(code, output, candidate, declaration, path)
        if identity != {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths}:
            raise ValueError('local gate inputs changed during checking')
        report['passed'] = True
    finally:
        if work is not None:
            cleanup = [{'path': str(p), 'size': p.stat().st_size,
                        'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
                       for p in sorted(work.rglob('*')) if p.is_file()]
            (out / 'temporary-cleanup-manifest.json').write_text(json.dumps(cleanup, indent=2) + '\n')
            for row in cleanup:
                p = Path(row['path'])
                if p.stat().st_size != row['size'] or hashlib.sha256(p.read_bytes()).hexdigest() != row['sha256']:
                    raise ValueError('temporary cleanup identity changed')
            shutil.rmtree(work)
            report['temporary_cleanup'] = {'files': len(cleanup), 'bytes': sum(p['size'] for p in cleanup)}
        (out / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
    print('LOCAL PRIORITY BOUNDARY: PASS (not port or full function proof)')
    print(out.relative_to(ROOT) / 'result.json')


if __name__ == '__main__':
    main()
