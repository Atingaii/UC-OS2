#!/usr/bin/env python3
"""Local vacated-cache branch and source counter execution; not full API/port evidence."""
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
CONNECT = 'certiucos/v293/proofs/V293OSSchedStorageConnect.v'
WITNESS = 'certiucos/v293/proofs/V293OSSchedStorageConnectWitness.v'
BOUNDARY = 'certiucos/v293/proofs/V293SwitchPriorityBoundary.v'
PROBE = 'audit/probes/V293CacheLagProbe.v'
SOURCES = [CONNECT, WITNESS, BOUNDARY]
ROOT_COUNT = 8
spec = importlib.util.spec_from_file_location('cache_local_check', ROOT / 'scripts/check-v293-storage-prefix.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


def checked_assumptions(output):
    if output.count('Axioms:') + output.count('Closed under the global context') != ROOT_COUNT:
        raise ValueError('eight actual root assumption prints required')
    return CHECK.TRUST.check_assumptions(
        output.replace('Closed under the global context', ''), CHECK.TRUST.ALLOWED)


def mutations(connect, boundary):
    def header(source, declaration, old, new):
        start = source.index(declaration)
        end = source.index('Proof.', start)
        return source[:start] + CHECK.replace_once(source[start:end], old, new) + source[end:]
    rekey = 'Theorem V293_rekey_vacates_cache :'
    ready = 'Theorem V293_ready_OSSched_vacated_cache :'
    same = 'Theorem V293_cache_lag_same_pointer_execution :'
    # ONE theorem header per control; its entire original proof is retained.
    return {
        'old-new-distinction-omitted-only': (CONNECT, header(connect, rekey,
            'cached <> new ->', 'True ->'), rekey),
        'vacated-slot-omitted-only': (CONNECT, header(connect, ready,
            'nth nc entries Vnull = Vnull ->', 'True ->'), ready),
        'source-increment-omitted-only': (CONNECT, header(connect, ready,
            'V293_OSSched_change high current counter (sprim (switch target))',
            'sifthen (V293_OSSched_different high current) (sseq (sskip None) (sprim (switch target)))'), ready),
        'pointer-guard-claimed-true-only': (BOUNDARY, header(boundary, same,
            '(V293_cache_lag_ge, emp, V293_cache_lag_memory) = Some (Vint32 Int.zero)',
            '(V293_cache_lag_ge, emp, V293_cache_lag_memory) = Some (Vint32 Int.one)'), same),
    }


def main():
    out = ROOT / 'audit/logs/stage26-cache-lag-branch' / time.strftime('run-%Y%m%d-%H%M%S')
    out.mkdir(parents=True, exist_ok=False)
    paths = sorted({p.relative_to(ROOT).as_posix()
                    for tree in ['framework', 'tactics', 'certiucos/v293']
                    for p in (ROOT / tree).rglob('*.v')} |
                   {PROBE, 'scripts/check-v293-cache-lag.py',
                    'tests/test_cache_lag_local.py',
                    'scripts/check-v293-storage-prefix.py', 'scripts/check-memory-trust.py',
                    'Makefile', '_CoqProject'})
    identity = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths}
    report = {'scope': 'LOCAL_VACATED_CACHE_READY_BRANCH_AND_COUNTER_TRACE_NOT_FULL_API_PORT_OR_GOOD_OS',
              'kernel_GOOD_OS_proved': False, 'source_OSCtxSw_contract_discharged': False,
              'formal_function_evidence_updated': False, 'prebuilt_dependency_closure': True,
              'input_sha256': identity, 'checks': {}, 'negative_controls': {}, 'passed': False}
    coqbin = os.environ.get('COQBIN', '')

    def run(label, args, required=True):
        try:
            p = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, timeout=600)
        except subprocess.TimeoutExpired as error:
            output = error.stdout or ''
            if isinstance(output, bytes):
                output = output.decode(errors='replace')
            (out / (label + '.log')).write_text(output)
            report['checks'][label] = {'exit_code': 124, 'timeout_seconds': 600,
                                       'log': label + '.log'}
            raise
        (out / (label + '.log')).write_text(p.stdout)
        report['checks'][label] = {'exit_code': p.returncode, 'log': label + '.log'}
        if required and p.returncode:
            raise ValueError(label + ' failed; inspect ' + str(out))
        return p.returncode, p.stdout

    work = None
    try:
        _, version = run('version', [coqbin + 'coqc', '--version'])
        if not re.search(r'version 8\.18\.0(?: |$)', version, re.MULTILINE):
            raise ValueError('Coq 8.18.0 required')
        for source in SOURCES:
            run(Path(source).stem, [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS', source])
        _, output = run('eight-literal-roots', [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS', PROBE])
        report['actual_assumptions_union'] = checked_assumptions(output)
        for source in [*SOURCES, PROBE]:
            run(Path(source).stem + '-coqchk', [coqbin + 'coqchk', '-silent', '-R', '.', 'CertiOS',
                'CertiOS.' + str(Path(source).with_suffix('')).replace('/', '.')])
        work = Path(tempfile.mkdtemp(prefix='v293-cache-lag-'))
        positive = work / 'positive-same-environment'
        positive.mkdir()
        flags = ['-q', '-R', '.', 'CertiOS', '-R', str(positive), 'CertiOS.certiucos.v293.proofs']
        for source in SOURCES:
            path = positive / Path(source).name
            path.write_bytes((ROOT / source).read_bytes())
            run('positive-' + path.stem, [coqbin + 'coqc', *flags, str(path)])
        _, output = run('positive-probe', [coqbin + 'coqc', *flags, PROBE])
        if checked_assumptions(output) != report['actual_assumptions_union']:
            raise ValueError('positive assumptions differ')
        for label, (source, candidate, declaration) in mutations(
                (ROOT / CONNECT).read_text(), (ROOT / BOUNDARY).read_text()).items():
            case = work / label
            case.mkdir()
            path = case / Path(source).name
            path.write_text(candidate)
            code, output = run(label, [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS',
                '-R', str(case), 'CertiOS.certiucos.v293.proofs', str(path)], False)
            report['negative_controls'][label] = CHECK.check_rejection(code, output, candidate, declaration, path)
        if identity != {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths}:
            raise ValueError('protocol inputs changed during verification')
        report['passed'] = True
    finally:
        if work is not None:
            targets = [{'path': str(p), 'size': p.stat().st_size,
                        'sha256': hashlib.sha256(p.read_bytes()).hexdigest()}
                       for p in sorted(work.rglob('*')) if p.is_file()]
            (out / 'temporary-cleanup-manifest.json').write_text(json.dumps(targets, indent=2) + '\n')
            for row in targets:
                path = Path(row['path'])
                if path.stat().st_size != row['size'] or hashlib.sha256(path.read_bytes()).hexdigest() != row['sha256']:
                    raise ValueError('temporary cleanup target changed')
            shutil.rmtree(work)
            report['temporary_cleanup'] = {'files': len(targets), 'bytes': sum(p['size'] for p in targets),
                                           'removed': not work.exists()}
        (out / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
    print('LOCAL CACHE LAG: PASS (full API and source port connection remain open)')
    print(out.relative_to(ROOT) / 'result.json')


if __name__ == '__main__':
    main()
