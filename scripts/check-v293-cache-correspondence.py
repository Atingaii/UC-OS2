#!/usr/bin/env python3
"""Local two-memory cache correspondence; never port or full-function evidence."""
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
COMPARISON = 'certiucos/v293/proofs/V293OSSchedPointerCompare.v'
BOUNDARY = 'certiucos/v293/proofs/V293SwitchPriorityBoundary.v'
PROBE = 'audit/probes/V293CacheCorrespondenceProbe.v'
SOURCES = [COMPARISON, BOUNDARY]
ROOT_COUNT = 6
spec = importlib.util.spec_from_file_location('cache_local_check', ROOT / 'scripts/check-v293-storage-prefix.py')
CHECK = importlib.util.module_from_spec(spec)
spec.loader.exec_module(CHECK)


def checked_assumptions(output):
    if output.count('Axioms:') + output.count('Closed under the global context') != ROOT_COUNT:
        raise ValueError('six actual root assumption prints required')
    return CHECK.TRUST.check_assumptions(
        output.replace('Closed under the global context', ''), CHECK.TRUST.ALLOWED)


def mutations(comparison, boundary):
    def header(source, declaration, old, new):
        start = source.index(declaration)
        end = source.index('Proof.', start)
        return source[:start] + CHECK.replace_once(source[start:end], old, new) + source[end:]
    load = 'Theorem V293_cache_related_load :'
    sync = 'Theorem V293_cache_synchronized_store_refinement :'
    cross = 'Theorem V293_OSSched_cross_memory_comparison :'
    decisions = 'Theorem V293_cache_observation_decisions :'
    # Each control changes ONE theorem header; original proof is retained.
    return {
        'wrong-noncache-load-only': (COMPARISON, header(comparison, load,
            'load tp source (b, i) = load tp normalized (b, i).',
            'load tp source (b, i) = None.'), load),
        'wrong-source-cache-after-sync-only': (COMPARISON, header(comparison, sync,
            'V293_cache_correspondence cache nc source\' normalized\'.',
            'V293_cache_correspondence cache (S nc) source\' normalized\'.'), sync),
        'current-coherence-omitted-only': (COMPARISON, header(comparison, cross,
            'V293_current_task tasks tid nc -> V293_highest_ready tasks next ->',
            'True -> V293_highest_ready tasks next ->'), cross),
        'stale-source-guard-claimed-equal-only': (BOUNDARY, header(boundary, decisions,
            '(V293_cache_observation_ge, emp, V293_cache_observation_normalized) = Some (Vint32 Int.one) /\\',
            '(V293_cache_observation_ge, emp, V293_cache_observation_normalized) = Some (Vint32 Int.zero) /\\'), decisions),
    }


def main():
    out = ROOT / 'audit/logs/stage26-cache-correspondence' / time.strftime('run-%Y%m%d-%H%M%S')
    out.mkdir(parents=True, exist_ok=False)
    paths = sorted({p.relative_to(ROOT).as_posix()
                    for tree in ['framework', 'tactics', 'certiucos/v293']
                    for p in (ROOT / tree).rglob('*.v')} |
                   {PROBE, 'scripts/check-v293-cache-correspondence.py',
                    'tests/test_cache_correspondence_local.py',
                    'scripts/check-v293-storage-prefix.py', 'scripts/check-memory-trust.py',
                    'Makefile', '_CoqProject'})
    identity = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in paths}
    report = {'scope': 'LOCAL_TWO_MEMORY_CACHE_CORRESPONDENCE_NOT_PORT_IMPLEMENTATION_C_SIMULATION_OR_GOOD_OS',
              'kernel_GOOD_OS_proved': False, 'source_OSCtxSw_contract_discharged': False,
              'formal_function_evidence_updated': False, 'prebuilt_dependency_closure': True,
              'input_sha256': identity, 'checks': {}, 'negative_controls': {}, 'passed': False}
    coqbin = os.environ.get('COQBIN', '')

    def run(label, args, required=True):
        p = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, timeout=600)
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
        _, output = run('six-literal-roots', [coqbin + 'coqc', '-q', '-R', '.', 'CertiOS', PROBE])
        report['actual_assumptions_union'] = checked_assumptions(output)
        for source in [*SOURCES, PROBE]:
            run(Path(source).stem + '-coqchk', [coqbin + 'coqchk', '-silent', '-R', '.', 'CertiOS',
                'CertiOS.' + str(Path(source).with_suffix('')).replace('/', '.')])
        work = Path(tempfile.mkdtemp(prefix='v293-cache-correspondence-'))
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
                (ROOT / COMPARISON).read_text(), (ROOT / BOUNDARY).read_text()).items():
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
    print('LOCAL CACHE CORRESPONDENCE: PASS (source port contract still open)')
    print(out.relative_to(ROOT) / 'result.json')


if __name__ == '__main__':
    main()
