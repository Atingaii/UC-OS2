#!/usr/bin/env python3
"""Execute real C APIs and a prospective 2x2 authorized-repair ablation."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CHECKOUT = Path('csrc/upstream/v2.93.01/checkout')
PATCHES = {
    'mutex': Path('csrc/repairs/0001-nested-mutex-restoration.patch'),
    'guard': Path('csrc/repairs/0002-locked-current-self-delete.patch'),
}
PATCH_TARGETS = {'mutex': 'Source/os_mutex.c', 'guard': 'Source/os_task.c'}
VARIANTS = {'upstream': (), 'mutex-only': ('mutex',),
            'guard-only': ('guard',), 'both': ('mutex', 'guard')}
FLAGS = ['-m32', '-std=c11', '-ffreestanding', '-nostdinc', '-nostdlib', '-static',
         '-fno-pie', '-no-pie', '-fno-stack-protector', '-Werror=implicit-function-declaration']
# Required observable, not just "some nonzero exit". Crashes/timeouts never
# count as reproduced known failures. Expectations are unchanged across variants.
CASES = [
    ('K1-timeout-suspend-resume', None, None),
    ('K1-suspend-timeout-resume', None, None),
    ('K2-single-mutex-delete', None, None),
    ('K3-pend-delete-forward', 'mutex', 'owner->OSTCBPrio == 10'),
    ('K3-accept-delete-forward', 'mutex', 'owner->OSTCBPrio == 10'),
    ('K3-pend-delete-reuse', 'mutex', 'owner->OSTCBPrio == 10'),
    ('K3-accept-delete-reuse', 'mutex', 'owner->OSTCBPrio == 10'),
    ('K3-pend-delete-reverse-control', None, None),
    ('K3-accept-delete-reverse-control', None, None),
    ('K3-pend-post-forward', 'mutex', 'owner->OSTCBPrio == 10'),
    ('K3-accept-post-forward', 'mutex', 'owner->OSTCBPrio == 10'),
    ('K3-pend-post-reverse-control', None, None),
    ('K3-accept-post-reverse-control', None, None),
    ('K4-self-lock-1', 'guard', 'result == OS_ERR_SCHED_LOCKED'),
    ('K4-explicit-lock-1', 'guard', 'result == OS_ERR_SCHED_LOCKED'),
    ('K4-self-lock-255', 'guard', 'result == OS_ERR_SCHED_LOCKED'),
    ('K4-explicit-lock-255', 'guard', 'result == OS_ERR_SCHED_LOCKED'),
    ('delete-error-order-and-permitted-controls', None, None),
    ('K3-no-pend-delete-reuse', 'mutex', 'owner->OSTCBPrio == 10'),
    ('K3-suspended-owner-other-deleter', 'mutex', 'owner->OSTCBPrio == 10'),
    ('K3-waiting-owner-other-deleter', 'mutex', 'OSPrioCur == 3 && OSTCBCur == controller'),
    ('K3-handoff-to-inherited-owner', 'mutex', '(second->OSEventCnt & 0xffu) == 10'),
    ('disabled-ceiling-control', None, None),
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(args, cwd=ROOT):
    proc = subprocess.run([str(a) for a in args], cwd=cwd, capture_output=True, text=True, timeout=60)
    if proc.returncode:
        raise ValueError(f'command failed ({proc.returncode}): {args}\n{proc.stdout}{proc.stderr}')
    return proc.stdout


def materialize(destination, repairs):
    """Copy locked inputs only; caller audits the pristine checkout first."""
    lock = json.loads((ROOT / 'csrc/UPSTREAM.lock.json').read_text())
    for rel in [*lock['files'], 'os_cfg.h']:
        target = destination / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / CHECKOUT / rel, target)
    for name in repairs:
        # No fuzz, shell substitution, network fetch or modification of upstream.
        patch = ROOT / PATCHES[name]
        changed = command(['git', 'apply', '--numstat', patch], cwd=destination).splitlines()
        if len(changed) != 1 or changed[0].split('\t')[-1] != PATCH_TARGETS[name]:
            raise ValueError(f'patch changes files outside its authorized source: {name}')
        command(['git', 'apply', '--check', patch], cwd=destination)
        command(['git', 'apply', patch], cwd=destination)
    hashes = {rel: sha(destination / rel) for rel in lock['files']}
    changed = {rel for rel, expected in lock['files'].items() if hashes[rel] != expected}
    if changed != {PATCH_TARGETS[name] for name in repairs}:
        raise ValueError('applied patches differ from their authorized source-file set')
    return hashes


def compile_binary(source, binary, compiler='gcc', optimization='-O0'):
    command([compiler, *FLAGS, optimization,
             '-I', ROOT / 'csrc/analysis-port', '-I', source, '-I', source / 'Source',
             ROOT / 'tests/c/start-i386.S', ROOT / 'tests/c/kernel-regressions.c', '-o', binary])


def check_matrix(compilers=('gcc', 'clang'), optimizations=('-O0', '-O2')):
    # Read-only identity/configuration/boundary check. Do NOT call the config
    # generator here: it would overwrite local drift before detecting it.
    command(['python3', 'scripts/inventory-v293-source.py', '--check'])
    inputs = [Path(__file__).relative_to(ROOT), *PATCHES.values(),
              Path('scripts/inventory-v293-source.py'), Path('audit/source-inventory.json'),
              Path('csrc/UPSTREAM.lock.json'), Path('csrc/config/v29301-profile.json'),
              CHECKOUT / 'os_cfg.h', Path('csrc/analysis-port/os_cpu.h'),
              Path('csrc/analysis-port/app_cfg.h'), Path('tests/c/kernel-regressions.c'),
              Path('tests/c/start-i386.S')]
    report = {
        'schema_version': 1, 'scope': 'REAL_C_CONTROLLED_CPU_BOUNDARY_REGRESSION_NOT_COQ_PROOF',
        'input_sha256': {str(p): sha(ROOT / p) for p in inputs},
        'tools': {c: command([c, '--version']).splitlines()[0] for c in compilers},
        'compiler_flags': FLAGS, 'optimizations': list(optimizations),
        'case_count_per_binary': len(CASES), 'variants': {}, 'results': [],
    }
    # Owned temp directory contains copied source and derived binaries only.
    # The context manager removes it on success, failure or compile timeout.
    with tempfile.TemporaryDirectory(prefix='ucos-c-regression-') as directory:
        work = Path(directory)
        for variant, repairs in VARIANTS.items():
            source = work / variant
            hashes = materialize(source, repairs)
            report['variants'][variant] = {'repairs': list(repairs), 'source_sha256': hashes}
            for compiler in compilers:
                for optimization in optimizations:
                    binary = work / f'{variant}-{compiler}-{optimization[1:]}'
                    compile_binary(source, binary, compiler, optimization)
                    for index, (name, repair, symptom) in enumerate(CASES):
                        proc = subprocess.run([str(binary), str(index)], capture_output=True,
                                              text=True, timeout=5)
                        expected_failure = repair is not None and repair not in repairs
                        if expected_failure:
                            ok = proc.returncode == 2 and f'expression={symptom}\n' in proc.stdout
                            if repair == 'guard':
                                ok = ok and 'delete_result=0 current_is_free=1' in proc.stdout
                                ok = ok and 'replacement_reused_current_tcb=1' in proc.stdout
                        else:
                            ok = proc.returncode == 0 and proc.stdout.endswith('PASS\n')
                        ok = bool(ok and not proc.stderr)
                        report['results'].append({
                            'variant': variant, 'compiler': compiler, 'optimization': optimization,
                            'case': name, 'expected': 'KNOWN_FAILURE' if expected_failure else 'PASS',
                            'exit_code': proc.returncode, 'stdout': proc.stdout,
                            'stderr': proc.stderr, 'expectation_met': ok,
                        })
    report['matrix_passed'] = all(r['expectation_met'] for r in report['results'])
    report['both_repairs_all_cases_passed'] = all(
        r['exit_code'] == 0 and r['expectation_met'] for r in report['results'] if r['variant'] == 'both')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--report', type=Path, help='write this run to a new JSON file; never overwrite evidence')
    mode.add_argument('--check-report', type=Path, help='rerun and compare with reviewed JSON; never rewrite')
    args = parser.parse_args()
    try:
        result = check_matrix()
        text = json.dumps(result, ensure_ascii=False, indent=2) + '\n'
        if args.report:
            with args.report.open('x') as stream:
                stream.write(text)
        if args.check_report and args.check_report.read_text() != text:
            raise ValueError('C regression evidence drift; inspect before recording new evidence')
        failures = [r for r in result['results'] if not r['expectation_met']]
        for row in failures:
            print(json.dumps(row, ensure_ascii=False))
        print(f"C REGRESSION MATRIX: {'FAIL' if failures else 'PASS'} ({len(result['results'])} runs)")
        print('Scope: known-failure ablation and bounded C regressions, not GOOD_OS.')
        if failures:
            raise SystemExit(1)
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        parser.exit(1, f'C REGRESSION MATRIX: FAIL: {error}\n')


if __name__ == '__main__':
    main()
