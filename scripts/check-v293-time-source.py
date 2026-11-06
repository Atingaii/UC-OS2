#!/usr/bin/env python3
"""Replay locked C -> restricted AST -> existing complete time functions.

Retains single-copy-source mutants past parsing and rejects them at unchanged
Coq function equalities. Does not award whole-program coverage credit.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def load(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), ROOT / 'scripts' / name)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def digest(data):
    return hashlib.sha256(data).hexdigest()


EQUALITIES = '''
Require Import CertiOS.certiucos.v293.proofs.V293TimeGetAPI.
Require Import CertiOS.certiucos.v293.proofs.V293TimeSetAPI.
Theorem checked_get : forall now ticks saved,
  V293_source_OSTimeGet_function now ticks saved = V293_TimeGet_function now ticks saved.
Proof. reflexivity. Qed.
Theorem checked_set : forall now ticks saved,
  V293_source_OSTimeSet_function now ticks saved = V293_TimeSet_function now ticks saved.
Proof. reflexivity. Qed.
'''


def inspect(evidence, coqc):
    seam = load('v293-time-source.py')
    freeze = load('freeze-v293-source.py')
    c = load('check-v293-c-regressions.py')
    u = load('inventory-v293-source.py')
    version = subprocess.check_output([coqc, '--version'], text=True)
    if not re.search(r'version 8\.18\.0\b', version):
        raise ValueError('this evidence replay requires Coq 8.18.0')
    actual, inventory = freeze.collect(ROOT)
    for path, obj in [(freeze.FREEZE, actual), (freeze.INVENTORY, inventory)]:
        if (ROOT / path).read_text() != freeze.serialize(obj):
            raise ValueError('fixed source/inventory drift: ' + str(path))
    inputs = {p: digest((ROOT / p).read_bytes()) for p in [
        'scripts/v293-time-source.py', 'scripts/check-v293-time-source.py', seam.CODE,
        'certiucos/v293/proofs/V293TimeSourceAPI.v', 'csrc/repairs/FROZEN_SOURCE.json',
        'audit/repaired-source-inventory.json']}
    rows = [r for r in inventory['functions'] if r['name'] in seam.NAMES]
    if sorted(r['name'] for r in rows) != sorted(seam.NAMES):
        raise ValueError('expected unique source locations for both time APIs')
    with tempfile.TemporaryDirectory(prefix='v293-time-source-') as td:
        work = Path(td)
        source = work / freeze.SOURCE
        if c.materialize(source, ('mutex', 'guard')) != actual['program']['source_sha256']:
            raise ValueError('materialized source identity mismatch')
        for rel in ['os_cpu.h', 'app_cfg.h']:
            p = work / u.PORT / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / u.PORT / rel, p)
        includes = [v for p in [u.PORT, freeze.SOURCE, freeze.SOURCE / 'Source']
                    for v in ['-I', str(p)]]
        unit = str(freeze.SOURCE / 'Source/ucos_ii.c')
        pp = u.run(work, ['clang', *u.CLANG_FLAGS, *includes, '-E', unit])
        if digest(pp) != inventory['preprocessed_sha256']:
            raise ValueError('configured input differs from frozen inventory')

        def parse(data):
            (work / 'kernel.i').write_bytes(data)
            tree = json.loads(u.run(work, ['clang', *u.CLANG_FLAGS, '-x', 'c', '-fsyntax-only',
                                          '-Xclang', '-ast-dump=json', 'kernel.i']))
            nodes = [n for n in u.definitions(tree) if n['name'] in seam.NAMES]
            if sorted(n['name'] for n in nodes) != sorted(seam.NAMES):
                raise ValueError('expected exactly both configured time definitions')
            return nodes, {n['name']: seam.decode(n) for n in nodes}

        nodes, sources = parse(pp)
        gcc = u.run(work, ['gcc', *u.GCC_FLAGS, *includes, '-E', unit])
        _, gcc_sources = parse(gcc)
        if gcc_sources != sources:
            raise ValueError('GCC/Clang copy/declaration/marker disagreement')
        generated = seam.emit(sources)
        if (ROOT / seam.CODE).read_text() != generated:
            raise ValueError('generated time function differs from configured AST emission')
        for row in rows:
            src = work / row['source']
            data = src.read_bytes()
            definition = pp[row['preprocessed_begin_byte']:row['preprocessed_end_byte_exclusive']]
            lines = b''.join(data.splitlines(keepends=True)[row['first_line']-1:row['last_line']])
            if (digest(data) != row['source_file_sha256'] or digest(lines) != row['source_lines_sha256']
                    or digest(definition) != row['preprocessed_definition_sha256']):
                raise ValueError('time source location identity mismatch')
            (evidence / (row['name'] + '.configured.c.snapshot.txt')).write_bytes(definition)
            (evidence / (row['name'] + '.source.c.snapshot.txt')).write_bytes(lines)
        (evidence / 'configured-ast.json').write_text(json.dumps(nodes, indent=2) + '\n')
        checks = []

        def check(label, code, expected_failure=None):
            text = code + EQUALITIES
            path = work / 'TimeCheck.v'
            path.write_text(text)
            (evidence / (label + '.v.snapshot.txt')).write_text(text)
            command = [coqc, '-q', '-R', str(ROOT), 'CertiOS', '-Q', str(work), 'TimeCheck', str(path)]
            result = subprocess.run(command, cwd=work, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            log = result.stdout.decode()
            (evidence / (label + '.log')).write_text(log)
            line = None
            if expected_failure:
                start = text.index('Theorem checked_' + expected_failure)
                proof = text.index('Proof. reflexivity.', start)
                line = text[:proof].count('\n') + 1
                matches = re.findall(r'line (\d+), characters', log)
                if (result.returncode != 1 or not matches or int(matches[-1]) != line
                        or 'Unable to unify' not in log):
                    raise ValueError(label + ': not rejected at the unchanged function equality')
            elif result.returncode != 0:
                raise ValueError(label + ': positive equality failed')
            checks.append({'label': label, 'exit': result.returncode, 'code_sha256': digest(code.encode()),
                           'snapshot_sha256': digest(text.encode()), 'expected_equality_line': line,
                           'gate': 'UNCHANGED_FUNCTION_EQUALITY', 'decoder_accepted': True})

        check('positive', generated)
        for name, old, new, failed in [
                ('OSTimeGet', b'ticks = OSTime;', b'ticks = ticks;', 'get'),
                ('OSTimeSet', b'OSTime = ticks;', b'OSTime = OSTime;', 'set')]:
            row = next(r for r in rows if r['name'] == name)
            begin, end = row['preprocessed_begin_byte'], row['preprocessed_end_byte_exclusive']
            original = pp[begin:end]
            if original.count(old) != 1:
                raise ValueError('mutant copy location is not unique')
            mutated = original.replace(old, new)
            (evidence / (name + '.mutant.configured.c.snapshot.txt')).write_bytes(mutated)
            _, mutated_sources = parse(pp[:begin] + mutated + pp[end:])
            expected_sources = dict(sources)
            expected_sources[name] = 'ticks' if name == 'OSTimeGet' else 'OSTime'
            if mutated_sources != expected_sources:
                raise ValueError('mutation changed more than the selected copy source')
            check('mutant-' + name, seam.emit(mutated_sources), failed)
        for p, h in inputs.items():
            if digest((ROOT / p).read_bytes()) != h:
                raise ValueError('input edited during source replay: ' + p)
        return {'scope': 'RESTRICTED_SOURCE_EQUALITY_TO_EXISTING_TIME_FUNCTIONS_NOT_GOOD_OS',
                'trusted_boundary': ['Clang AST', 'restricted Python decoder/emitter', 'ADR0005 critical normalization'],
                'version': version.strip(), 'inputs': inputs, 'locations': rows, 'sources': sources,
                'gcc_clang_agreement': True, 'checks': checks, 'passed': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--evidence-dir', required=True, type=Path)
    parser.add_argument('--coqc', default='coqc')
    args = parser.parse_args()
    # A replay never overwrites its own previous evidence.
    args.evidence_dir.mkdir(parents=True, exist_ok=False)
    report = inspect(args.evidence_dir.resolve(), args.coqc)
    (args.evidence_dir / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print('TIME SOURCE CONNECTION: PASS (2 original functions; 2 accepted copy mutants rejected at Coq equality)')


if __name__ == '__main__':
    main()
