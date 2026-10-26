#!/usr/bin/env python3
"""Reproduce the repaired fixed-profile source identity and its complete inventory."""
from __future__ import annotations

import argparse
from collections import Counter
import importlib.util
import json
import re
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SOURCE = Path('csrc/repaired/v2.93.01/checkout')  # Logical path inside an owned temporary root.
FREEZE = Path('csrc/repairs/FROZEN_SOURCE.json')
INVENTORY = Path('audit/repaired-source-inventory.json')
STATES = ['located', 'modeled', 'specified', 'local_hoare',
          'component_linked', 'full_target_linked']
LAYER = 'PINNED_UPSTREAM_WITH_TWO_AUTHORIZED_REPAIRS_FIXED_PROFILE'
HELPERS = {'OSMutex_BasePrio', 'OSMutex_EffectivePrio'}
CHANGED = {'OSMutexAccept', 'OSMutexDel', 'OSMutexPend', 'OSMutexPost',
           'OSMutex_RdyAtPrio', 'OSTaskDel'}


def load_tool(root, name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), root / 'scripts' / name)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def serialize(value):
    return json.dumps(value, ensure_ascii=False, indent=2) + '\n'


def identity(program):
    """Identity covers all source/header bytes and selected analysis inputs, not tests."""
    import hashlib
    canonical = json.dumps(program, sort_keys=True, separators=(',', ':')).encode()
    return hashlib.sha256(canonical).hexdigest()


def check_delta(upstream, repaired):
    before = {f['name']: f for f in upstream['functions']}
    after = {f['name']: f for f in repaired['functions']}
    if before.keys() - after.keys() or after.keys() - before.keys() != HELPERS:
        raise ValueError('repaired definition set is not upstream plus the two authorized helpers')
    if any(after[n]['linkage'] != 'internal' or after[n]['category'] != 'internal' for n in HELPERS):
        raise ValueError('repair helpers must remain static and internal')
    if any(before[n]['type'] != after[n]['type'] or before[n]['linkage'] != after[n]['linkage']
           for n in before):
        raise ValueError('repair changed an existing function interface')
    # Raw configured definition extents avoid false deltas from changed #line
    # paths/line numbers. Exact preprocessed hashes remain in each inventory.
    changed = {n for n in before if before[n]['source_lines_sha256'] !=
               after[n]['source_lines_sha256']}
    if changed != CHANGED:
        raise ValueError(f'configured body changes exceed or omit authorized functions: {sorted(changed)}')
    if upstream['boundaries'] != repaired['boundaries']:
        raise ValueError('repair changed CPU/critical/context-switch boundaries')
    if upstream['effective_os_macros'] != repaired['effective_os_macros']:
        raise ValueError('repair changed effective configuration')
    return {'added_static_helpers': sorted(HELPERS), 'changed_existing_bodies': sorted(changed),
            'removed_definitions': [], 'existing_interfaces_unchanged': True,
            'effective_configuration_unchanged': True, 'boundaries_unchanged': True}


def collect(root):
    upstream_tool = load_tool(root, 'inventory-v293-source.py')
    c_tool = load_tool(root, 'check-v293-c-regressions.py')
    # Recompute the original upstream inventory, do not regenerate configuration.
    upstream = upstream_tool.inventory(root)
    if serialize(upstream) != (root / upstream_tool.MANIFEST).read_text():
        raise ValueError('reviewed upstream inventory drift')
    lock = json.loads((root / 'csrc/UPSTREAM.lock.json').read_text())
    profile = json.loads((root / 'csrc/config/v29301-profile.json').read_text())
    regression = json.loads((root / 'audit/c-regressions.json').read_text())
    for rel, expected in regression['input_sha256'].items():
        if c_tool.sha(root / rel) != expected:
            raise ValueError(f'C regression input identity drift: {rel}')
    if not regression['matrix_passed'] or not regression['both_repairs_all_cases_passed']:
        raise ValueError('reviewed C regression evidence is not passing')
    # A recorded C report is provenance, not a fresh execution or a proof oracle.
    inputs = [Path('scripts/freeze-v293-source.py'), Path('scripts/inventory-v293-source.py'),
              Path('scripts/check-v293-c-regressions.py'), Path('audit/source-inventory.json'),
              Path('audit/c-regressions.json'), Path('csrc/UPSTREAM.lock.json'),
              Path('csrc/config/v29301-profile.json'), Path('csrc/repairs/REPAIR_TARGET.json'),
              *c_tool.PATCHES.values(), upstream_tool.PORT / 'os_cpu.h',
              upstream_tool.PORT / 'app_cfg.h']
    with tempfile.TemporaryDirectory(prefix='ucos-repaired-inventory-') as directory:
        work = Path(directory)
        source = work / SOURCE
        hashes = c_tool.materialize(source, ('mutex', 'guard'))
        if hashes != regression['variants']['both']['source_sha256']:
            raise ValueError('replayed source differs from C regression source identity')
        for rel in ('os_cpu.h', 'app_cfg.h'):
            dest = work / upstream_tool.PORT / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(root / upstream_tool.PORT / rel, dest)
        program = {
            'target_release': lock['release'], 'target_commit': lock['commit'],
            'source_sha256': hashes,
            'os_cfg_sha256': c_tool.sha(source / 'os_cfg.h'),
            'analysis_port_sha256': {rel: c_tool.sha(root / upstream_tool.PORT / rel)
                                    for rel in ('os_cpu.h', 'app_cfg.h')},
        }
        source_id = identity(program)
        locked = {(SOURCE / p).as_posix(): h for p, h in hashes.items()}
        includes = [a for p in [upstream_tool.PORT, SOURCE, SOURCE / 'Source']
                    for a in ['-I', str(p)]]
        unit = str(SOURCE / 'Source/ucos_ii.c')
        pp = work / 'kernel.i'

        def parse(data):
            pp.write_bytes(data)
            return json.loads(upstream_tool.run(work, ['clang', *upstream_tool.CLANG_FLAGS,
                '-x', 'c', '-fsyntax-only', '-Xclang', '-ast-dump=json', str(pp)]))

        data = upstream_tool.run(work, ['clang', *upstream_tool.CLANG_FLAGS, *includes, '-E', unit])
        ast = parse(data)
        functions = upstream_tool.summarize(ast, data, work, locked)
        upstream_tool.run(work, ['gcc', *upstream_tool.GCC_FLAGS, *includes, '-fsyntax-only', unit])
        other = upstream_tool.run(work, ['gcc', *upstream_tool.GCC_FLAGS, *includes, '-E', unit])
        upstream_tool.compare_frontends(functions, upstream_tool.summarize(parse(other), other, work, locked))
        tags = upstream_tool.catalogue(work, sorted(p for p in locked if p.endswith('.c')))
        for f in functions:
            tag = tags.get(f['name'])
            if not tag or (tag['path'], tag['line'], tag['end']) != (
                    f['source'], f['first_line'], f['last_line']):
                raise ValueError(f"repaired compiler/ctags extent disagreement: {f['name']}")
        macros = upstream_tool.run(work, ['clang', *upstream_tool.CLANG_FLAGS, *includes, '-E', '-dM', unit])
        effective = {}
        for line in macros.decode().splitlines():
            match = re.match(r'#define (OS_\w+) (.*)$', line)
            if match:
                effective[match[1]] = match[2]
        names = {f['name'] for f in functions}
        excluded = [{'name': n, 'source': t['path'], 'first_line': t['line'],
                     'last_line': t['end'], 'source_file_sha256': locked[t['path']],
                     'status': 'NOT_IN_CONFIGURED_TRANSLATION_UNIT'}
                    for n, t in sorted(tags.items()) if n not in names]
        boundaries = upstream_tool.external_declarations(ast, functions)
        repaired = {
            'schema_version': 1, 'target_release': lock['release'], 'target_commit': lock['commit'],
            'source_layer': LAYER, 'source_identity_sha256': source_id,
            'proof_coverage_credit': 'LOCATION_ONLY_NOT_TRANSLATION_OR_PROOF',
            'logical_source_root': str(SOURCE),
            'preprocessed_sha256': upstream_tool.digest(data),
            'tools': upstream['tools'], 'clang_flags': upstream_tool.CLANG_FLAGS,
            'gcc_flags': upstream_tool.GCC_FLAGS, 'effective_os_macros': dict(sorted(effective.items())),
            'summary': {'configured_c_definitions': len(functions),
                        'categories': dict(sorted(Counter(f['category'] for f in functions).items())),
                        'declaration_only_boundaries': len(boundaries),
                        'unconfigured_source_catalogue': len(tags), 'excluded_definitions': len(excluded)},
            'functions': functions, 'boundaries': boundaries, 'excluded_definitions': excluded,
            'catalogue_limit': upstream['catalogue_limit'],
        }
        delta = check_delta(upstream, repaired)
        if program['os_cfg_sha256'] != profile['expected_effective_os_cfg_sha256']:
            raise ValueError('replayed configuration drift')
    freeze = {
        'schema_version': 1, 'scope': 'C_SOURCE_IDENTITY_NOT_CORRECTNESS_OR_COQ_PROOF',
        'source_layer': LAYER, 'source_identity_sha256': source_id, 'program': program,
        'replay': {'logical_source_root': str(SOURCE), 'patches_in_order': [str(p) for p in c_tool.PATCHES.values()],
                   'storage': 'RECONSTRUCTED_IN_OWNED_TEMPORARY_ROOT_NOT_COMMITTED_SOURCE_COPY'},
        'input_sha256': {str(p): c_tool.sha(root / p) for p in inputs},
        'inventory': {'path': str(INVENTORY), 'sha256': upstream_tool.digest(serialize(repaired).encode())},
        'authorized_delta': delta,
        'open_obligations': ['C_TO_COQIMP_CORRESPONDENCE', 'GLOBAL_INVARIANTS', 'ALL_FUNCTION_HOARE_PROOFS',
                             'BOUNDARY_CONTRACTS', 'INITIALIZATION', 'GOOD_OS', 'ASSUMPTION_AUDIT'],
    }
    return freeze, repaired


def location_rows(inventory):
    keys = ('source', 'first_line', 'last_line', 'source_file_sha256',
            'source_lines_sha256', 'preprocessed_definition_sha256', 'preprocessed_body_sha256')
    return [{'name': f['name'], 'source_identity_sha256': inventory['source_identity_sha256'],
             **{s: s == 'located' for s in STATES},
             'location': {'inventory': str(INVENTORY), **{k: f[k] for k in keys}}}
            for f in inventory['functions']]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', action='store_true', help='create first records only; never overwrite')
    args = parser.parse_args()
    try:
        freeze, inventory = collect(ROOT)
        outputs = {FREEZE: serialize(freeze), INVENTORY: serialize(inventory)}
        if args.record:
            if any((ROOT / p).exists() for p in outputs):
                raise ValueError('freeze records already exist; review a new source revision explicitly')
            for path, content in outputs.items():
                with (ROOT / path).open('x') as stream:
                    stream.write(content)
        else:
            for path, content in outputs.items():
                if (ROOT / path).read_text() != content:
                    raise ValueError(f'frozen source drift: {path}; records were not rewritten')
        print('REPAIRED SOURCE FREEZE: PASS', serialize(inventory['summary']).strip())
        print('source identity:', freeze['source_identity_sha256'])
        print('Scope: exact source identity and locations only; no Coq proof credit.')
    except (OSError, ValueError, KeyError, subprocess.TimeoutExpired) as error:
        parser.exit(1, f'REPAIRED SOURCE FREEZE: FAIL: {error}\n')


if __name__ == '__main__':
    main()
