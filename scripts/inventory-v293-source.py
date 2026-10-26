#!/usr/bin/env python3
"""Inventory the pinned, configured upstream program; never claim proof coverage."""
from __future__ import annotations

import argparse
from bisect import bisect_right
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CHECKOUT = Path('csrc/upstream/v2.93.01/checkout')
PORT = Path('csrc/analysis-port')
MANIFEST = Path('audit/source-inventory.json')
CLANG_FLAGS = ['-target', 'i386-unknown-none-elf', '-ffreestanding', '-nostdinc', '-std=c11',
               '-Werror=implicit-function-declaration']
GCC_FLAGS = ['-m32', '-ffreestanding', '-nostdinc', '-std=c11', '-Werror=implicit-function-declaration']
CONTEXT_SWITCHES = {'OSStartHighRdy', 'OSIntCtxSw', 'OSCtxSw'}
CRITICAL_SECTIONS = {'V293_EnterCritical', 'V293_ExitCritical'}
CPU_HOOKS = {'OSInitHookBegin', 'OSInitHookEnd', 'OSTaskCreateHook', 'OSTaskDelHook',
             'OSTaskIdleHook', 'OSTaskReturnHook', 'OSTaskStatHook', 'OSTaskStkInit',
             'OSTaskSwHook', 'OSTCBInitHook', 'OSTimeTickHook'}
LINE_MARKER = re.compile(rb'^#\s+(\d+)\s+"([^"\n]+)"(?:\s+\d+)*\s*$')


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run(root: Path, args: list[str]) -> bytes:
    result = subprocess.run(args, cwd=root, capture_output=True, check=False)
    if result.returncode:
        raise ValueError(f"command failed ({result.returncode}): {' '.join(args)}\n"
                         + result.stderr.decode(errors='replace'))
    return result.stdout


def walk(node):
    yield node
    for child in node.get('inner', []):
        yield from walk(child)


class SourceMap:
    """Resolve byte offsets in preprocessor output using compiler line markers."""
    def __init__(self, data: bytes):
        self.starts = []
        self.locations = []
        file, line, offset = '', 1, 0
        for text in data.splitlines(keepends=True):
            self.starts.append(offset)
            self.locations.append((file, line))
            marker = LINE_MARKER.match(text.rstrip(b'\r\n'))
            if marker:
                line, file = int(marker[1]), marker[2].decode()
            else:
                line += 1
            offset += len(text)
        self.length = len(data)

    def at(self, offset: int):
        if not 0 <= offset < self.length:
            raise ValueError(f'AST offset outside preprocessed input: {offset}')
        return self.locations[bisect_right(self.starts, offset) - 1]


def definitions(ast):
    return [node for node in ast.get('inner', []) if node.get('kind') == 'FunctionDecl'
            and any(c.get('kind') == 'CompoundStmt' for c in node.get('inner', []))]


def unique_by_name(items):
    result = {}
    for item in items:
        name = item['name']
        if name in result:
            raise ValueError(f'duplicate function definition: {name}')
        result[name] = item
    return result


def summarize(ast, preprocessed: bytes, root: Path, locked_files: dict):
    source_map = SourceMap(preprocessed)
    funcs = unique_by_name(definitions(ast))
    result = []
    for name, node in sorted(funcs.items()):
        body = next(c for c in node['inner'] if c['kind'] == 'CompoundStmt')
        begin = node['range']['begin']['offset']
        end_loc = node['range']['end']
        end = end_loc['offset'] + end_loc['tokLen']
        body_begin = body['range']['begin']['offset']
        file, first_line = source_map.at(begin)
        end_file, last_line = source_map.at(end - 1)
        path = Path(file)
        if file not in locked_files or end_file != file or first_line > last_line:
            raise ValueError(f'{name}: definition not in one locked source file: {file}')
        text_lines = (root / path).read_bytes().splitlines(keepends=True)
        if last_line > len(text_lines) or preprocessed[end - 1:end] != b'}':
            raise ValueError(f'{name}: invalid definition extent')
        calls, indirect = set(), 0
        for expr in walk(body):
            if expr.get('kind') != 'CallExpr':
                continue
            # Inspect only the callee subtree, not function-valued arguments.
            callee = expr.get('inner', [])[:1]
            refs = [n.get('referencedDecl', {}) for c in callee for n in walk(c)
                    if n.get('kind') == 'DeclRefExpr']
            direct = [r['name'] for r in refs if r.get('kind') == 'FunctionDecl']
            if direct:
                calls.update(direct)
            else:
                indirect += 1
        result.append({
            'name': name,
            'category': 'internal' if name.startswith('OS_') or
                        node.get('storageClass') == 'static' else 'public',
            'linkage': 'internal' if node.get('storageClass') == 'static' else 'external',
            'type': node['type']['qualType'],
            'source': file, 'first_line': first_line, 'last_line': last_line,
            'source_file_sha256': locked_files[file],
            'source_lines_sha256': digest(b''.join(text_lines[first_line - 1:last_line])),
            'preprocessed_begin_byte': begin, 'preprocessed_end_byte_exclusive': end,
            'preprocessed_definition_sha256': digest(preprocessed[begin:end]),
            'preprocessed_body_sha256': digest(preprocessed[body_begin:end]),
            'direct_calls': sorted(calls), 'indirect_call_sites': indirect,
        })
    return result


def compare_frontends(primary, alternate):
    # Ignore formatting/offset/hash differences between the two preprocessors.
    def semantic(rows):
        keys = ('name', 'type', 'source', 'first_line', 'last_line', 'direct_calls',
                'indirect_call_sites', 'category', 'linkage')
        return [{k: row[k] for k in keys} for row in rows]
    if semantic(primary) != semantic(alternate):
        raise ValueError('Clang/GCC preprocessing disagree on configured definitions')


def catalogue(root: Path, sources: list[str]):
    command = ['ctags', '--options=NONE', '--output-format=json', '--language-force=C',
               '--kinds-C=f', '--fields=+ne', '--if0=yes', '-o', '-', *sources]
    tags = [json.loads(line) for line in run(root, command).splitlines()]
    tags = [t for t in tags if t.get('_type') == 'tag']
    return unique_by_name(tags)


def external_declarations(ast, functions):
    names = {f['name'] for f in functions}
    called = {c for f in functions for c in f['direct_calls']}
    if not CRITICAL_SECTIONS <= called:
        raise ValueError('critical-section boundary erased from configured C calls')
    if not CONTEXT_SWITCHES <= called:
        raise ValueError('context-switch boundary erased from configured C calls')
    declarations = {}
    for node in ast.get('inner', []):
        if node.get('kind') != 'FunctionDecl' or node['name'] in names:
            continue
        name = node['name']
        if name in CONTEXT_SWITCHES:
            category = 'context_switch'
        elif name in CRITICAL_SECTIONS:
            category = 'critical_section'
        elif name in CPU_HOOKS:
            category = 'cpu_hook'
        else:
            raise ValueError(f'unclassified declaration-only function: {name}')
        declarations[name] = {'name': name, 'category': category,
                              'type': node['type']['qualType'], 'called_from_c': name in called,
                              'proof_status': 'OPEN_BOUNDARY_CONTRACT'}
    missing = called - names - set(declarations)
    if missing:
        raise ValueError(f'calls without a definition or explicit boundary: {sorted(missing)}')
    return [declarations[n] for n in sorted(declarations)]


def inventory(root: Path):
    lock = json.loads((root / 'csrc/UPSTREAM.lock.json').read_text())
    profile_path = Path('csrc/config/v29301-profile.json')
    profile = json.loads((root / profile_path).read_text())
    locked = {}
    for rel, expected in lock['files'].items():
        path = CHECKOUT / rel
        if digest((root / path).read_bytes()) != expected:
            raise ValueError(f'upstream hash mismatch: {path}')
        locked[path.as_posix()] = expected
    actual = {p.relative_to(root).as_posix() for p in (root / CHECKOUT / 'Source').iterdir()
              if p.suffix in {'.c', '.h'}}
    if actual != set(locked):
        raise ValueError('upstream Source file set differs from lock')
    template = root / CHECKOUT / lock['config_template']
    if digest(template.read_bytes()) != lock['config_template_sha256']:
        raise ValueError('upstream config template hash mismatch')
    config = CHECKOUT / 'os_cfg.h'
    if digest((root / config).read_bytes()) != profile['expected_effective_os_cfg_sha256']:
        raise ValueError('effective configuration hash mismatch')
    inputs = {p: digest((root / p).read_bytes()) for p in [
        PORT / 'os_cpu.h', PORT / 'app_cfg.h', config, profile_path]}
    # Relative input/include paths keep compiler line markers reproducible.
    includes = [a for p in [PORT, CHECKOUT, CHECKOUT / 'Source'] for a in ['-I', str(p)]]
    source = str(CHECKOUT / 'Source/ucos_ii.c')
    with tempfile.TemporaryDirectory(prefix='ucos-source-inventory-') as directory:
        pp = Path(directory) / 'kernel.i'
        def parse(data):
            pp.write_bytes(data)
            return json.loads(run(root, ['clang', *CLANG_FLAGS, '-x', 'c', '-fsyntax-only',
                                         '-Xclang', '-ast-dump=json', str(pp)]))
        preprocessed = run(root, ['clang', *CLANG_FLAGS, *includes, '-E', source])
        ast = parse(preprocessed)
        functions = summarize(ast, preprocessed, root, locked)
        # GCC provides an independent preprocessing + syntax-check oracle.
        run(root, ['gcc', *GCC_FLAGS, *includes, '-fsyntax-only', source])
        gcc_pp = run(root, ['gcc', *GCC_FLAGS, *includes, '-E', source])
        compare_frontends(functions, summarize(parse(gcc_pp), gcc_pp, root, locked))
        macros = run(root, ['clang', *CLANG_FLAGS, *includes, '-E', '-dM', source])
    tags = catalogue(root, sorted(p for p in locked if p.endswith('.c')))
    for row in functions:
        tag = tags.get(row['name'])
        if not tag or (tag['path'], tag['line'], tag['end']) != (
                row['source'], row['first_line'], row['last_line']):
            raise ValueError(f"compiler/ctags source extent disagreement: {row['name']}")
    names = {f['name'] for f in functions}
    excluded = [{'name': name, 'source': tag['path'], 'first_line': tag['line'],
                 'last_line': tag['end'], 'source_file_sha256': locked[tag['path']],
                 'status': 'NOT_IN_CONFIGURED_TRANSLATION_UNIT'}
                for name, tag in sorted(tags.items()) if name not in names]
    effective = {}
    for line in macros.decode().splitlines():
        match = re.match(r'#define (OS_\w+) (.*)$', line)
        if match:
            effective[match[1]] = match[2]
    # Hashing os_cfg.h alone is insufficient: os_cpu.h is included afterwards
    # and could silently override the selected profile for both compilers.
    for name, value in re.findall(r'^#define\s+(OS_\w+)\s+(\d+u)\b',
                                  (root / config).read_text(), re.MULTILINE):
        if effective.get(name) != value:
            raise ValueError(f'effective macro differs from os_cfg.h: {name}')
    return {
        'schema_version': 1, 'target_release': lock['release'], 'target_commit': lock['commit'],
        'source_layer': 'PINNED_UPSTREAM_BEFORE_AUTHORIZED_REPAIRS',
        'proof_coverage_credit': False,
        'input_sha256': {str(p): h for p, h in sorted(inputs.items())},
        'preprocessed_sha256': digest(preprocessed),
        'tools': {name: run(root, [name, '--version']).decode().splitlines()[0]
                  for name in ['clang', 'gcc', 'ctags']},
        'clang_flags': CLANG_FLAGS, 'gcc_flags': GCC_FLAGS,
        'effective_os_macros': dict(sorted(effective.items())),
        'summary': {'configured_c_definitions': len(functions),
                    'categories': dict(sorted(Counter(r['category'] for r in functions).items())),
                    'declaration_only_boundaries': len(external_declarations(ast, functions)),
                    'unconfigured_source_catalogue': len(tags), 'excluded_definitions': len(excluded)},
        'functions': functions, 'boundaries': external_declarations(ast, functions),
        'excluded_definitions': excluded,
        'catalogue_limit': 'ctags all-branch source catalogue, not an AST of every configuration',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='compare with reviewed manifest; never rewrite')
    args = parser.parse_args()
    try:
        result = inventory(ROOT)
        text = json.dumps(result, ensure_ascii=False, indent=2) + '\n'
        path = ROOT / MANIFEST
        if args.check:
            if path.read_text() != text:
                raise ValueError('source inventory drift; inspect changes before regenerating')
        else:
            path.write_text(text)
        print('SOURCE INVENTORY: PASS', json.dumps(result['summary'], ensure_ascii=False))
        print('Scope: upstream only; authorized repairs and proof linkage remain open.')
    except (OSError, ValueError, KeyError) as error:
        parser.exit(1, f'SOURCE INVENTORY: FAIL: {error}\n')


if __name__ == '__main__':
    main()
