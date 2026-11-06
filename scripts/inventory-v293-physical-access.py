#!/usr/bin/env python3
"""Inventory direct C field/global accesses, not alias effects or proof coverage."""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
REPORT = Path('audit/physical-access-inventory.json')
LIMITS = [
    'Direct syntactic accesses only; no points-to or alias analysis.',
    'No transitive callee effects; inspect direct_calls and boundary contracts separately.',
    'Address escape, indirect dereference and whole-record copies require manual obligations.',
    'Caller output structs, free-list objects and live objects are not distinguished by field name.',
    'No ownership, initialization reachability, C-to-Coq correspondence or GOOD_OS credit.',
]


def load(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), ROOT / 'scripts' / name)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha(data):
    return hashlib.sha256(data).hexdigest()


def serialize(value):
    return json.dumps(value, ensure_ascii=False, indent=2) + '\n'


def walk(node, ancestors=()):
    # Clang retains absent ForStmt slots as {}; preserve sibling indices.
    if not node:
        return
    yield node, ancestors
    for index, child in enumerate(node.get('inner', [])):
        yield from walk(child, (*ancestors, (node, index)))


def access_mode(ancestors):
    """Classify the selected lvalue, not a pointer's eventual pointee.

    LValueToRValue ends the lvalue path: p->ptr[i] = x reads ptr,
    whereas p->array[i] = x writes an element of array.
    """
    if any(p['kind'] == 'UnaryExprOrTypeTraitExpr' for p, _ in ancestors):
        return 'unevaluated'
    array_address = False
    for parent, index in reversed(ancestors):
        kind = parent['kind']
        if kind == 'ImplicitCastExpr':
            if parent.get('castKind') == 'LValueToRValue':
                return 'read'
            if parent.get('castKind') == 'ArrayToPointerDecay':
                array_address = True
            continue
        if kind == 'ParenExpr':
            continue
        if kind == 'ArraySubscriptExpr' and index == 0:
            array_address = False
            continue
        if kind == 'UnaryOperator':
            if parent.get('opcode') == '&':
                return 'address'
            if parent.get('opcode') in ('++', '--'):
                return 'read_write'
        if kind == 'CompoundAssignOperator' and index == 0:
            return 'read_write'
        if kind == 'BinaryOperator' and parent.get('opcode') == '=' and index == 0:
            return 'write'
        if kind == 'MemberExpr':
            return 'subobject_unresolved'
        return 'address' if array_address else 'unclassified'
    return 'unclassified'


def offsets(node):
    begin, end = node['range']['begin'], node['range']['end']
    # Input is already preprocessed: no macro expansion offsets may be guessed.
    return begin['offset'], end['offset'] + end['tokLen']


def scan(ast, data, source_map):
    fields, globals_ = {}, {}
    for node in ast.get('inner', []):
        if node['kind'] == 'RecordDecl' and node.get('completeDefinition'):
            for field in node.get('inner', []):
                if field['kind'] == 'FieldDecl':
                    fields[field['id']] = (node.get('name', '<anonymous>'), field['name'])
        if node['kind'] == 'VarDecl':
            globals_[node['id']] = node['name']
    functions = []
    for function in ast.get('inner', []):
        bodies = [c for c in function.get('inner', []) if c['kind'] == 'CompoundStmt']
        if function['kind'] != 'FunctionDecl' or not bodies:
            continue
        accesses = []
        dereferences = whole_record_assignments = indirect_calls = 0
        for node, parents in walk(bodies[0]):
            kind = node['kind']
            if kind == 'UnaryOperator' and node.get('opcode') == '*':
                dereferences += 1
            if kind == 'BinaryOperator' and node.get('opcode') == '=':
                tp = node.get('type', {}).get('desugaredQualType', node.get('type', {}).get('qualType', ''))
                if tp.startswith(('struct ', 'union ')) and '*' not in tp:
                    whole_record_assignments += 1
            if kind == 'CallExpr':
                callee = node.get('inner', [])[:1]
                if not any(n.get('referencedDecl', {}).get('kind') == 'FunctionDecl'
                           for c in callee for n, _ in walk(c)):
                    indirect_calls += 1
            if kind == 'MemberExpr':
                ref = node.get('referencedMemberDecl')
                if ref not in fields:
                    raise ValueError('member declaration not resolved; do not silently omit it')
                record, name = fields[ref]
                resource = f'{record}.{name}'
                storage = 'field'
            elif kind == 'DeclRefExpr' and node.get('referencedDecl', {}).get('id') in globals_:
                resource = globals_[node['referencedDecl']['id']]
                storage = 'global'
            else:
                continue
            begin, end = offsets(node)
            file, line = source_map.at(begin)
            accesses.append({'storage': storage, 'resource': resource, 'mode': access_mode(parents),
                             'source': file, 'line': line, 'begin_byte': begin,
                             'end_byte_exclusive': end, 'expression': data[begin:end].decode()})
        summary = {}
        for access in accesses:
            key = access['resource']
            summary.setdefault(key, set()).add(access['mode'])
        functions.append({'name': function['name'],
                          'direct_resources': {k: sorted(v) for k, v in sorted(summary.items())},
                          'accesses': accesses,
                          'unresolved_effect_sites': {'explicit_pointer_dereferences': dereferences,
                              'whole_record_assignments': whole_record_assignments,
                              'indirect_calls': indirect_calls}})
    return sorted(functions, key=lambda f: f['name'])


def record_layouts(text, ast):
    """Only flat configured structs are accepted; no silent nested-layout guess."""
    result = {}
    definitions = {n['name']: n for n in ast.get('inner', [])
                   if n['kind'] == 'RecordDecl' and n.get('completeDefinition') and n.get('name')}
    for block in text.split('*** Dumping AST Record Layout'):
        head = re.search(r'^\s*0 \| struct (\w+)\s*$', block, re.M)
        if not head or head[1] not in definitions:
            continue
        record = head[1]
        declared = [f for f in definitions[record].get('inner', []) if f['kind'] == 'FieldDecl']
        rows = re.findall(r'^\s*(\d+) \|   (\S[^\n]*)$', block, re.M)
        if len(rows) != len(declared):
            raise ValueError(f'{record}: unsupported or incomplete field layout')
        fields = {}
        for (offset, description), field in zip(rows, declared):
            if not re.search(r'\b' + re.escape(field['name']) + r'$', description):
                raise ValueError(f'{record}: AST/layout field disagreement')
            fields[field['name']] = {'offset': int(offset), 'type': field['type']['qualType']}
        size = re.search(r'\[sizeof=(\d+), align=(\d+)\]', block)
        if not size:
            raise ValueError(f'{record}: missing size')
        result[record] = {'size': int(size[1]), 'align': int(size[2]), 'fields': fields}
    if set(result) != set(definitions):
        raise ValueError('record-layout set differs from configured AST')
    return dict(sorted(result.items()))


def collect():
    freeze_tool = load('freeze-v293-source.py')
    freeze, inventory = freeze_tool.collect(ROOT)
    if serialize(freeze) != (ROOT / freeze_tool.FREEZE).read_text():
        raise ValueError('frozen source identity drift')
    if serialize(inventory) != (ROOT / freeze_tool.INVENTORY).read_text():
        raise ValueError('reviewed repaired inventory drift')
    inv = load('inventory-v293-source.py')
    c = load('check-v293-c-regressions.py')
    with tempfile.TemporaryDirectory(prefix='v293-physical-access-') as directory:
        work = Path(directory)
        try:
            source = work / freeze_tool.SOURCE
            if c.materialize(source, ('mutex', 'guard')) != freeze['program']['source_sha256']:
                raise ValueError('reconstructed source drift')
            for name in ('os_cpu.h', 'app_cfg.h'):
                dest = work / inv.PORT / name
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / inv.PORT / name, dest)
            includes = [a for p in [inv.PORT, freeze_tool.SOURCE, freeze_tool.SOURCE / 'Source']
                        for a in ['-I', str(p)]]
            data = inv.run(work, ['clang', *inv.CLANG_FLAGS, *includes, '-E',
                                 str(freeze_tool.SOURCE / 'Source/ucos_ii.c')])
            if sha(data) != inventory['preprocessed_sha256']:
                raise ValueError('preprocessed identity drift')
            proc = subprocess.run(['clang', *inv.CLANG_FLAGS, '-x', 'c', '-fsyntax-only',
                                   '-Xclang', '-ast-dump=json', '-'], cwd=work,
                                  input=data, capture_output=True, check=True)
            ast = json.loads(proc.stdout)
            locations = inv.summarize(ast, data, work,
                {(freeze_tool.SOURCE / p).as_posix(): h for p, h in freeze['program']['source_sha256'].items()})
            if locations != inventory['functions']:
                raise ValueError('definition/body/location identities drift')
            layout = subprocess.run(['clang', *inv.CLANG_FLAGS, '-x', 'c', '-fsyntax-only',
                                     '-Xclang', '-fdump-record-layouts-complete', '-'], cwd=work,
                                    input=data, capture_output=True, check=True).stdout.decode()
            rows = scan(ast, data, inv.SourceMap(data))
            locations = {f['name']: f for f in locations}
            for row in rows:
                row['identity'] = locations[row['name']]
            layouts = record_layouts(layout, ast)
        finally:
            # Confirm every owned temporary file before TemporaryDirectory removes any.
            files = sorted(p for p in work.rglob('*') if p.is_file())
            cleanup = [{'path': str(p.relative_to(work)), 'bytes': p.stat().st_size,
                        'sha256': sha(p.read_bytes()), 'category': 'reconstructed source/analysis header'}
                       for p in files]
            for item in cleanup:
                path = work / item['path']
                if path.is_symlink() or sha(path.read_bytes()) != item['sha256']:
                    raise ValueError('owned temporary tree changed before cleanup')
    inputs = {str(p): sha((ROOT / p).read_bytes()) for p in [
        freeze_tool.FREEZE, freeze_tool.INVENTORY, Path('scripts/inventory-v293-physical-access.py'),
        Path('scripts/freeze-v293-source.py'), Path('scripts/inventory-v293-source.py'),
        Path('scripts/check-v293-c-regressions.py')]}
    return {'schema_version': 1, 'scope': 'DIRECT_C_ACCESSES_NOT_COMPLETE_MEMORY_EFFECTS',
            'proof_coverage_credit': False, 'source_identity_sha256': freeze['source_identity_sha256'],
            'preprocessed_sha256': sha(data), 'input_sha256': inputs,
            'clang': inventory['tools']['clang'], 'clang_flags': inv.CLANG_FLAGS,
            'limitations': LIMITS, 'record_layouts': layouts, 'functions': rows,
            'summary': {'functions': len(rows), 'records': len(layouts),
                        'access_sites': sum(len(r['accesses']) for r in rows),
                        'modes': dict(sorted(Counter(a['mode'] for r in rows for a in r['accesses']).items()))},
            'cleanup': {'targets': cleanup, 'all_targets_validated_before_removal': True,
                        'temporary_tree_removed': not work.exists()}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', action='store_true', help='create first report only; never overwrite')
    args = parser.parse_args()
    try:
        result = collect()
        path = ROOT / REPORT
        if args.record:
            with path.open('x') as output:
                output.write(serialize(result))
        elif json.loads(path.read_text()) != result:
            raise ValueError('physical access inventory drift; existing evidence was not rewritten')
        print('PHYSICAL ACCESS INVENTORY: PASS', serialize(result['summary']).strip())
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        parser.exit(1, f'PHYSICAL ACCESS INVENTORY: FAIL: {error}\n')


if __name__ == '__main__':
    main()
