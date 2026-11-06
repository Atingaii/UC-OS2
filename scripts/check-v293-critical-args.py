#!/usr/bin/env python3
"""Check the three modeled error-call arguments against freshly configured C.

This is a narrow manual-mapping regression, not a verified C frontend.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CODE = 'certiucos/v293/code/V293OSTaskChangePrio.v'


def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / name)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def configured_calls():
    c = module('check-v293-c-regressions.py')
    t = module('inventory-v293-source.py')
    w = Path(tempfile.mkdtemp(prefix='v293-critical-args-'))
    try:
        source = Path('csrc/repaired/v2.93.01/checkout')
        hashes = c.materialize(w / source, ('mutex', 'guard'))
        assert hashes == json.loads((ROOT / 'audit/c-regressions.json').read_text())['variants']['both']['source_sha256']
        for name in ['os_cpu.h', 'app_cfg.h']:
            dst = w / t.PORT / name
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / t.PORT / name, dst)
        inc = [a for p in [t.PORT, source, source / 'Source'] for a in ['-I', str(p)]]
        data = t.run(w, ['clang', *t.CLANG_FLAGS, *inc, '-E', str(source / 'Source/ucos_ii.c')])
        pp = w / 'kernel.i'
        pp.write_bytes(data)
        ast = json.loads(t.run(w, ['clang', *t.CLANG_FLAGS, '-x', 'c', '-fsyntax-only', '-Xclang', '-ast-dump=json', str(pp)]))
        funcs = t.summarize(ast, data, w, {str(source / p): h for p, h in hashes.items()})
        identity = next(f for f in funcs if f['name'] == 'OSTaskChangePrio')
        assert identity['preprocessed_definition_sha256'] == 'c29b633e71cf54c2d244eb87c7a5910a1f2973e6cd23d7a23769070b24bc2dbf'
        fn = next(n for n in t.walk(ast) if n.get('kind') == 'FunctionDecl' and n.get('name') == 'OSTaskChangePrio' and any(x.get('kind') == 'CompoundStmt' for x in n.get('inner', [])))
        calls = []
        for n in t.walk(fn):
            if n.get('kind') != 'CallExpr':
                continue
            target = [x['referencedDecl']['name'] for x in t.walk(n['inner'][0]) if x.get('kind') == 'DeclRefExpr']
            if target not in [['V293_EnterCritical'], ['V293_ExitCritical']]:
                continue
            assert len(n['inner']) == 2
            arg = n['inner'][1]
            assert arg.get('kind') == 'UnaryOperator' and arg.get('opcode') == '&', arg
            ref = arg['inner'][0]
            assert ref.get('kind') == 'DeclRefExpr' and ref['referencedDecl']['name'] == 'cpu_sr'
            assert arg['type']['qualType'] == 'OS_CPU_SR *'
            assert ref['type'].get('desugaredQualType') == 'unsigned int'
            calls.append({'target': target[0], 'argument': arg})
        assert [c['target'] for c in calls] == ['V293_EnterCritical'] + ['V293_ExitCritical'] * 4
        return {'function': identity, 'calls': calls}
    finally:
        # Only this invocation's generated tree. Confirm every file before removal.
        manifest = [(p, p.stat().st_size, hashlib.sha256(p.read_bytes()).hexdigest()) for p in w.rglob('*') if p.is_file()]
        for p, size, digest in manifest:
            assert p.stat().st_size == size and hashlib.sha256(p.read_bytes()).hexdigest() == digest
        shutil.rmtree(w)


def model_calls(code):
    code = re.sub(r'\(\*.*?\*\)', '', code, flags=re.S)
    entry = code.split('Definition V293_task_prio_entry_lookup\n', 1)[1].split('Definition ', 1)[0]
    reserved = code.split('Definition V293_task_prio_reserved_error ', 1)[1].split('Definition ', 1)[0]
    # Capture each actual call immediately followed by its distinct return.
    pattern = r'\bsseq\s+\(scall exit_id (.*?)\)\s+\(srete \(econst32 \(Int.repr (40|41|67)\)\)\)'
    return [(int(code), ' '.join(arg.split())) for arg, code in re.findall(pattern, entry + reserved, re.S)]


def check_model(code):
    actual = model_calls(code)
    expected = [(n, '(eaddrof (evar cpu_sr) :: nil)') for n in [40, 41, 67]]
    assert actual == expected, f'error-call argument mismatch: expected {expected!r}; actual {actual!r}'
    return actual


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    evidence = configured_calls()
    if args.output:
        args.output.write_text(json.dumps(evidence, indent=2) + '\n')
    check_model((ROOT / CODE).read_text())
    print('PASS: fresh C has &cpu_sr in 1 enter/4 exit calls; all 3 modeled error exits pass its address.')


if __name__ == '__main__':
    main()
