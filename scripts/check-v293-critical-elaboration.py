#!/usr/bin/env python3
"""Explicit critical macro mapping + occupied-return gate, NOT raw-port execution."""
import argparse
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
SOURCE = 'certiucos/v293/proofs/V293CriticalReturn.v'
PROBE = 'audit/probes/V293CriticalElaborationProbe.v'
NORMAL = 'V293_critical_prefix_normalization'
OCCUPIED = 'V293_occupied_critical_return'
ROOTS = [NORMAL, 'V293_port_rejects_wrong_token', OCCUPIED,
         'V293_occupied_critical_witness', 'V293_missing_port_has_no_step']


def digest(data):
    return hashlib.sha256(data).hexdigest()


def sha(path):
    return digest(path.read_bytes())


def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT/'scripts'/name)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def cleanup(tree, destination):
    rows = [{'path': str(p), 'size': p.stat().st_size, 'sha256': sha(p)}
            for p in sorted(tree.rglob('*')) if p.is_file()]
    destination.write_text(json.dumps(rows, indent=2)+'\n')
    for row in rows:
        p = Path(row['path'])
        assert p.stat().st_size == row['size'] and sha(p) == row['sha256']
    shutil.rmtree(tree)
    assert not tree.exists()


def check_saved_uses(fn, walk):
    """Only this function's local uses; no general alias/escape or frontend proof."""
    decls = [n for n in walk(fn) if n.get('kind') == 'VarDecl' and n.get('name') == 'cpu_sr']
    assert len(decls) == 1
    decl = decls[0]
    assert decl['type'].get('desugaredQualType') == 'unsigned int'
    assert [n.get('value') for n in walk(decl) if n.get('kind') == 'IntegerLiteral'] == ['0']
    refs, call_refs, calls = [], [], []
    for node in walk(fn):
        if node.get('kind') == 'DeclRefExpr' and node.get('referencedDecl', {}).get('id') == decl['id']:
            refs.append(node['id'])
        if node.get('kind') != 'CallExpr':
            continue
        children = node.get('inner', [])
        target = [x['referencedDecl']['name'] for x in walk(children[0]) if x.get('kind') == 'DeclRefExpr']
        if target not in [['V293_EnterCritical'], ['V293_ExitCritical']]:
            continue
        assert len(children) == 2
        arg = children[1]
        assert arg.get('kind') == 'UnaryOperator' and arg.get('opcode') == '&'
        assert arg['type']['qualType'] == 'OS_CPU_SR *'
        assert len(arg['inner']) == 1
        ref = arg['inner'][0]
        assert ref['kind'] == 'DeclRefExpr' and ref['referencedDecl']['id'] == decl['id']
        call_refs.append(ref['id'])
        calls.append(target[0])
    assert calls == ['V293_EnterCritical'] + ['V293_ExitCritical']*4
    assert sorted(refs) == sorted(call_refs) and len(set(refs)) == 5
    return {'cpu_sr_type': decl['type'], 'initializer': 0, 'all_uses_are_port_address_arguments': True,
            'use_count': len(refs), 'calls': calls, 'scope': 'manual mapping regression, not a verified frontend or port implementation'}


def configured_shape(out):
    c, t = module('check-v293-c-regressions.py'), module('inventory-v293-source.py')
    tree = Path(tempfile.mkdtemp(prefix='v293-critical-shape-'))
    try:
        source = Path('csrc/repaired/v2.93.01/checkout')
        hashes = c.materialize(tree/source, ('mutex', 'guard'))
        assert hashes == json.loads((ROOT/'audit/c-regressions.json').read_text())['variants']['both']['source_sha256']
        for name in ['os_cpu.h', 'app_cfg.h']:
            dst = tree/t.PORT/name
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT/t.PORT/name, dst)
        inc = [a for p in [t.PORT, source, source/'Source'] for a in ['-I', str(p)]]
        data = t.run(tree, ['clang', *t.CLANG_FLAGS, *inc, '-E', str(source/'Source/ucos_ii.c')])
        pp = tree/'kernel.i'
        pp.write_bytes(data)
        ast = json.loads(t.run(tree, ['clang', *t.CLANG_FLAGS, '-x', 'c', '-fsyntax-only', '-Xclang', '-ast-dump=json', str(pp)]))
        funcs = t.summarize(ast, data, tree, {str(source/p): h for p,h in hashes.items()})
        identity = next(f for f in funcs if f['name'] == 'OSTaskChangePrio')
        assert identity['preprocessed_definition_sha256'] == 'c29b633e71cf54c2d244eb87c7a5910a1f2973e6cd23d7a23769070b24bc2dbf'
        fn = next(n for n in t.walk(ast) if n.get('kind') == 'FunctionDecl' and n.get('name') == 'OSTaskChangePrio'
                  and any(x.get('kind') == 'CompoundStmt' for x in n.get('inner', [])))
        return {'function': identity, 'shape': check_saved_uses(fn, t.walk), 'source_sha256': hashes}
    finally:
        cleanup(tree, out/'configured-C-cleanup.json')


def through_qed(source, name):
    start = source.index('Theorem '+name+' :')
    end = source.index('Qed.', source.index('Proof.', start))+len('Qed.')
    return source[:end]+'\n'


def projections(source):
    normal = through_qed(source, NORMAL)
    definitions = source[:source.index('Theorem '+NORMAL+' :')]
    closure = source[source.index('(* Standard reflexive/transitive closure'):]
    occupied = through_qed(definitions + closure, OCCUPIED)
    return normal, occupied


def replace_once(source, old, new):
    assert source.count(old) == 1, old
    return source.replace(old, new)


def controls(source):
    normal, occupied = projections(source)
    definitions_end = occupied.index('Theorem '+OCCUPIED+' :')
    a, b = occupied[:definitions_end], occupied[definitions_end:]
    # Change definitions only, never the target Proof or its suffix.
    exit_sti = replace_once(a, 'sseq (sprim excrit) (srete (econst32 (Int.repr error)))',
                           'sseq (sprim sti) (srete (econst32 (Int.repr error)))')+b
    enter_cli = replace_once(a, '(sseq (sprim encrit) (V293_primitive_entry',
                            '(sseq (sprim cli) (V293_primitive_entry')+b
    h, p = b.split('Proof.', 1)
    wrong = a+replace_once(h, '(sskip (Some (Vint32 (Int.repr 40))))',
                         '(sskip (Some (Vint32 (Int.repr 41))))')+'Proof.'+p
    start = normal.index('Fixpoint V293_port_calls ')
    end = normal.index('Definition V293_port_normalize ', start)
    acceptor = normal[start:end]
    assert acceptor.count('| eaddrof (evar x) :: nil =>') == 2
    value = normal[:start]+acceptor.replace('| eaddrof (evar x) :: nil =>', '| evar x :: nil =>')+normal[end:]
    cases = [('ExitSti', exit_sti, OCCUPIED, occupied), ('EnterCli', enter_cli, OCCUPIED, occupied),
             ('WrongReturn', wrong, OCCUPIED, occupied), ('ValueArgument', value, NORMAL, normal)]
    for label, changed, target, original in cases:
        i = original.index('Proof.', original.index('Theorem '+target+' :'))
        j = changed.index('Proof.', changed.index('Theorem '+target+' :'))
        assert original[i:] == changed[j:], label
        assert original[:i] != changed[:j], label
        assert 'Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn' not in changed
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=False)
    inputs = {str(p.relative_to(ROOT)): sha(p) for d in ['framework', 'tactics', 'certiucos/v293']
              for p in sorted((ROOT/d).rglob('*.v'))}
    for name in [PROBE, '_CoqProject', 'scripts/check-v293-critical-elaboration.py',
                 'csrc/analysis-port/os_cpu.h', 'csrc/analysis-port/app_cfg.h',
                 'csrc/config/v29301-profile.json', 'csrc/repairs/FROZEN_SOURCE.json', 'audit/c-regressions.json']:
        inputs[name] = sha(ROOT/name)
    source = (ROOT/SOURCE).read_text()
    cases = controls(source)
    normal, occupied = projections(source)
    tree = Path(tempfile.mkdtemp(prefix='v293-critical-elaboration-'))
    positive = [('PositiveFull', source, ROOTS), ('PositiveOccupied', occupied, [OCCUPIED]),
                ('PositiveNormalization', normal, [NORMAL])]
    # Persist all exact controls and their immutable hashes BEFORE any coqc.
    protocol = []
    for label, s, roots in positive:
        full = s+'\n'+''.join('Print Assumptions '+r+'.\n' for r in roots)
        (tree/(label+'.v')).write_text(full)
        (out/(label+'.v.snapshot.txt')).write_text(full)
    for label, s, root, original in cases:
        (tree/(label+'.v')).write_text(s)
        (out/(label+'.v.snapshot.txt')).write_text(s)
        proof_line = s[:s.index('Proof.', s.index('Theorem '+root+' :'))].count('\n')+1
        protocol.append({'label': label, 'target': root, 'target_proof_line': proof_line,
                         'sha256': digest(s.encode()), 'proof_suffix_unchanged': True, 'downstream_credit': False})
    (out/'control-protocol.json').write_text(json.dumps(protocol, indent=2)+'\n')
    report = {'inputs': inputs, 'checks': {}, 'scope': 'explicit macro abstraction, occupied branch only; NOT raw sfexec execution, memory-token simulation, whole API or GOOD_OS',
              'controls_import_candidate_module': False, 'dependency_products': 'existing original 165 sources; no source-only clean-build credit'}
    coq = os.environ.get('COQBIN', '')
    def run(label, command):
        start = time.monotonic()
        with (out/(label+'.log')).open('w') as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, timeout=600)
        row = {'exit_code': result.returncode, 'elapsed_seconds': time.monotonic()-start, 'log': label+'.log'}
        report['checks'][label] = row
        (out/'result.partial.json').write_text(json.dumps(report, indent=2)+'\n')
        return row
    try:
        report['configured_C'] = configured_shape(out)
        (out/'configured-C.json').write_text(json.dumps(report['configured_C'], indent=2)+'\n')
        assert run('production-coqc', [coq+'coqc', '-q', '-R', str(ROOT), 'CertiOS', SOURCE])['exit_code'] == 0
        assert run('probe-coqc', [coq+'coqc', '-q', '-R', str(ROOT), 'CertiOS', PROBE])['exit_code'] == 0
        for label, mod in [('production', 'certiucos.v293.proofs.V293CriticalReturn'),
                           ('probe', 'audit.probes.V293CriticalElaborationProbe')]:
            assert run(label+'-coqchk', [coq+'coqchk', '-silent', '-R', str(ROOT), 'CertiOS', 'CertiOS.'+mod])['exit_code'] == 0
        flags = ['-q', '-R', str(ROOT), 'CertiOS', '-Q', str(tree), 'CriticalElaborationControls']
        checker = module('check-v293-task-prio-rekey.py')
        report['probe_assumptions'] = checker.checked_assumptions((out/'probe-coqc.log').read_text(), 6)
        report['positive_assumptions'] = {}
        for label, s, roots in positive:
            assert run(label, [coq+'coqc', *flags, str(tree/(label+'.v'))])['exit_code'] == 0
            report['positive_assumptions'][label] = checker.checked_assumptions((out/(label+'.log')).read_text(), len(roots))
        for entry in protocol:
            label = entry['label']
            assert sha(tree/(label+'.v')) == entry['sha256']
            row = run('negative-'+label, [coq+'coqc', *flags, str(tree/(label+'.v'))])
            match = re.search(r'line (\d+)', (out/row['log']).read_text())
            assert row['exit_code'] == 1 and match and int(match[1]) > entry['target_proof_line'], row
            row.update(entry, error_line=int(match[1]))
        report['passed'] = True
    finally:
        cleanup(tree, out/'temporary-cleanup.json')
        report['temporary_tree_removed'] = not tree.exists()
        report['inputs_unchanged'] = all(sha(ROOT/p) == h for p,h in inputs.items())
        (out/'result.json').write_text(json.dumps(report, indent=2)+'\n')
    assert report['inputs_unchanged']
    print(json.dumps({'passed': report['passed'], 'output_dir': str(out)}, indent=2))


if __name__ == '__main__':
    main()
