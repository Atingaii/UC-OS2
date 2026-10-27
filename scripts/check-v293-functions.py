#!/usr/bin/env python3
"""Replay the frozen OSVersion body, local proof and one-function API unit.

The Clang frontend and this deliberately restricted emitter are trusted source
correspondence tools, not a verified C compiler. Unsupported syntax is rejected.
This gate proves a nonempty one-function API unit, not whole-kernel linkage.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CODE = 'certiucos/v293/code/V293OSVersion.v'
SPEC = 'certiucos/v293/spec/V293OSVersionSpec.v'
PROOF = 'certiucos/v293/proofs/V293OSVersionProof.v'
API = 'certiucos/v293/proofs/V293OSVersionAPI.v'
REPORT = 'audit/function-evidence-stage09.json'
SCOPE = 'CHECKED_SOURCE_AND_SINGLE_FUNCTION_API_COMPONENT_NOT_GOOD_OS'
ROOTS = ['V293_OSVersion_local_hoare', 'V293_OSVersion_post_exact',
         'V293_OSVersion_execution']
API_ROOTS = ['V293_OSVersion_api_contract', 'V293_OSVersion_api_rule',
             'V293_OSVersion_api_builders']
GATES = ['located', 'modeled', 'specified', 'local_hoare', 'component_linked']


def load(root, name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), root / 'scripts' / name)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def children(node, kind, count):
    if node.get('kind') != kind or len(node.get('inner', [])) != count:
        raise ValueError(f'unsupported AST shape: expected {kind} with {count} children')
    return node.get('inner', [])


def decode_osversion(node):
    """Accept exactly a no-argument UINT16 function returning a UINT32 literal.

    Clang must resolve INT16U to unsigned short at the implicit cast. The
    i386 target fixes these widths. No calls, globals, locals, attributes,
    control flow or extra statements are silently discarded.
    """
    if (node.get('name') != 'OSVersion' or node.get('type', {}).get('qualType') != 'INT16U (void)'
            or node.get('storageClass') or node.get('variadic') or node.get('inline')):
        raise ValueError('unsupported OSVersion signature/linkage')
    body, = children(node, 'FunctionDecl', 1)
    ret, = children(body, 'CompoundStmt', 1)
    cast, = children(ret, 'ReturnStmt', 1)
    paren, = children(cast, 'ImplicitCastExpr', 1)
    if (cast.get('castKind') != 'IntegralCast'
            or cast.get('type', {}).get('desugaredQualType') != 'unsigned short'):
        raise ValueError('unsupported return conversion; require unsigned-short integral cast')
    literal, = children(paren, 'ParenExpr', 1)
    children(literal, 'IntegerLiteral', 0)
    if any(n.get('type', {}).get('qualType') != 'unsigned int' for n in [paren, literal]):
        raise ValueError('unsupported literal type; require unsigned int')
    text = literal.get('value', '')
    if not re.fullmatch(r'[0-9]+', text) or not 0 <= int(text) < 2**32:
        raise ValueError('unsupported UINT32 literal')
    return int(text)


def emit_osversion(literal):
    return '''(* Generated from the frozen, configured Clang AST by check-v293-functions.py.
   The unsigned-int to unsigned-short return conversion is explicit. *)
Require Import CertiOS.framework.model.memory.
Require Import CertiOS.framework.model.language.

Definition V293_OSVersion_expr : expr :=
  ecast (econst32 (Int.repr %d)) Tint16.

Definition V293_OSVersion_body : stmts := srete V293_OSVersion_expr.

Definition V293_OSVersion_function : function :=
  (Tint16, dnil, dnil, V293_OSVersion_body).
''' % literal


PROBE = '''Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSVersion.
Require Import CertiOS.certiucos.v293.proofs.V293OSVersionProof.

(* The expected type is independent of the exported specification definition.
   Merely finding a theorem with the right name is not proof evidence. *)
Definition checked_local_hoare : forall Spec sd li I tid frame,
  InfRules Spec sd li I
    (fun result => [| result = Some (Vint32 (Int.repr 29300)) |] ** frame)
    Afalse frame V293_OSVersion_body Afalse tid := V293_OSVersion_local_hoare.

Definition checked_execution : forall p ge caller M f ks,
  cstepstar p
    (curs V293_OSVersion_body, (kenil, kcall f V293_OSVersion_body caller ks))
    (ge, emp, M)
    (curs (sskip (Some (Vint32 (Int.repr 29300)))), (kenil, ks)) (ge, caller, M)
  := V293_OSVersion_execution.

Definition checked_function :
  V293_OSVersion_function = (Tint16, dnil, dnil, V293_OSVersion_body) := eq_refl.
'''

API_PROBE = '''Require Import CertiOS.certiucos.v293.proofs.V293OSVersionAPI.

(* Inline both maps and the result: neither an empty unit nor a substituted
   permissive API specification can silently satisfy the checked interface. *)
Definition checked_api_rule : forall version_id Spec sd li I lg,
  APIRule
    (fun f => if Z.eq_dec f version_id then
      Some (Tint16, dnil, dnil, V293_OSVersion_body) else None)
    (fun f => if Z.eq_dec f version_id then
      Some (fun _ => spec_done (Some (Vint32 (Int.repr 29300))), (Tint16, nil))
      else None) Spec sd li I lg := V293_OSVersion_api_rule.

Definition checked_api_contract : forall P f Spec sd li I lg tid vl pre post,
  P f = Some (Tint16, dnil, dnil, V293_OSVersion_body) ->
  Some pre = BuildPreA' P f
    (fun _ => spec_done (Some (Vint32 (Int.repr 29300))), (Tint16, nil)) vl li tid lg ->
  Some post = BuildRetA' P f
    (fun _ => spec_done (Some (Vint32 (Int.repr 29300))), (Tint16, nil)) vl li tid lg ->
  InfRules Spec sd li I post Afalse pre V293_OSVersion_body Afalse tid
  := V293_OSVersion_api_contract.

Definition checked_api_builders : forall version_id li tid lg,
  exists pre post,
    Some pre = BuildPreA' (V293_OSVersion_api_unit version_id) version_id
      V293_OSVersion_api nil li tid lg /\\
    Some post = BuildRetA' (V293_OSVersion_api_unit version_id) version_id
      V293_OSVersion_api nil li tid lg := V293_OSVersion_api_builders.
'''


def source_replay(root, work):
    freeze = load(root, 'freeze-v293-source.py')
    # Complete source/configuration replay happens before any translation.
    actual_freeze, inventory = freeze.collect(root)
    for path, actual in [(freeze.FREEZE, actual_freeze), (freeze.INVENTORY, inventory)]:
        if (root / path).read_text() != freeze.serialize(actual):
            raise ValueError(f'frozen source drift: {path}')
    c = load(root, 'check-v293-c-regressions.py')
    u = load(root, 'inventory-v293-source.py')
    source = work / freeze.SOURCE
    if c.materialize(source, ('mutex', 'guard')) != actual_freeze['program']['source_sha256']:
        raise ValueError('translation source differs from frozen program')
    for rel in ['os_cpu.h', 'app_cfg.h']:
        dest = work / u.PORT / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root / u.PORT / rel, dest)
    includes = [a for p in [u.PORT, freeze.SOURCE, freeze.SOURCE / 'Source']
                for a in ['-I', str(p)]]
    unit = str(freeze.SOURCE / 'Source/ucos_ii.c')

    def parse(data):
        (work / 'kernel.i').write_bytes(data)
        ast = json.loads(u.run(work, ['clang', *u.CLANG_FLAGS, '-x', 'c', '-fsyntax-only',
                                    '-Xclang', '-ast-dump=json', 'kernel.i']))
        nodes = [n for n in u.definitions(ast) if n['name'] == 'OSVersion']
        if len(nodes) != 1:
            raise ValueError('expected exactly one configured OSVersion definition')
        return nodes[0]

    data = u.run(work, ['clang', *u.CLANG_FLAGS, *includes, '-E', unit])
    if hashlib.sha256(data).hexdigest() != inventory['preprocessed_sha256']:
        raise ValueError('translation preprocessed input differs from frozen inventory')
    node = parse(data)
    literal = decode_osversion(node)
    other = parse(u.run(work, ['gcc', *u.GCC_FLAGS, *includes, '-E', unit]))
    if decode_osversion(other) != literal:
        raise ValueError('GCC/Clang configured literal disagreement')
    if (root / CODE).read_text() != emit_osversion(literal):
        raise ValueError('CoqImp model differs from actual configured AST emission')
    return inventory, node, literal


def input_hashes(root):
    paths = {p.relative_to(root).as_posix() for tree in ['framework', 'tactics', 'certiucos/v293']
             for p in (root / tree).rglob('*.v')}
    freeze = json.loads((root / 'csrc/repairs/FROZEN_SOURCE.json').read_text())
    paths |= set(freeze['input_sha256'])
    paths |= {'csrc/repairs/FROZEN_SOURCE.json', 'audit/repaired-source-inventory.json',
              'scripts/check-v293-functions.py', 'scripts/coverage-audit.py', 'scripts/project-audit.py',
              'scripts/check-memory-trust.py', 'scripts/v293-scheduler-source.py', 'Makefile', '_CoqProject'}
    return {p: sha(root / p) for p in sorted(paths)}


def inspect(root=ROOT):
    coqbin = os.environ.get('COQBIN', '')
    report = {'schema_version': 1, 'scope': SCOPE, 'input_sha256': input_hashes(root),
              'kernel_GOOD_OS_proved': False, 'checks': {}}

    def run(label, command, cwd=root, timeout=1800):
        proc = subprocess.run(command, cwd=cwd, text=True, capture_output=True, timeout=timeout)
        result = {'exit_code': proc.returncode, 'stdout': proc.stdout, 'stderr': proc.stderr}
        report['checks'][label] = result
        return result

    def passed(row, label):
        if row['exit_code']:
            raise ValueError(f'{label} failed: {row["stdout"]}{row["stderr"]}')

    version = run('version', [coqbin + 'coqc', '--version'])
    passed(version, 'version')
    if not re.search(r'version 8\.18\.0(?: |$)', version['stdout'], re.MULTILINE):
        raise ValueError('function checks require Coq 8.18.0')
    with tempfile.TemporaryDirectory(prefix='ucos-function-proof-') as directory:
        work = Path(directory)
        inventory, node, literal = source_replay(root, work)
        scheduler = load(root, 'v293-scheduler-source.py')
        scheduler_info, _, scheduler_table = scheduler.check_source(root, work, load)
        report['source_identity_sha256'] = inventory['source_identity_sha256']
        report['functions'] = {'OSVersion': {
            'gates': GATES,
            'location': next(f for f in inventory['functions'] if f['name'] == 'OSVersion'),
            'model': CODE, 'specification': SPEC, 'proof': PROOF, 'roots': ROOTS,
            'component': API, 'component_roots': API_ROOTS,
            'component_scope': 'SINGLE_FUNCTION_API_UNIT_FOR_ANY_LINKER_ID_NOT_FULL_KERNEL',
            'source_literal': literal, 'return_conversion': 'unsigned int -> unsigned short',
            'correspondence': 'RESTRICTED_TRUSTED_CLANG_AST_EMITTER_NOT_VERIFIED_C_COMPILER'}}
        passed(run('project_audit', ['python3', 'scripts/project-audit.py']), 'project audit')
        # Rebuild every dependency from source, without copying any .vo or
        # consulting the checkout's build products. Positive and mutant proofs
        # below use precisely this freshly compiled framework/tactic closure.
        build = work / 'build'
        for rel in report['input_sha256']:
            if rel.endswith('.v') or rel in {'Makefile', '_CoqProject'}:
                target = build / rel
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(root / rel, target)
        passed(run('clean_build', ['make', 'build', f'COQBIN={coqbin}', 'JOBS=2'], build),
               'isolated clean build')

        scheduler_info.update(scheduler.check_proofs(root, work, build, coqbin, run, load, scheduler_table))
        report['scheduler_checkpoint'] = scheduler_info

        def compile_tree(label, model=None, spec=None, proof=None, api=None,
                         probe=False, component=True):
            dest = work / label
            flags = ['-R', str(build / 'framework'), 'CertiOS.framework',
                     '-R', str(build / 'tactics'), 'CertiOS.tactics',
                     '-R', str(dest / 'certiucos'), 'CertiOS.certiucos',
                     '-R', str(dest / 'checks'), 'FunctionCheck']
            (dest / 'checks').mkdir(parents=True)
            files = [(CODE, model), (SPEC, spec), (PROOF, proof)]
            if component:
                files.append((API, api))
            for rel, body in files:
                path = dest / rel
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text((root / rel).read_text() if body is None else body)
                row = run(label + ':' + Path(rel).stem, [coqbin + 'coqc', '-q', *flags, str(path)], dest)
                if row['exit_code']:
                    return row, flags, dest
            if probe:
                path = dest / 'checks/Contract.v'
                roots = ROOTS + (API_ROOTS if component else [])
                path.write_text(PROBE + (API_PROBE if component else '') + '\n'
                                + '\n'.join(f'Print Assumptions {r}.' for r in roots))
                return run(label + ':contract', [coqbin + 'coqc', '-q', *flags, str(path)], dest), flags, dest
            return row, flags, dest

        row, flags, dest = compile_tree('positive', probe=True)
        passed(row, 'isolated source-function contract')
        # These roots need no new assumptions; the frame lemmas may inherit
        # precisely the already accepted standard framework assumptions.
        trust = load(root, 'check-memory-trust.py')
        output = row['stdout']
        sections = output.split('Axioms:')[1:]
        actual = set()
        for section in sections:
            section = section.split('Closed under the global context')[0]
            actual |= set(trust.check_assumptions(section, trust.FRAMEWORK_ALLOWED))
        if output.count('Axioms:') + output.count('Closed under the global context') != len(ROOTS + API_ROOTS):
            raise ValueError('missing or ambiguous function-root assumption output')
        report['root_assumptions'] = sorted(actual)
        passed(run('coqchk', [coqbin + 'coqchk', '-silent', *flags,
                   'CertiOS.certiucos.v293.proofs.V293OSVersionProof',
                   'CertiOS.certiucos.v293.proofs.V293OSVersionAPI', 'FunctionCheck.Contract'], dest), 'coqchk')

        # Prospective single-factor controls, not just early frozen-hash failures.
        # 1. A changed literal is accepted by the emitter but rejected by the
        #    unchanged semantic result proof at V293_OSVersion_eval.
        changed = copy.deepcopy(node)
        cast = changed['inner'][0]['inner'][0]['inner'][0]
        cast['inner'][0]['inner'][0]['value'] = str(literal + 1)
        mutant = emit_osversion(decode_osversion(changed))
        row, _, _ = compile_tree('wrong_literal', model=mutant)
        proof = (root / PROOF).read_text()
        match = re.search(r'line (\d+), characters', row['stderr'])
        lo = proof[:proof.index('Lemma V293_OSVersion_eval')].count('\n') + 1
        hi = proof[:proof.index('Qed.')].count('\n') + 1
        if row['exit_code'] != 1 or not match or not lo <= int(match[1]) <= hi:
            raise ValueError('literal fault did not reach the designated evaluation proof')
        # 2. An inconsistent precondition can make a theorem trivially compile.
        #    Its name is retained, but the independent contract probe rejects it.
        start = proof.index('Theorem V293_OSVersion_local_hoare')
        end = proof.index('Qed.', start) + len('Qed.')
        bad_hoare = '''Theorem V293_OSVersion_local_hoare : forall Spec sd li I tid frame,
  InfRules Spec sd li I (V293_OSVersion_post frame) Afalse
    Afalse V293_OSVersion_body Afalse tid.
Proof.
  intros. unfold V293_OSVersion_body.
  eapply rete_rule with (v := V293_OSVersion_result) (t := Tint16).
  intros s Hfalse. contradiction.
Qed.'''
        # Isolate the local contract control: do not let the new downstream API
        # proof reject first and masquerade as the independent probe's result.
        row, _, _ = compile_tree('false_precondition', proof=proof[:start] + bad_hoare + proof[end:],
                                 probe=True, component=False)
        match = re.search(r'line (\d+), characters', row['stderr'])
        lo = PROBE[:PROBE.index('Definition checked_local_hoare')].count('\n') + 1
        hi = PROBE[:PROBE.index('Definition checked_execution')].count('\n')
        if (row['exit_code'] != 1 or not match or not lo <= int(match[1]) <= hi
                or report['checks'].get('false_precondition:V293OSVersionProof', {}).get('exit_code') != 0):
            raise ValueError(f'vacuous theorem did not reach the designated contract rejection: {row}')
        report['negative_controls'] = {
            'literal_changed_only': 'REJECTED_AT_V293_OSVersion_eval',
            'false_precondition_only': 'MUTANT_ROOT_COMPILED_REJECTED_AT_checked_local_hoare'}
        api = (root / API).read_text()

        def api_rejected(label, mutant, declaration):
            row, _, _ = compile_tree(label, api=mutant)
            match = re.search(r'line (\d+), characters', row['stderr'])
            start = mutant.index(declaration)
            lo = mutant[:start].count('\n') + 1
            hi = mutant[:mutant.index('Qed.', start)].count('\n') + 1
            if (row['exit_code'] != 1 or not match or not lo <= int(match[1]) <= hi
                    or report['checks'].get(label + ':V293OSVersionProof', {}).get('exit_code') != 0):
                raise ValueError(f'{label} did not reach designated API obligation: {row}')

        # Each changes just one semantic factor; all base proofs still compile.
        wrong_result = api.replace('spec_done (Some V293_OSVersion_result)',
                                   'spec_done (Some (Vint32 (Int.repr 29301)))', 1)
        api_rejected('wrong_api_result', wrong_result, 'Theorem V293_OSVersion_api_contract')
        missing_entry = api.replace('then Some V293_OSVersion_function else None',
                                    'then None else None', 1)
        api_rejected('missing_api_entry', missing_entry, 'Lemma V293_OSVersion_api_domains')
        report['negative_controls'].update({
            'api_result_changed_only': 'REJECTED_AT_V293_OSVersion_api_contract',
            'api_entry_removed_only': 'REJECTED_AT_V293_OSVersion_api_domains'})
    if input_hashes(root) != report['input_sha256']:
        raise ValueError('function gate inputs changed during inspection')
    return report


def validate_record(root, report):
    """Static identity check. Live Coq replay is deliberately a separate gate."""
    if (report['schema_version'] != 1 or report['scope'] != SCOPE
            or report['kernel_GOOD_OS_proved'] is not False):
        raise ValueError('unsupported function evidence scope/schema')
    if input_hashes(root) != report['input_sha256']:
        raise ValueError('stale function evidence input identity; rerun check-functions')
    inventory = json.loads((root / 'audit/repaired-source-inventory.json').read_text())
    if report['source_identity_sha256'] != inventory['source_identity_sha256']:
        raise ValueError('function evidence source identity differs')
    expected = {'OSVersion': {
        'gates': GATES,
        'location': next(f for f in inventory['functions'] if f['name'] == 'OSVersion'),
        'model': CODE, 'specification': SPEC, 'proof': PROOF, 'roots': ROOTS,
        'component': API, 'component_roots': API_ROOTS,
        'component_scope': 'SINGLE_FUNCTION_API_UNIT_FOR_ANY_LINKER_ID_NOT_FULL_KERNEL',
        'source_literal': 29300, 'return_conversion': 'unsigned int -> unsigned short',
        'correspondence': 'RESTRICTED_TRUSTED_CLANG_AST_EMITTER_NOT_VERIFIED_C_COMPILER'}}
    if report['functions'] != expected:
        raise ValueError('function evidence does not match checked source/model/contracts')
    checks = report['checks']
    required = ['version', 'project_audit', 'clean_build', 'positive:V293OSVersion',
                'positive:V293OSVersionSpec', 'positive:V293OSVersionProof',
                'positive:V293OSVersionAPI', 'positive:contract', 'coqchk']
    if any(checks[k]['exit_code'] != 0 for k in required):
        raise ValueError('function evidence contains an unsuccessful positive gate')
    if (checks['wrong_literal:V293OSVersionProof']['exit_code'] != 1
            or checks['false_precondition:V293OSVersionProof']['exit_code'] != 0
            or checks['false_precondition:contract']['exit_code'] != 1
            or checks['wrong_api_result:V293OSVersionProof']['exit_code'] != 0
            or checks['wrong_api_result:V293OSVersionAPI']['exit_code'] != 1
            or checks['missing_api_entry:V293OSVersionProof']['exit_code'] != 0
            or checks['missing_api_entry:V293OSVersionAPI']['exit_code'] != 1):
        raise ValueError('function evidence is missing designated negative controls')
    if not set(report['root_assumptions']) <= load(root, 'check-memory-trust.py').FRAMEWORK_ALLOWED:
        raise ValueError('unexpected function-root assumptions')
    scheduler = load(root, 'v293-scheduler-source.py')
    checkpoint = report['scheduler_checkpoint']
    if checkpoint != {
            'shift': 3, 'lookup_entries': 256,
            'scope': 'SOURCE_BOUND_READS_AND_UNINTERLEAVED_UPDATES_NOT_FUNCTION_HOARE',
            'coverage_credit': False, 'roots': scheduler.ROOTS,
            'root_assumptions': checkpoint['root_assumptions'],
            'negative_controls': scheduler.NEGATIVE_CONTROLS}:
        raise ValueError('scheduler checkpoint scope/roots/controls differ')
    if not set(checkpoint['root_assumptions']) <= load(root, 'check-memory-trust.py').FRAMEWORK_ALLOWED:
        raise ValueError('unexpected scheduler-root assumptions')
    for rel in [scheduler.TABLE, scheduler.CODE, scheduler.MODEL, scheduler.EVAL, scheduler.EXEC]:
        if checks['scheduler:positive:' + Path(rel).stem]['exit_code'] != 0:
            raise ValueError('scheduler checkpoint positive compilation failed')
    if any(checks[k]['exit_code'] != 0 for k in ['scheduler:positive:contract', 'scheduler:coqchk']):
        raise ValueError('scheduler checkpoint probe/coqchk failed')
    if (checks['scheduler:wrong_table:V293ReadyBitmap']['exit_code'] != 1
            or checks['scheduler:wrong_table:V293ReadyTable']['exit_code'] != 0
            or checks['scheduler:wrong_shift:V293ReadyBitmap']['exit_code'] != 0
            or checks['scheduler:wrong_shift:V293OSSchedNewEval']['exit_code'] != 1):
        raise ValueError('scheduler designated table/shift rejection missing')
    for label in scheduler.CONTROLS:
        if (checks['scheduler:' + label + ':actual']['exit_code'] != 0
                or checks['scheduler:' + label + ':rejected']['exit_code'] != 1):
            raise ValueError('scheduler designated concrete semantic control missing')
    return report['functions']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--record', action='store_true', help='create evidence once; never overwrite')
    args = parser.parse_args()
    try:
        report = inspect()
        validate_record(ROOT, report)
        if args.record:
            with (ROOT / REPORT).open('x') as stream:
                json.dump(report, stream, ensure_ascii=False, indent=2)
                stream.write('\n')
        print('SOURCE FUNCTION CHECK: PASS (OSVersion, through one-function component_linked)')
        print('root assumptions:', report['root_assumptions'])
        print('GOOD_OS: OPEN; no full-target linkage claimed')
    except (OSError, ValueError, KeyError, TypeError, subprocess.TimeoutExpired) as error:
        parser.exit(1, f'SOURCE FUNCTION CHECK: FAIL: {error}\n')


if __name__ == '__main__':
    main()
