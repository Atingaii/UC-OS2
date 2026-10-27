#!/usr/bin/env python3
"""Restricted source seam for OS_SchedNew, not a verified C frontend."""
from __future__ import annotations
import json
import re
from pathlib import Path

CODE = 'certiucos/v293/code/V293OSSchedNew.v'
TABLE = 'certiucos/v293/code/V293ReadyTable.v'
MODEL = 'certiucos/v293/model/V293ReadyBitmap.v'
EVAL = 'certiucos/v293/proofs/V293OSSchedNewEval.v'
EXEC = 'certiucos/v293/proofs/V293OSSchedNewExec.v'
HOARE = 'certiucos/v293/proofs/V293OSSchedNewHoare.v'
WITNESS = 'certiucos/v293/proofs/V293OSSchedNewWitness.v'
FILES = [TABLE, CODE, MODEL, EVAL, EXEC, HOARE, WITNESS]
SCOPE = 'SOURCE_BOUND_BODY_HOARE_NOT_INTERNAL_COMPONENT_OR_GOOD_OS'
ROOTS = ['V293_ready_table_checked', 'V293_ready_selection', 'V293_ready_selection_range',
         'V293_OSSchedNew_row_eval', 'V293_shift_add_narrow', 'V293_OSSchedNew_priority_eval', 'V293_OSSchedNew_updates_execution',
         'V293_OSSchedNew_updates_frame', 'V293_OSSchedNew_updates_result',
         'V293_OSSchedNew_precondition_witness', 'V293_sched_inputs_load',
         'V293_OSSchedNew_row_hoare', 'V293_OSSchedNew_priority_hoare',
         'V293_OSSchedNew_body_hoare', 'V293_OSSchedNew_spatial_precondition_witness']


def canonical(node):
    typ = node.get('type', {})
    ref = node.get('referencedDecl', {})
    if ref and ref.get('type') != typ:
        raise ValueError('reference type disagrees with declaration')
    return (node.get('kind'), typ.get('qualType'), typ.get('desugaredQualType'),
            node.get('valueCategory'), node.get('castKind'), node.get('opcode'),
            node.get('name', ref.get('name')), ref.get('kind'), node.get('value'),
            node.get('storageClass'), bool(node.get('variadic')), bool(node.get('inline')),
            tuple(canonical(c) for c in node.get('inner', [])))


def n(kind, qual=None, desugared=None, category=None, cast=None, opcode=None,
      name=None, ref=None, value=None, storage=None, inner=()):
    return (kind, qual, desugared, category, cast, opcode, name, ref, value, storage,
            False, False, tuple(inner))


def ref(name, qual, desugared=None):
    return n('DeclRefExpr', qual, desugared, 'lvalue', name=name, ref='VarDecl')


def cast(kind, qual, child, desugared=None, explicit=False):
    return n('CStyleCastExpr' if explicit else 'ImplicitCastExpr', qual, desugared,
             'prvalue', cast=kind, inner=[child])


def rvalue(child, qual, desugared='unsigned char'):
    return cast('LValueToRValue', qual, child, desugared)


def table_read(index):
    decay = cast('ArrayToPointerDecay', 'const INT8U *', ref('OSUnMapTbl', 'const INT8U[256]'))
    elem = n('ArraySubscriptExpr', 'const INT8U', 'const unsigned char', 'lvalue', inner=[decay, index])
    return rvalue(elem, 'INT8U')


def expected(shift):
    y = ref('y', 'INT8U', 'unsigned char')
    yread = rvalue(y, 'INT8U')
    row_decay = cast('ArrayToPointerDecay', 'OS_PRIO *', ref('OSRdyTbl', 'OS_PRIO[2]'))
    row = rvalue(n('ArraySubscriptExpr', 'OS_PRIO', 'unsigned char', 'lvalue',
                   inner=[row_decay, yread]), 'OS_PRIO')
    left = n('BinaryOperator', 'int', category='prvalue', opcode='<<', inner=[
        cast('IntegralCast', 'int', yread),
        n('IntegerLiteral', 'unsigned int', category='prvalue', value=str(shift))])
    plus = n('BinaryOperator', 'int', category='prvalue', opcode='+', inner=[
        n('ParenExpr', 'int', category='prvalue', inner=[left]),
        cast('IntegralCast', 'int', table_read(row))])
    rhs = cast('IntegralCast', 'INT8U', n('ParenExpr', 'int', category='prvalue', inner=[plus]),
               'unsigned char', explicit=True)
    assign = lambda l, r: n('BinaryOperator', 'INT8U', 'unsigned char', 'prvalue', opcode='=', inner=[l, r])
    body = n('CompoundStmt', inner=[
        n('DeclStmt', inner=[n('VarDecl', 'INT8U', 'unsigned char', name='y')]),
        assign(y, table_read(rvalue(ref('OSRdyGrp', 'OS_PRIO', 'unsigned char'), 'OS_PRIO'))),
        assign(ref('OSPrioHighRdy', 'INT8U', 'unsigned char'), rhs)])
    return n('FunctionDecl', 'void (void)', name='OS_SchedNew', storage='static', inner=[body])


def decode(node):
    literals = []
    def visit(x):
        if x.get('kind') == 'IntegerLiteral':
            literals.append(x.get('value'))
        for child in x.get('inner', []):
            visit(child)
    visit(node)
    if len(literals) != 1 or not str(literals[0]).isdigit() or not 0 <= int(literals[0]) < 32:
        raise ValueError('unsupported scheduler shift literal')
    shift = int(literals[0])
    if canonical(node) != expected(shift):
        raise ValueError('unsupported scheduler AST, signature, type or conversion')
    return shift


def extract_table(ast):
    candidates = [n for n in ast['inner'] if n.get('kind') == 'VarDecl'
                  and n.get('name') == 'OSUnMapTbl'
                  and any(c.get('kind') == 'InitListExpr' for c in n.get('inner', []))]
    if len(candidates) != 1 or candidates[0]['type']['qualType'] != 'const INT8U[256]':
        raise ValueError('require unique actual const 256-byte lookup-table definition')
    children = candidates[0].get('inner', [])
    if len(children) != 1 or children[0].get('kind') != 'InitListExpr':
        raise ValueError('unsupported initializer or attributes')
    entries = children[0].get('inner', [])
    if len(entries) != 256:
        raise ValueError('require exactly 256 initializer entries')
    values = []
    for entry in entries:
        inner = entry.get('inner', [])
        if (entry.get('kind') != 'ImplicitCastExpr' or entry.get('castKind') != 'IntegralCast'
                or entry.get('type', {}).get('desugaredQualType') != 'unsigned char'
                or len(inner) != 1):
            raise ValueError('unsupported table entry conversion')
        literal = inner[0]
        value = literal.get('value', '')
        if (literal.get('kind') != 'IntegerLiteral' or literal.get('inner')
                or literal.get('type', {}).get('qualType') != 'unsigned int'
                or not value.isdigit() or not 0 <= int(value) < 256):
            raise ValueError('unsupported table entry literal')
        values.append(int(value))
    return values


def emit_table(values):
    if len(values) != 256 or any(type(v) is not int or not 0 <= v < 256 for v in values):
        raise ValueError('require 256 byte values')
    return '''(* Actual configured OSUnMapTbl initializer; checked by the scheduler gate.
   This data is not a replacement mathematical decoder. *)
Require Import Coq.Lists.List.
Import ListNotations.

Definition V293_ready_table : list nat :=
  [
''' + ';\n'.join('    ' + '; '.join(map(str, values[i:i+16])) for i in range(0, 256, 16)) + '''
  ].

Definition V293_ready_lookup (n : nat) : nat := nth n V293_ready_table 0.
'''


def emit_code(shift):
    return '''(* Checked translation of the configured static OS_SchedNew.
   Array decay and lvalue reads use CoqImp's native array/evar semantics.
   The promoted 32-bit operations and final byte narrowing remain explicit.
   Identifiers are linker parameters, not a completed global symbol table. *)
Require Import CertiOS.framework.model.memory CertiOS.framework.model.language.

Definition V293_OSSchedNew_row_expr (unmap group : var) : expr :=
  earrayelem (evar unmap) (evar group).

Definition V293_OSSchedNew_priority_expr (unmap rows y : var) : expr :=
  ecast
    (ebinop oplus
      (ebinop olshift (ecast (evar y) Tint32) (econst32 (Int.repr %d)))
      (ecast (earrayelem (evar unmap) (earrayelem (evar rows) (evar y))) Tint32))
    Tint8.

Definition V293_OSSchedNew_updates (unmap group rows high y : var) : stmts :=
  sseq (sassign (evar y) (V293_OSSchedNew_row_expr unmap group))
       (sassign (evar high) (V293_OSSchedNew_priority_expr unmap rows y)).

(* A C void function falling through its closing brace returns to its caller. *)
Definition V293_OSSchedNew_body (unmap group rows high y : var) : stmts :=
  sseq (V293_OSSchedNew_updates unmap group rows high y) sret.

Definition V293_OSSchedNew_function (unmap group rows high y : var) : function :=
  (Tvoid, dnil, dcons y Tint8 dnil, V293_OSSchedNew_body unmap group rows high y).
''' % shift


def check_source(root, work, loader):
    """Caller first replays the frozen program. Check both preprocessor ASTs."""
    u = loader(root, 'inventory-v293-source.py')
    freeze = loader(root, 'freeze-v293-source.py')
    includes = [a for p in [u.PORT, freeze.SOURCE, freeze.SOURCE / 'Source'] for a in ['-I', str(p)]]
    unit = str(freeze.SOURCE / 'Source/ucos_ii.c')
    decoded = []
    nodes = []
    for compiler, flags in [('clang', u.CLANG_FLAGS), ('gcc', u.GCC_FLAGS)]:
        data = u.run(work, [compiler, *flags, *includes, '-E', unit])
        (work / 'kernel.i').write_bytes(data)
        ast = json.loads(u.run(work, ['clang', *u.CLANG_FLAGS, '-x', 'c', '-fsyntax-only',
                                     '-Xclang', '-ast-dump=json', 'kernel.i']))
        node, = [n for n in u.definitions(ast) if n['name'] == 'OS_SchedNew']
        # Bind variable uses to the actual declaration identities, not just names.
        declared = {n['id']: n for n in ast['inner'] if n.get('kind') == 'VarDecl'}
        declared.update({node['inner'][0]['inner'][0]['inner'][0]['id']:
                         node['inner'][0]['inner'][0]['inner'][0]})
        def refs(x):
            if x.get('kind') == 'DeclRefExpr':
                r = x['referencedDecl']; d = declared.get(r['id'])
                if d is None or any(d.get(k) != r.get(k) for k in ['kind', 'name', 'type']):
                    raise ValueError('scheduler reference is not the actual declaration')
            for child in x.get('inner', []):
                refs(child)
        refs(node)
        decoded.append((decode(node), extract_table(ast)))
        nodes.append(node)
    if decoded[0] != decoded[1]:
        raise ValueError('scheduler GCC/Clang preprocessor disagreement')
    shift, table = decoded[0]
    for rel, generated in [(CODE, emit_code(shift)), (TABLE, emit_table(table))]:
        if (root / rel).read_text() != generated:
            raise ValueError('scheduler Coq emission differs from actual configured AST: ' + rel)
    return {'shift': shift, 'lookup_entries': len(table),
            'scope': SCOPE,
            'coverage_credit': False, 'roots': ROOTS}, nodes[0], table

# Kept independent of exported theorem declarations; inline the byte-level
# membership and group conditions so a permissive replacement is not enough.
PROBE = '''Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Local Open Scope nat_scope.
Definition checked_selection : forall lo hi group,
  lo < 256 -> hi < 256 ->
  group = (if lo =? 0 then 0 else 1) + (if hi =? 0 then 0 else 2) ->
  (exists p, (p < 8 /\\ Nat.testbit lo p = true) \/
    (8 <= p /\\ p < 13 /\\ Nat.testbit hi (p - 8) = true)) ->
  V293_ready_lookup group < 2 /\\
  ((V293_ready_select lo hi group < 8 /\\ Nat.testbit lo (V293_ready_select lo hi group) = true) \/
   (8 <= V293_ready_select lo hi group /\\ V293_ready_select lo hi group < 13 /\\
    Nat.testbit hi (V293_ready_select lo hi group - 8) = true)) /\\
  (forall p, ((p < 8 /\\ Nat.testbit lo p = true) \/
    (8 <= p /\\ p < 13 /\\ Nat.testbit hi (p - 8) = true)) -> V293_ready_select lo hi group <= p)
  := V293_ready_selection.

Definition checked_priority_read : forall ge le M unmap group rows y bt bg br byblock lo hi g,
  V293_sched_read_env ge le unmap group rows bt bg br ->
  V293_sched_read_memory M bt bg br lo hi g ->
  get le y = Some (byblock, Tint8) ->
  load Tint8 M (byblock, 0%Z) = Some (V293_byteval (V293_ready_lookup g)) ->
  lo < 256 -> hi < 256 -> g = V293_ready_group lo hi ->
  (exists p, V293_bitmap_ready lo hi p) ->
  evalval (V293_OSSchedNew_priority_expr unmap rows y) (ge, le, M) =
    Some (V293_byteval (V293_ready_select lo hi g)) /\\
  evaltype (V293_OSSchedNew_priority_expr unmap rows y) (ge, le, M) = Some Tint8
  := V293_OSSchedNew_priority_eval.

Definition checked_updates : forall P ks ge le M unmap group rows high y
    bt bg br bh byblock lo hi g oldy oldhigh,
  V293_sched_read_env ge le unmap group rows bt bg br ->
  V293_sched_read_memory M bt bg br lo hi g ->
  get le y = Some (byblock, Tint8) ->
  get le high = None -> get ge high = Some (bh, Tint8) ->
  get M (byblock, 0%Z) = Some (true, oldy) ->
  get M (bh, 0%Z) = Some (true, oldhigh) ->
  byblock <> bt -> byblock <> bg -> byblock <> br -> byblock <> bh ->
  lo < 256 -> hi < 256 -> g = V293_ready_group lo hi ->
  (exists p, V293_bitmap_ready lo hi p) ->
  cstepstar P
    (curs (V293_OSSchedNew_updates unmap group rows high y), (kenil, ks)) (ge, le, M)
    (curs (sskip None), (kenil, ks))
    (ge, le, V293_write_byte (V293_write_byte M byblock (V293_ready_lookup g))
       bh (V293_ready_select lo hi g)) := V293_OSSchedNew_updates_execution.

Definition checked_frame : forall M byblock bh lo hi g a,
  a <> (byblock, 0%Z) -> a <> (bh, 0%Z) ->
  get (V293_write_byte (V293_write_byte M byblock (V293_ready_lookup g))
    bh (V293_ready_select lo hi g)) a = get M a
  := V293_OSSchedNew_updates_frame.

Definition checked_nonvacuity : exists ge le M,
    V293_sched_read_env ge le 100%Z 101%Z 102%Z 1%positive 2%positive 3%positive /\\
    V293_sched_read_memory M 1%positive 2%positive 3%positive 0 16 2 /\\
    get le 104%Z = Some (5%positive, Tint8) /\\
    get le 103%Z = None /\\ get ge 103%Z = Some (4%positive, Tint8) /\\
    get M (5%positive, 0%Z) = Some (true, Undef) /\\
    get M (4%positive, 0%Z) = Some (true, Undef) /\\
    2 = V293_ready_group 0 16 /\\
    (exists p, V293_bitmap_ready 0 16 p) := V293_OSSchedNew_precondition_witness.
'''

# Deliberately duplicate the expected resource/spec shape. In particular the
# writable flags, nonempty input, absence of an expression oracle, and absence
# of a False premise must not follow a weakened exported definition.
PROBE += r'''
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Fixpoint checked_bytes (b : block) (i : Z) (values : list nat) : asrt :=
  match values with
  | nil => Aemp
  | cons v tail => Amapsto (b, i) Tint8 false (V293_byteval v) ** checked_bytes b (i + 1)%Z tail
  end.
Definition checked_bindings unmap group rows high y bt bg br bh byblock : asrt :=
  Agvarenv unmap (Tarray Tint8 256) (bt, 0%Z) //\\
  Agvarenv group Tint8 (bg, 0%Z) //\\
  Agvarenv rows (Tarray Tint8 2) (br, 0%Z) //\\
  Agvarenv high Tint8 (bh, 0%Z) //\\
  Alvarenv y Tint8 (byblock, 0%Z) //\\
  A_notin_lenv unmap //\\ A_notin_lenv group //\\ A_notin_lenv rows //\\ A_notin_lenv high.
Definition checked_common unmap group rows high y bt bg br bh byblock lo hi g li tid frame :=
  (checked_bindings unmap group rows high y bt bg br bh byblock **
    (checked_bytes bt 0 V293_ready_table ** checked_bytes br 0 (cons lo (cons hi nil)) **
      Amapsto (bg, 0%Z) Tint8 false (V293_byteval g))) ** (CurLINV li tid ** frame).
Definition checked_state common byblock bh yv hv :=
  (common ** PV (byblock, Int.zero) @ Tint8 |-> yv) ** PV (bh, Int.zero) @ Tint8 |-> hv.
Definition checked_body_hoare : forall Spec sd li I tid aop frame
    unmap group rows high y bt bg br bh byblock lo hi g yold hold,
  lo < 256 -> hi < 256 -> g = V293_ready_group lo hi ->
  (exists p, V293_bitmap_ready lo hi p) ->
  let common := checked_common unmap group rows high y bt bg br bh byblock lo hi g li tid frame in
  InfRules Spec sd li I
    (fun result => <||aop||> **
      ([|result = None /\ V293_bitmap_ready lo hi (V293_ready_select lo hi g) /\
        (forall p, V293_bitmap_ready lo hi p -> V293_ready_select lo hi g <= p)|] **
        checked_state common byblock bh (V293_byteval (V293_ready_lookup g))
          (V293_byteval (V293_ready_select lo hi g)))) Afalse
    (<||aop||> ** checked_state common byblock bh yold hold)
    (sseq
      (sseq (sassign (evar y) (earrayelem (evar unmap) (evar group)))
        (sassign (evar high)
          (ecast (ebinop oplus
            (ebinop olshift (ecast (evar y) Tint32) (econst32 (Int.repr 3)))
            (ecast (earrayelem (evar unmap) (earrayelem (evar rows) (evar y))) Tint32)) Tint8))) sret)
    Afalse tid := V293_OSSchedNew_body_hoare.
Definition checked_spatial_witness : exists s,
  s |= <||spec_done None||> **
    checked_state
      (checked_common 100%Z 101%Z 102%Z 103%Z 104%Z
        1%positive 2%positive 3%positive 4%positive 5%positive
        0 16 2 (fun _ _ => Aemp) (7%positive, Int.zero) Aemp)
      5%positive 4%positive (V293_byteval 0) (V293_byteval 0)
  := V293_OSSchedNew_spatial_precondition_witness.
'''

CONTROLS = {
    'group_coherence_removed_only': (
        'Definition actual_result : V293_ready_select 2 16 2 = 12 := eq_refl.\n',
        'Definition should_select_minimum : V293_ready_select 2 16 2 = 1 := eq_refl.\n',
        'REJECTED_AT_should_select_minimum'),
    'nonempty_removed_only': (
        'Definition actual_result : V293_ready_select 0 0 0 = 0 := eq_refl.\n',
        'Definition should_select_ready : Nat.testbit 0 (V293_ready_select 0 0 0) = true := eq_refl.\n',
        'REJECTED_AT_should_select_ready'),
    'writable_permission_removed_only': (
        'Definition readonly_M : mem := sig (5%positive, 0%Z) (false, Undef).\n'
        'Lemma actual_store : store Tint8 readonly_M (5%positive, 0%Z) (V293_byteval 1) = None.\n'
        'Proof. unfold store, V293_byteval, readonly_M. cbn [encode_val encode_int]. '
        'unfold inj_bytes. cbn [List.map storebytes]. unfold addr, offset. '
        'rewrite map_get_sig. reflexivity. Qed.\n',
        'Definition should_store : store Tint8 readonly_M (5%positive, 0%Z) (V293_byteval 1) = '
        'Some (V293_write_byte readonly_M 5%positive 1) := eq_refl.\n',
        'REJECTED_AT_should_store'),
}
BODY_CONTROLS = {
    'group_resource_removed_only': 'REJECTED_AT_V293_sched_inputs_load',
    'local_write_permission_removed_only': 'REJECTED_AT_V293_OSSchedNew_row_hoare',
    'output_post_restores_old_value_only': 'REJECTED_AT_V293_OSSchedNew_priority_hoare',
    'body_false_premise_added_only': 'MUTANT_COMPILES_REJECTED_AT_checked_body_hoare',
}
NEGATIVE_CONTROLS = {
    **BODY_CONTROLS,
    'table_entry_16_changed_only': 'REJECTED_AT_V293_ready_table_checked',
    'shift_changed_only': 'REJECTED_AT_V293_OSSchedNew_priority_eval',
    **{k: v[2] for k, v in CONTROLS.items()},
}


def check_proofs(root, work, build, coqbin, run, loader, table):
    def compile_tree(label, replacements=None, probe=None):
        dest = work / ('scheduler_' + label)
        flags = ['-R', str(build / 'framework'), 'CertiOS.framework',
                 '-R', str(build / 'tactics'), 'CertiOS.tactics',
                 '-R', str(dest / 'certiucos'), 'CertiOS.certiucos',
                 '-R', str(dest / 'checks'), 'SchedulerCheck']
        (dest / 'checks').mkdir(parents=True)
        for rel in FILES:
            target = dest / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text((replacements or {}).get(rel, (root / rel).read_text()))
            row = run(f'scheduler:{label}:{Path(rel).stem}', [coqbin + 'coqc', '-q', *flags, str(target)], dest)
            if row['exit_code']:
                return row, flags, dest
        if probe is not None:
            path = dest / 'checks/Contract.v'; path.write_text(probe)
            row = run(f'scheduler:{label}:contract', [coqbin + 'coqc', '-q', *flags, str(path)], dest)
        return row, flags, dest

    def failed_at(row, source, declaration):
        match = re.search(r'line (\d+), characters', row['stderr'])
        start = source.index(declaration)
        lo = source[:start].count('\n') + 1
        end = source.find('Qed.', start)
        if declaration.startswith('Definition '):
            end = source.find('\nDefinition ', start + len(declaration))
        hi = source[:end].count('\n') + 1 if end >= 0 else source.count('\n') + 1
        if row['exit_code'] != 1 or not match or not lo <= int(match[1]) <= hi:
            raise ValueError('scheduler control missed designated obligation: ' + str(row))

    row, flags, dest = compile_tree('positive', probe=PROBE + '\n' +
        '\n'.join('Print Assumptions ' + r + '.' for r in ROOTS))
    if row['exit_code']:
        raise ValueError('scheduler proof/probe failed: ' + str(row))
    out = row['stdout']; assumptions = set()
    trust = loader(root, 'check-memory-trust.py')
    for part in out.split('Axioms:')[1:]:
        assumptions |= set(trust.check_assumptions(part.split('Closed under the global context')[0],
                                                   trust.FRAMEWORK_ALLOWED))
    if out.count('Axioms:') + out.count('Closed under the global context') != len(ROOTS):
        raise ValueError('missing scheduler root assumption output')
    row = run('scheduler:coqchk', [coqbin + 'coqchk', '-silent', *flags,
        'CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness', 'SchedulerCheck.Contract'], dest)
    if row['exit_code']:
        raise ValueError('scheduler coqchk failed: ' + str(row))

    wrong_table = list(table); wrong_table[16] = 3
    row, _, _ = compile_tree('wrong_table', {TABLE: emit_table(wrong_table)})
    failed_at(row, (root / MODEL).read_text(), 'Lemma V293_ready_table_checked')
    # Let the restricted emitter accept exactly this changed shift; keep the
    # entire table, independent spec, generic arithmetic lemma and proof fixed.
    row, _, _ = compile_tree('wrong_shift', {CODE: emit_code(2)})
    failed_at(row, (root / EVAL).read_text(), 'Theorem V293_OSSchedNew_priority_eval')
    # Reuse the positive object tree. These controls are semantic inputs, not
    # stale-source hash tests. Each actual result is compiled before demanding
    # the independently wrong property in a second invocation.
    for label, (actual, wrong, _) in CONTROLS.items():
        path = dest / 'checks' / (label + '.v')
        prefix = PROBE + '\n' + actual
        path.write_text(prefix)
        row = run(f'scheduler:{label}:actual', [coqbin + 'coqc', '-q', *flags, str(path)], dest)
        if row['exit_code']:
            raise ValueError('scheduler control actual result did not compile: ' + str(row))
        path.write_text(prefix + wrong)
        row = run(f'scheduler:{label}:rejected', [coqbin + 'coqc', '-q', *flags, str(path)], dest)
        # The deliberately wrong statement is a single-line declaration.
        match = re.search(r'line (\d+), characters', row['stderr'])
        if row['exit_code'] != 1 or not match or int(match[1]) != prefix.count('\n') + 1:
            raise ValueError('scheduler concrete semantic control did not reject at its expected statement')
    # Prospective single-factor mutations. Keep source/table, all other
    # contracts, proof bodies, and the independent expected type unchanged.
    source = (root / HOARE).read_text()
    def replace_once(text, old, new):
        if text.count(old) != 1:
            raise ValueError('body mutation anchor is not unique')
        return text.replace(old, new, 1)
    mutations = {
        'group_resource_removed_only': (
            replace_once(source, '  Amapsto (bg, 0%Z) Tint8 false (V293_byteval g).', '  Aemp.'),
            'Lemma V293_sched_inputs_load'),
        'local_write_permission_removed_only': (
            replace_once(source, '(common ** PV (byblock, Int.zero) @ Tint8 |-> yv)',
                         '(common ** PV (byblock, Int.zero) @ Tint8 |-r-> yv)'),
            'Theorem V293_OSSchedNew_row_hoare'),
    }
    # Change only the second assignment's post, not its input or implementation.
    start = source.index('Theorem V293_OSSchedNew_priority_hoare')
    end = source.index('Proof.', start)
    mutations['output_post_restores_old_value_only'] = (
        source[:start] + replace_once(source[start:end],
            '(V293_byteval (V293_ready_select lo hi g))) tid.', 'hold) tid.') + source[end:],
        'Theorem V293_OSSchedNew_priority_hoare')
    for label, (changed, declaration) in mutations.items():
        row, _, _ = compile_tree(label, {HOARE: changed})
        failed_at(row, changed, declaration)
    # A stronger, vacuous theorem is easy to compile. Only the independent
    # expected interface, not merely compilation or a source hash, rejects it.
    start = source.index('Theorem V293_OSSchedNew_body_hoare')
    changed = source[:start] + source[start:].replace(
        '  lo < 256 -> hi < 256 ->', '  False -> lo < 256 -> hi < 256 ->', 1).replace(
        'hold Hlo Hhi Hgroup Hready common.', 'hold Hfalse Hlo Hhi Hgroup Hready common.', 1)
    label = 'body_false_premise_added_only'
    row, _, _ = compile_tree(label, {HOARE: changed})
    if row['exit_code']:
        raise ValueError('vacuous body mutant must compile before type rejection')
    row, _, _ = compile_tree(label + '_probe', {HOARE: changed}, probe=PROBE)
    failed_at(row, PROBE, 'Definition checked_body_hoare')
    return {'root_assumptions': sorted(assumptions), 'negative_controls': NEGATIVE_CONTROLS}
