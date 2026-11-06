#!/usr/bin/env python3
"""Restricted configured time-API AST seam; ADR0005, not a verified frontend.

Only copy-source selection varies. Everything else, including declaration
order, volatile qualifications and critical-token identity, is checked.
"""
from __future__ import annotations

CODE = 'certiucos/v293/code/V293TimeSource.v'
NAMES = ('OSTimeGet', 'OSTimeSet')


def canonical(node):
    # Unknown fields fail closed. Location, Clang identities and usage flags
    # do not affect this syntax; local reference identities are checked below.
    ignored = {'id', 'loc', 'range', 'previousDecl', 'isUsed', 'isReferenced',
               'mangledName', 'typeAliasDeclId'}
    fields = {'kind', 'name', 'type', 'valueCategory', 'castKind', 'opcode',
              'value', 'init', 'isPostfix', 'canOverflow', 'referencedDecl',
              'inner', 'qualType', 'desugaredQualType'}
    if set(node) - ignored - fields:
        raise ValueError('unsupported time AST fields: ' + str(sorted(set(node) - ignored - fields)))
    return {k: ([canonical(x) for x in v] if isinstance(v, list)
                else canonical(v) if isinstance(v, dict) else v)
            for k, v in node.items() if k not in ignored}


def typ(name):
    return {'qualType': name, **({'desugaredQualType': 'volatile unsigned int'
                                if name.startswith('volatile ') else 'unsigned int'}
                               if name in ('INT32U', 'OS_CPU_SR', 'volatile INT32U') else {})}


def n(kind, children=(), **kw):
    return {'kind': kind, **kw, **({'inner': list(children)} if children else {})}


def ref(name, getter):
    ty = typ('volatile INT32U' if name == 'OSTime' else
             'OS_CPU_SR' if name == 'cpu_sr' else 'INT32U')
    kind = 'ParmVarDecl' if name == 'ticks' and not getter else 'VarDecl'
    return n('DeclRefExpr', type=ty, valueCategory='lvalue',
             referencedDecl={'kind': kind, 'name': name, 'type': ty})


def read(name, getter):
    return n('ImplicitCastExpr', [ref(name, getter)], type=typ('INT32U'),
             valueCategory='prvalue', castKind='LValueToRValue')


def marker(name, getter):
    ft = typ('void (OS_CPU_SR *)')
    function = n('DeclRefExpr', type=ft, valueCategory='prvalue',
                 referencedDecl={'kind': 'FunctionDecl', 'name': name, 'type': ft})
    decay = n('ImplicitCastExpr', [function], type=typ('void (*)(OS_CPU_SR *)'),
              valueCategory='prvalue', castKind='FunctionToPointerDecay')
    address = n('UnaryOperator', [ref('cpu_sr', getter)], type=typ('OS_CPU_SR *'),
                valueCategory='prvalue', opcode='&', isPostfix=False, canOverflow=False)
    return n('CallExpr', [decay, address], type=typ('void'), valueCategory='prvalue')


def expected(name, source):
    getter = name == 'OSTimeGet'
    saved = n('DeclStmt', [n('VarDecl', [n('IntegerLiteral', type=typ('unsigned int'),
                                         valueCategory='prvalue', value='0')],
                             name='cpu_sr', type=typ('OS_CPU_SR'), init='c')])
    copy = n('BinaryOperator', [ref('ticks' if getter else 'OSTime', getter), read(source, getter)],
             type=typ('INT32U'), valueCategory='prvalue', opcode='=')
    statements = ([n('DeclStmt', [n('VarDecl', name='ticks', type=typ('INT32U'))])]
                  if getter else []) + [saved, marker('V293_EnterCritical', getter),
                                       copy, marker('V293_ExitCritical', getter)]
    if getter:
        result = n('ImplicitCastExpr', [n('ParenExpr', [ref('ticks', True)],
                                         type=typ('INT32U'), valueCategory='lvalue')],
                   type=typ('INT32U'), valueCategory='prvalue', castKind='LValueToRValue')
        statements.append(n('ReturnStmt', [result]))
    params = [] if getter else [n('ParmVarDecl', name='ticks', type=typ('INT32U'))]
    return n('FunctionDecl', params + [n('CompoundStmt', statements)], name=name,
             type=typ('INT32U (void)' if getter else 'void (INT32U)'))


def decode(node):
    name = node.get('name')
    if name not in NAMES:
        raise ValueError('unsupported time function')
    locals_ = {}

    def visit(x):
        if x.get('kind') in ('VarDecl', 'ParmVarDecl'):
            key = x.get('name')
            if key in locals_ or not x.get('id'):
                raise ValueError('duplicate or unidentified local declaration')
            locals_[key] = x['id']
        for c in x.get('inner', []):
            visit(c)

    visit(node)

    def references(x):
        declaration = x.get('referencedDecl', {})
        key = declaration.get('name')
        if key in locals_ and declaration.get('id') != locals_[key]:
            raise ValueError('local reference identity mismatch')
        for c in x.get('inner', []):
            references(c)

    references(node)
    actual = canonical(node)
    for source in ('OSTime', 'ticks'):
        if actual == expected(name, source):
            return source
    raise ValueError('unsupported time AST, type, declaration, statement or marker')


def emit(sources):
    if set(sources) != set(NAMES) or any(s not in ('OSTime', 'ticks') for s in sources.values()):
        raise ValueError('require both time functions and supported copy sources')
    bodies = []
    for name, getter in [('OSTimeGet', True), ('OSTimeSet', False)]:
        source = 'now' if sources[name] == 'OSTime' else 'ticks'
        dst = 'ticks' if getter else 'now'
        result = '(srete (evar ticks))' if getter else 'sret'
        bodies.append(f'''Definition V293_source_{name}_body (now ticks saved : var) : stmts :=
  sseq (sassign (evar saved) (econst32 Int.zero))
    (sseq (sseq (sprim encrit)
      (sseq (sassign (evar {dst}) (evar {source})) (sprim excrit)))
      {result}).
Definition V293_source_{name}_function (now ticks saved : var) : function :=
  ({'Tint32,dnil,dcons ticks Tint32 (dcons saved Tint32 dnil)' if getter else 'Tvoid,dcons ticks Tint32 dnil,dcons saved Tint32 dnil'},
    V293_source_{name}_body now ticks saved).
''')
    return '''(* Generated by scripts/v293-time-source.py from configured Clang AST.
   Critical markers use ADR0005; this is not physical port execution. *)
Require Import CertiOS.framework.model.memory.
Require Import CertiOS.framework.model.language.

''' + '\n'.join(bodies)
