#!/usr/bin/env python3
"""Source-bound internal call and pointer read, not the OS_Sched body Hoare."""
from pathlib import Path
import json
import re
import shutil

CODE = 'certiucos/v293/code/V293OSSchedDispatch.v'
TASKS = 'certiucos/v293/model/V293SchedulerTasks.v'
CALL = 'certiucos/v293/proofs/V293OSSchedCall.v'
TARGET = 'certiucos/v293/proofs/V293OSSchedTarget.v'
WITNESS = 'certiucos/v293/proofs/V293OSSchedTargetWitness.v'
FILES = [CODE, TASKS, CALL, TARGET, WITNESS]
ROOTS = ['V293_OSSchedNew_call_rule', 'V293_ready_selection_task', 'V293_scheduler_good',
         'V293_OSSched_target_task', 'V293_OSSched_target_precondition_witness']
SCOPE = 'SOURCE_BOUND_CALL_RULE_AND_TARGET_READ_NOT_COMPOSED_PREFIX_OR_OS_SCHED_HOARE'
CONTROLS = {
    'bitmap_membership_removed_only': 'REJECTED_AT_V293_ready_selection_task',
    'table_entry_identity_removed_only': 'REJECTED_AT_V293_ready_selection_task',
    'pointer_resource_stride_changed_only': 'REJECTED_AT_V293_read_pointers_load',
    'call_false_premise_added_only': 'MUTANT_COMPILES_REJECTED_AT_checked_call',
    'target_false_premise_added_only': 'MUTANT_COMPILES_REJECTED_AT_checked_target',
}


def walk(node):
    yield node
    for child in node.get('inner', []):
        yield from walk(child)


def expected(s):
    """Independently written exact configured OS_Sched shape, including guards."""
    n, ref, cast = s.n, s.ref, s.cast
    byte = lambda name: s.rvalue(ref(name, 'INT8U', 'unsigned char'), 'INT8U')
    zero = n('IntegerLiteral', 'unsigned int', category='prvalue', value='0')
    cpu = ref('cpu_sr', 'OS_CPU_SR', 'unsigned int')
    def call(name, critical=False):
        signature = 'void (OS_CPU_SR *)' if critical else 'void (void)'
        pointer = 'void (*)(OS_CPU_SR *)' if critical else 'void (*)(void)'
        fn = n('DeclRefExpr', signature, category='prvalue', name=name, ref='FunctionDecl')
        args = [n('UnaryOperator', 'OS_CPU_SR *', category='prvalue', opcode='&', inner=[cpu])] if critical else []
        return n('CallExpr', 'void', category='prvalue', inner=[cast('FunctionToPointerDecay', pointer, fn), *args])
    def guard(name, body):
        cond = n('BinaryOperator', 'int', category='prvalue', opcode='==',
                 inner=[cast('IntegralCast', 'unsigned int', byte(name)), zero])
        return n('IfStmt', inner=[cond, n('CompoundStmt', inner=body)])
    target = n('BinaryOperator', 'OS_TCB *', category='prvalue', opcode='=', inner=[
        ref('OSTCBHighRdy', 'OS_TCB *'),
        cast('LValueToRValue', 'OS_TCB *', n('ArraySubscriptExpr', 'OS_TCB *', category='lvalue', inner=[
            cast('ArrayToPointerDecay', 'OS_TCB **', ref('OSTCBPrioTbl', 'OS_TCB *[13]')), byte('OSPrioHighRdy')]))])
    different = n('BinaryOperator', 'int', category='prvalue', opcode='!=', inner=[
        cast('IntegralCast', 'int', byte('OSPrioHighRdy')), cast('IntegralCast', 'int', byte('OSPrioCur'))])
    counter = n('UnaryOperator', 'INT32U', 'unsigned int', 'prvalue', opcode='++',
                inner=[ref('OSCtxSwCtr', 'INT32U', 'unsigned int')])
    switch = n('IfStmt', inner=[different, n('CompoundStmt', inner=[counter, call('OSCtxSw')])])
    return n('FunctionDecl', 'void (void)', name='OS_Sched', inner=[n('CompoundStmt', inner=[
        n('DeclStmt', inner=[n('VarDecl', 'OS_CPU_SR', 'unsigned int', name='cpu_sr', inner=[zero])]),
        call('V293_EnterCritical', True),
        guard('OSIntNesting', [guard('OSLockNesting', [call('OS_SchedNew'), target, switch])]),
        call('V293_ExitCritical', True)])])


def decode(node, scheduler):
    if scheduler.canonical(node) != expected(scheduler):
        raise ValueError('unsupported OS_Sched AST, guard, call, type or statement order')
    # The older canonical seam predates unary operators. Do not drop their
    # pre/post distinction or the initialized declaration's storage semantics.
    unary = [(x.get('opcode'), x.get('isPostfix')) for x in walk(node) if x['kind'] == 'UnaryOperator']
    locals_ = [(x.get('name'), x.get('init')) for x in walk(node) if x['kind'] == 'VarDecl']
    if unary != [('&', False), ('++', True), ('&', False)] or locals_ != [('cpu_sr', 'c')]:
        raise ValueError('unsupported OS_Sched unary or local initialization semantics')


def check_references(node, declarations):
    for x in walk(node):
        if x.get('kind') == 'DeclRefExpr':
            ref = x['referencedDecl']; decl = declarations.get(ref['id'])
            if decl is None or any(decl.get(k) != ref.get(k) for k in ['kind', 'name', 'type']):
                raise ValueError('caller reference is not the actual declaration')


def check_source(root, work, loader):
    scheduler = loader(root, 'v293-scheduler-source.py')
    u = loader(root, 'inventory-v293-source.py'); freeze = loader(root, 'freeze-v293-source.py')
    includes = [a for p in [u.PORT, freeze.SOURCE, freeze.SOURCE / 'Source'] for a in ['-I', str(p)]]
    unit = str(freeze.SOURCE / 'Source/ucos_ii.c')
    nodes = []
    for compiler, flags in [('clang', u.CLANG_FLAGS), ('gcc', u.GCC_FLAGS)]:
        (work / 'caller.i').write_bytes(u.run(work, [compiler, *flags, *includes, '-E', unit]))
        ast = json.loads(u.run(work, ['clang', *u.CLANG_FLAGS, '-x', 'c', '-fsyntax-only',
                                     '-Xclang', '-ast-dump=json', 'caller.i']))
        node, = [n for n in u.definitions(ast) if n['name'] == 'OS_Sched']
        decode(node, scheduler)
        declarations = {n['id']: n for n in ast['inner'] if n.get('kind') in {'VarDecl', 'FunctionDecl'}}
        declarations.update({n['id']: n for n in walk(node) if n.get('kind') == 'VarDecl'})
        check_references(node, declarations)
        nodes.append(node)
    if scheduler.canonical(nodes[0]) != scheduler.canonical(nodes[1]):
        raise ValueError('caller GCC/Clang preprocessor disagreement')
    if (root / CODE).read_text() != EMISSION:
        raise ValueError('caller prefix Coq emission differs from the checked two statements')
    inventory = json.loads((root / 'audit/repaired-source-inventory.json').read_text())
    return next(f for f in inventory['functions'] if f['name'] == 'OS_Sched')


EMISSION = "(* Only the first two statements of OS_Sched's unlocked branch.\n   This is not a translation of its critical-section wrapper or context switch.\n   The pointee type remains a linker parameter: no TCB field is dereferenced. *)\nRequire Import CertiOS.framework.model.memory CertiOS.framework.model.language.\n\nDefinition V293_OSSched_target_expr (table high : var) : expr :=\n  earrayelem (evar table) (evar high).\n\nDefinition V293_OSSched_target_update (table high target : var) : stmts :=\n  sassign (evar target) (V293_OSSched_target_expr table high).\n\nDefinition V293_OSSched_unlocked_prefix (sched_id table high target : var) : stmts :=\n  sseq (scall sched_id nil) (V293_OSSched_target_update table high target).\n"


PROBE = r'''
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Definition checked_bitmap_tasks lo hi (tasks : TcbMod.map) : Prop :=
  forall p, p < 13 -> (V293_bitmap_ready lo hi p <->
    exists t m, get tasks t = Some (Int.repr (Z.of_nat p), rdy, m)).
Definition checked_priority_table (entries : list val) (tasks : TcbMod.map) : Prop :=
  length entries = 13 /\ forall t priority status m,
  get tasks t = Some (priority, status, m) -> exists p,
  p < 13 /\ priority = Int.repr (Z.of_nat p) /\ nth p entries Vnull = Vptr t.
Definition checked_highest tasks t : Prop := exists priority m,
  get tasks t = Some (priority, rdy, m) /\
  forall t' priority' m', get tasks t' = Some (priority', rdy, m') ->
  (Int.unsigned priority <= Int.unsigned priority')%Z.
Definition checked_scheduler : ossched := fun O t => exists tasks,
  get O abstcblsid = Some (abstcblist tasks) /\ checked_highest tasks t.
Fixpoint checked_pointers (tp : type) (b : block) (offset : Z) (entries : list val) : asrt :=
  match entries with nil => Aemp | cons v tail =>
  Amapsto (b, offset) (Tptr tp) false v ** checked_pointers tp b (offset + 4)%Z tail end.
Definition checked_good_scheduler : GoodSched checked_scheduler := V293_scheduler_good.

Definition checked_call : forall Spec sd li I r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_sched_fpre unmap group rows high bt bg br bh li Hli,
     V293_sched_fpost unmap group rows high bt bg br bh li Hli, (Tvoid, nil)) ->
  InfRules Spec sd li I r ri
    (checked_pre unmap group rows high bt bg br bh lo hi li tid aop ** frame)
    (scall sched_id nil)
    (EX result : option val,
      checked_post unmap group rows high bt bg br bh lo hi li tid aop result ** frame) tid := V293_OSSchedNew_call_rule.

Definition checked_task_selection : forall lo hi entries tasks,
  lo < 256 -> hi < 256 ->
  (exists p, V293_bitmap_ready lo hi p) ->
  checked_bitmap_tasks lo hi tasks -> checked_priority_table entries tasks ->
  exists t m,
    get tasks t = Some (Int.repr (Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi))), rdy, m) /\
    nth (V293_ready_select lo hi (V293_ready_group lo hi)) entries Vnull = Vptr t /\
    checked_highest tasks t := V293_ready_selection_task.

Definition checked_target : forall s table high tp bp bh lo hi entries tasks frame,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  checked_bitmap_tasks lo hi tasks -> checked_priority_table entries tasks ->
  get (getlenv s) table = None -> get (getlenv s) high = None ->
  get (getgenv s) table = Some (bp, Tarray (Tptr tp) 13) ->
  get (getgenv s) high = Some (bh, Tint8) ->
  load Tint8 (getmem s) (bh, 0%Z) =
    Some (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) ->
  s |= (checked_pointers tp bp 0 entries ** Aabsdata abstcblsid (abstcblist tasks)) ** frame ->
  exists t m,
    get tasks t = Some (Int.repr (Z.of_nat (V293_ready_select lo hi (V293_ready_group lo hi))), rdy, m) /\
    evalval (V293_OSSched_target_expr table high) (getgenv s, getlenv s, getmem s) = Some (Vptr t) /\
    evaltype (V293_OSSched_target_expr table high) (getgenv s, getlenv s, getmem s) = Some (Tptr tp) /\
    checked_scheduler (getabst s) t := V293_OSSched_target_task.

Definition checked_target_witness : exists s entries tasks,
  checked_bitmap_tasks 0 16 tasks /\ checked_priority_table entries tasks /\
  get (getlenv s) 100%Z = None /\ get (getlenv s) 101%Z = None /\
  get (getgenv s) 100%Z = Some (8%positive, Tarray (Tptr Tvoid) 13) /\
  get (getgenv s) 101%Z = Some (9%positive, Tint8) /\
  load Tint8 (getmem s) (9%positive, 0%Z) = Some (V293_byteval 12) /\
  s |= (checked_pointers Tvoid 8%positive 0 entries ** Aabsdata abstcblsid (abstcblist tasks)) **
    Amapsto (9%positive, 0%Z) Tint8 false (V293_byteval 12) := V293_OSSched_target_precondition_witness.
'''


def replace_once(source, old, new):
    if source.count(old) != 1:
        raise ValueError('caller mutation anchor is not unique')
    return source.replace(old, new, 1)


def check(root, work, build, coqbin, run, loader, location):
    scheduler = loader(root, 'v293-scheduler-source.py')
    internal = loader(root, 'v293-scheduler-internal.py')
    probe = scheduler.PROBE + internal.PRELUDE + PROBE
    checks = {}
    def record(label, command, cwd):
        row = run('caller:' + label, command, cwd); checks[label] = row
        return row

    def compile_tree(label, replacements=None, assumptions=False):
        dest = work / ('caller_' + label)
        # Every copied object was built from source in this invocation's empty
        # build directory, never from the checkout or an earlier gate run.
        shutil.copytree(build / 'certiucos', dest / 'certiucos')
        (dest / 'checks').mkdir()
        flags = ['-R', str(build / 'framework'), 'CertiOS.framework',
                 '-R', str(build / 'tactics'), 'CertiOS.tactics',
                 '-R', str(dest / 'certiucos'), 'CertiOS.certiucos',
                 '-R', str(dest / 'checks'), 'CallerCheck']
        for rel in FILES:
            path = dest / rel
            for suffix in ['.vo', '.vos', '.vok', '.glob']:
                path.with_suffix(suffix).unlink(missing_ok=True)
            path.write_text((replacements or {}).get(rel, (root / rel).read_text()))
            row = record(label + ':' + Path(rel).stem, [coqbin + 'coqc', '-q', *flags, str(path)], dest)
            if row['exit_code']:
                return row, flags, dest
        path = dest / 'checks/Contract.v'
        path.write_text(probe + ('\n' + '\n'.join('Print Assumptions ' + r + '.' for r in ROOTS) if assumptions else ''))
        row = record(label + ':contract', [coqbin + 'coqc', '-q', *flags, str(path)], dest)
        return row, flags, dest

    row, flags, dest = compile_tree('positive', assumptions=True)
    if row['exit_code']:
        raise ValueError('caller proof/probe failed: ' + str(row))
    trust = loader(root, 'check-memory-trust.py'); assumptions = set()
    for part in row['stdout'].split('Axioms:')[1:]:
        assumptions |= set(trust.check_assumptions(part.split('Closed under the global context')[0], trust.FRAMEWORK_ALLOWED))
    if row['stdout'].count('Axioms:') + row['stdout'].count('Closed under the global context') != len(ROOTS):
        raise ValueError('missing caller root assumption output')
    row = record('coqchk', [coqbin + 'coqchk', '-silent', *flags,
        *['CertiOS.' + Path(f).with_suffix('').as_posix().replace('/', '.') for f in FILES],
        'CallerCheck.Contract'], dest)
    if row['exit_code']:
        raise ValueError('caller coqchk failed: ' + str(row))

    tasks = (root / TASKS).read_text(); target = (root / TARGET).read_text(); call = (root / CALL).read_text()
    mutations = {
        'bitmap_membership_removed_only': (TASKS, replace_once(tasks,
            'exists t m, get tasks t = Some (Int.repr (Z.of_nat p), rdy, m)).', 'True).'),
            'Theorem V293_ready_selection_task'),
        'table_entry_identity_removed_only': (TASKS, replace_once(tasks,
            'nth p entries Vnull = Vptr t.', 'True.'), 'Theorem V293_ready_selection_task'),
        'pointer_resource_stride_changed_only': (TARGET, replace_once(target,
            'V293_read_pointers tp b (offset + 4)%Z tail',
            'V293_read_pointers tp b (offset + 1)%Z tail'), 'Lemma V293_read_pointers_load'),
    }
    call_mutant = replace_once(call, '  lo < 256 -> hi < 256 -> GoodFrm frame ->',
                              '  False -> lo < 256 -> hi < 256 -> GoodFrm frame ->')
    call_mutant = replace_once(call_mutant, '    Hlo Hhi Hframe Hspec.', '    Hfalse Hlo Hhi Hframe Hspec.')
    mutations['call_false_premise_added_only'] = (CALL, call_mutant, 'Definition checked_call')
    target_mutant = replace_once(target, '  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->',
                                '  False -> lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->')
    target_mutant = replace_once(target_mutant, 'tasks frame Hlo Hhi Hnonempty', 'tasks frame Hfalse Hlo Hhi Hnonempty')
    mutations['target_false_premise_added_only'] = (TARGET, target_mutant, 'Definition checked_target')
    for label, (rel, mutant, declaration) in mutations.items():
        row, _, _ = compile_tree(label, {rel: mutant})
        is_probe = declaration.startswith('Definition checked_')
        failed_source = probe if is_probe else mutant
        start = failed_source.index(declaration)
        lo = failed_source[:start].count('\n') + 1
        end = failed_source.find('\nDefinition ', start + len(declaration)) if is_probe else failed_source.index('Qed.', start)
        hi = failed_source[:end].count('\n') + 1 if end >= 0 else failed_source.count('\n') + 1
        match = re.search(r'line (\d+), characters', row['stderr'])
        expected_file = '/checks/Contract.v' if is_probe else '/' + rel
        if (row['exit_code'] != 1 or not match or not lo <= int(match[1]) <= hi
                or expected_file not in row['stderr']):
            raise ValueError('caller control missed designated obligation: ' + str(row))
        for prerequisite in FILES if is_probe else FILES[:FILES.index(rel)]:
            if checks[label + ':' + Path(prerequisite).stem]['exit_code'] != 0:
                raise ValueError('caller control prerequisite failed')
    return {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS, 'source_location': location,
            'translated_statements': ['OS_SchedNew();', 'OSTCBHighRdy = OSTCBPrioTbl[OSPrioHighRdy];'],
            'root_assumptions': sorted(assumptions), 'negative_controls': CONTROLS}


def validate(root, checkpoint, checks, loader):
    inventory = json.loads((root / 'audit/repaired-source-inventory.json').read_text())
    expected = {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS,
        'source_location': next(f for f in inventory['functions'] if f['name'] == 'OS_Sched'),
        'translated_statements': ['OS_SchedNew();', 'OSTCBHighRdy = OSTCBPrioTbl[OSPrioHighRdy];'],
        'root_assumptions': checkpoint['root_assumptions'], 'negative_controls': CONTROLS}
    if checkpoint != expected:
        raise ValueError('caller checkpoint scope/roots/source/controls differ')
    if not set(checkpoint['root_assumptions']) <= loader(root, 'check-memory-trust.py').FRAMEWORK_ALLOWED:
        raise ValueError('unexpected caller root assumptions')
    for key in ['positive:' + Path(f).stem for f in FILES] + ['positive:contract', 'coqchk']:
        if checks['caller:' + key]['exit_code'] != 0:
            raise ValueError('caller checkpoint positive check failed')
    for label in CONTROLS:
        rel = TASKS if label.startswith(('bitmap_', 'table_')) else CALL if label.startswith('call_') else TARGET
        is_probe = '_false_premise_' in label
        for prerequisite in FILES if is_probe else FILES[:FILES.index(rel)]:
            if checks['caller:' + label + ':' + Path(prerequisite).stem]['exit_code'] != 0:
                raise ValueError('caller control prerequisite missing')
        key = label + (':contract' if is_probe else ':' + Path(rel).stem)
        if checks['caller:' + key]['exit_code'] != 1:
            raise ValueError('caller designated control missing')
