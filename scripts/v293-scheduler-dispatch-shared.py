#!/usr/bin/env python3
"""Actual guarded source prefix with the unique table AND target owned by Inv."""
from pathlib import Path
import re
import shutil

CORE = 'certiucos/v293/proofs/V293OSSchedDispatchShared.v'
WITNESS = 'certiucos/v293/proofs/V293OSSchedDispatchSharedWitness.v'
FILES = [CORE, WITNESS]
ROOTS = ['V293_dispatch_entry_open', 'V293_dispatch_entry_close',
         'V293_OSSched_dispatch_prefix', 'V293_OSSched_guarded_dispatch_prefix',
         'V293_dispatch_prefix_precondition_witness']
SCOPE = 'SOURCE_PREFIX_AND_GUARDS_WITH_SHARED_TARGET_NOT_COMPARE_COUNTER_SWITCH_OR_GOOD_OS'
OBLIGATIONS = {
    'post_time_changed_only': (CORE, 'Theorem V293_OSSched_dispatch_prefix :'),
    'callee_owns_dispatch_core_only': (CORE, 'Theorem V293_OSSched_dispatch_prefix :'),
    'target_returned_old_only': (CORE, 'Theorem V293_OSSched_dispatch_prefix :'),
    'guard_false_premise_added_only': (None, 'Definition checked_guarded_dispatch_prefix :'),
    'witness_stale_time_only': (WITNESS, 'Theorem V293_dispatch_prefix_precondition_witness :'),
    'disabled_guard_post_changed_only': (CORE, 'Theorem V293_OSSched_guarded_dispatch_prefix :'),
}
CONTROLS = {
    'post_time_changed_only': 'REJECTED_AT_V293_OSSched_dispatch_prefix_NOT_DOWNSTREAM_CREDIT',
    'callee_owns_dispatch_core_only': 'REJECTED_AT_V293_OSSched_dispatch_prefix_NOT_DOWNSTREAM_CREDIT',
    'target_returned_old_only': 'REJECTED_AT_V293_OSSched_dispatch_prefix_NOT_DOWNSTREAM_CREDIT',
    'guard_false_premise_added_only': 'CORE_AND_WITNESS_COMPILE_REJECTED_AT_checked_guarded_dispatch_prefix',
    'witness_stale_time_only': 'CORE_COMPILES_REJECTED_AT_V293_dispatch_prefix_precondition_witness',
    'disabled_guard_post_changed_only': 'PREFIX_COMPILES_REJECTED_AT_V293_OSSched_guarded_dispatch_prefix',
}

# Literal resource contracts, independent of the candidate root type.
PROBE = r'''

Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchSharedWitness.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSharedWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternalWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import Coq.Lists.List.
Local Open Scope nat_scope.
Definition checked_lent_fields (t : tid) (ts : TcbMod.map) (es : EcbMod.map) (n : int32) :=
  Aabsdata curtid (oscurt t) ** (Aabsdata abstcblsid (abstcblist ts) **
    (Aabsdata absecblsid (absecblist es) ** Aabsdata ostmid (ostm n))).
Definition checked_lent_snapshot target tp t ts es n := SWINV (V293_dispatch_inv target tp) //\\
  ((CurTid t ** checked_lent_fields t ts es n) ** Atrue).
Definition checked_lent_flags := (isrclr ** Aie false) ** (EX k : hid, ATopis k).
Definition checked_target target tp := EX v : val,
  [|rule_type_val_match (Tptr tp) v = true|] ** (GV target @ (Tptr tp) |-> v).
Definition checked_core target tp :=
  (EX t : tid, EX ts : TcbMod.map, EX es : EcbMod.map, EX n : int32,
    CurTid t ** checked_lent_fields t ts es n) ** checked_target target tp.
Definition checked_inv_shape : forall target tp k,
  getinv (V293_dispatch_inv target tp k) =
    match k with O => checked_core target tp | S _ => Aemp end :=
  fun target tp k => match k with O => eq_refl | S _ => eq_refl end.
Definition checked_snapshot_open : forall target tp t ts es n,
  checked_lent_snapshot target tp t ts es n ==>
    checked_lent_flags ** ((CurTid t ** checked_lent_fields t ts es n) ** checked_target target tp) :=
  V293_dispatch_entry_open.
Definition checked_snapshot_close : forall target tp t ts es n,
  checked_lent_flags ** ((CurTid t ** checked_lent_fields t ts es n) ** checked_target target tp) ==>
    checked_lent_snapshot target tp t ts es n := V293_dispatch_entry_close.
Definition checked_opened_shape : forall k, getinv (V293_opened_inv k) = Aemp := fun k => eq_refl.
Definition checked_returned_snapshot target tp t ts es n next :=
  SWINV (V293_dispatch_inv target tp) //\\
    (((CurTid t ** checked_lent_fields t ts es n) **
      (GV target @ (Tptr tp) |-> (Vptr next))) ** Atrue).
Definition checked_lent_pre unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks events now frame stack critical :=
  (V293_sched_internal_pre unmap group rows high bt bg br bh lo hi li tid aop **
    (checked_lent_snapshot target tp tid tasks events now ** (Ais stack ** Acs critical))) **
  ((V293_prefix_bindings table high target tp bp bo ** V293_read_pointers tp bp 0 entries) **
    frame).
Definition checked_lent_post unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks events now frame stack critical :=
  EX t : Modules.tid, [|V293_highest_ready tasks t|] **
    ((V293_sched_internal_post unmap group rows high bt bg br bh lo hi li tid aop None **
      (checked_returned_snapshot target tp tid tasks events now t ** (Ais stack ** Acs critical))) **
      ((V293_prefix_bindings table high target tp bp bo ** V293_read_pointers tp bp 0 entries) **
        frame)).
Definition checked_dispatch_prefix : forall Spec sd li r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks events now
    stack critical (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh li V293_opened_inv Hli,
     V293_critical_fpost unmap group rows high bt bg br bh li V293_opened_inv Hli, (Tvoid, nil)) ->
  InfRules Spec sd li (V293_dispatch_inv target tp) r ri
    (checked_lent_pre unmap group rows high bt bg br bh lo hi li tid aop
      table target tp bp bo entries tasks events now frame stack critical)
    (V293_OSSched_unlocked_prefix sched_id table high target)
    (checked_lent_post unmap group rows high bt bg br bh lo hi li tid aop
      table target tp bp bo entries tasks events now frame stack critical) tid :=
  V293_OSSched_dispatch_prefix.
Definition checked_guarded_dispatch_prefix : forall Spec sd li r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks events now
    stack critical interrupt lock bi bl ni nl (Hli : GoodLInvAsrt li),
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks -> GoodFrm frame ->
  ni < 256 -> nl < 256 ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh li V293_opened_inv Hli,
     V293_critical_fpost unmap group rows high bt bg br bh li V293_opened_inv Hli, (Tvoid, nil)) ->
  let gf := V293_guard_cell interrupt bi ni ** (V293_guard_cell lock bl nl ** frame) in
  let pre := checked_lent_pre unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks events now gf stack critical in
  let post := checked_lent_post unmap group rows high bt bg br bh lo hi li tid aop
    table target tp bp bo entries tasks events now gf stack critical in
  InfRules Spec sd li (V293_dispatch_inv target tp) r ri pre
    (V293_OSSched_guards interrupt lock (V293_OSSched_unlocked_prefix sched_id table high target))
    (if Nat.eqb ni 0 && Nat.eqb nl 0 then post else pre) tid := V293_OSSched_guarded_dispatch_prefix.
Definition checked_shared_entry : forall different es n, exists s,
  V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
  V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
  V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
  (V293_ready_select 0 16 (V293_ready_group 0 16) <> V293_current_mode_priority different <-> different = true) /\
  s |= checked_lent_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
    0 16 V293_witness_li V293_idle_tid (spec_done None)
    106%Z 107%Z Tvoid 8%positive 10%positive
    (V293_current_mode_entries different) (V293_current_mode_tasks different) es n Aemp nil nil :=
  V293_dispatch_prefix_precondition_witness.
'''

def mutations(source, witness, replace):
    a = source.index('Definition V293_dispatch_prefix_post ')
    b = source.index('Theorem V293_OSSched_dispatch_prefix :', a)
    time = source[:a] + replace(source[a:b],
        'tasks events now next **', 'tasks events (Int.add now Int.one) next **') + source[b:]
    target = source[:a] + replace(source[a:b],
        'tasks events now next **', 'tasks events now tid **') + source[b:]
    a = source.index('Theorem V293_OSSched_dispatch_prefix :')
    b = source.index('Proof.', a)
    lookup = source[:a] + source[a:b].replace('li V293_opened_inv Hli',
        'li (V293_dispatch_inv target tp) Hli') + source[b:]
    a = source.index('Theorem V293_OSSched_guarded_dispatch_prefix :')
    false = source[:a] + replace(source[a:], '  lo < 256 -> hi < 256 ->',
        '  False -> lo < 256 -> hi < 256 ->')
    false = replace(false, 'Hli Hlo Hhi Hr Hb Htable Hframe Hni Hnl Hspec gf pre post.',
                    'Hli Hfalse Hlo Hhi Hr Hb Htable Hframe Hni Hnl Hspec gf pre post.')
    stale = replace(witness,
        '(V293_OSSched_shared_precondition_witness different events now)',
        '(V293_OSSched_shared_precondition_witness different events (Int.add now Int.one))')
    disabled = replace(source, 'then post else pre) tid.', 'then post else post) tid.')
    texts = {'post_time_changed_only': (time, witness),
             'callee_owns_dispatch_core_only': (lookup, witness),
             'target_returned_old_only': (target, witness),
             'guard_false_premise_added_only': (false, witness),
             'witness_stale_time_only': (source, stale),
             'disabled_guard_post_changed_only': (disabled, witness)}
    return {label: (*pair, *OBLIGATIONS[label]) for label, pair in texts.items()}

def check_rejection(row, source, failed_rel, declaration, label):
    start = source.index(declaration)
    lo = source[:start].count('\n') + 1
    # A contract may have let-bindings before its final :=, and qualified
    # constants contain dots. Only a statement-terminating dot ends it.
    end = (start + re.search(r'\.(?=\s|$)', source[start:]).end()
           if failed_rel is None else source.index('Qed.', start) + len('Qed.'))
    hi = source[:end].count('\n') + 1
    match = re.search(r'File "([^"\n]+)", line (\d+), characters', row['stderr'])
    expected_file = '/checks/Contract.v' if failed_rel is None else '/' + failed_rel
    if (row['exit_code'] != 1 or not match or not lo <= int(match[2]) <= hi
            or not ('/' + match[1]).endswith(expected_file) or '\nError:' not in row['stderr']):
        raise ValueError('dispatch-shared control missed designated obligation: ' + label + ': ' + str(row))


def check(root, work, build, coqbin, run, loader, location):
    caller = loader(root, 'v293-scheduler-caller.py')
    probe = PROBE
    checks = {}
    def record(label, command, cwd):
        if label in checks:
            raise ValueError('duplicate shared command identity: ' + label)
        row = run('dispatch_shared:' + label, command, cwd); checks[label] = row
        return row

    def compile_tree(label, core, witness, assumptions=False):
        dest = work / ('dispatch_shared_' + label)
        shutil.copytree(build / 'certiucos', dest / 'certiucos')
        (dest / 'checks').mkdir()
        flags = ['-R', str(build / 'framework'), 'CertiOS.framework',
                 '-R', str(build / 'tactics'), 'CertiOS.tactics',
                 '-R', str(dest / 'certiucos'), 'CertiOS.certiucos',
                 '-R', str(dest / 'checks'), 'DispatchSharedCheck']
        for rel, contents in zip(FILES, [core, witness]):
            path = dest / rel
            for suffix in ['.vo', '.vos', '.vok', '.glob']:
                path.with_suffix(suffix).unlink(missing_ok=True)
            path.write_text(contents)
            row = record(label + ':' + Path(rel).stem, [coqbin + 'coqc', '-q', *flags, str(path)], dest)
            if row['exit_code']:
                return row, flags, dest
        path = dest / 'checks/Contract.v'
        path.write_text(probe + ('\n' + '\n'.join('Print Assumptions ' + r + '.' for r in ROOTS) if assumptions else ''))
        return record(label + ':contract', [coqbin + 'coqc', '-q', *flags, str(path)], dest), flags, dest

    source = (root / CORE).read_text(); witness = (root / WITNESS).read_text()
    variants = mutations(source, witness, caller.replace_once)
    row, flags, dest = compile_tree('positive', source, witness, assumptions=True)
    if row['exit_code']:
        raise ValueError('dispatch-shared proof/probe failed: ' + str(row))
    trust = loader(root, 'check-memory-trust.py'); assumptions = set()
    for part in row['stdout'].split('Axioms:')[1:]:
        assumptions |= set(trust.check_assumptions(part.split('Closed under the global context')[0], trust.FRAMEWORK_ALLOWED))
    if row['stdout'].count('Axioms:') + row['stdout'].count('Closed under the global context') != len(ROOTS):
        raise ValueError('missing dispatch-shared root assumption output')
    row = record('coqchk', [coqbin + 'coqchk', '-silent', *flags,
        *['CertiOS.' + Path(f).with_suffix('').as_posix().replace('/', '.') for f in FILES],
        'DispatchSharedCheck.Contract'], dest)
    if row['exit_code']:
        raise ValueError('dispatch-shared coqchk failed: ' + str(row))
    for label, (core, wit, failed_rel, declaration) in variants.items():
        row, _, _ = compile_tree(label, core, wit)
        failed_source = probe if failed_rel is None else (core if failed_rel == CORE else wit)
        check_rejection(row, failed_source, failed_rel, declaration, label)
        for rel in (FILES if failed_rel is None else FILES[:FILES.index(failed_rel)]):
            if checks[label + ':' + Path(rel).stem]['exit_code'] != 0:
                raise ValueError('dispatch-shared control prerequisite failed')
    return {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS, 'source_location': location,
            'root_assumptions': sorted(assumptions), 'negative_controls': CONTROLS}


def validate(root, checkpoint, checks, loader):
    import json
    inventory = json.loads((root / 'audit/repaired-source-inventory.json').read_text())
    expected = {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS,
        'source_location': next(f for f in inventory['functions'] if f['name'] == 'OS_Sched'),
        'root_assumptions': checkpoint['root_assumptions'], 'negative_controls': CONTROLS}
    if checkpoint != expected:
        raise ValueError('dispatch-shared checkpoint scope/roots/source/controls differ')
    if not set(checkpoint['root_assumptions']) <= loader(root, 'check-memory-trust.py').FRAMEWORK_ALLOWED:
        raise ValueError('unexpected dispatch-shared root assumptions')
    for key in ['positive:' + Path(f).stem for f in FILES] + ['positive:contract', 'coqchk']:
        if checks['dispatch_shared:' + key]['exit_code'] != 0:
            raise ValueError('dispatch-shared checkpoint positive check failed')
    for label, (failed_rel, _) in OBLIGATIONS.items():
        fail = 'contract' if failed_rel is None else Path(failed_rel).stem
        prerequisites = FILES if failed_rel is None else FILES[:FILES.index(failed_rel)]
        for rel in prerequisites:
            if checks['dispatch_shared:' + label + ':' + Path(rel).stem]['exit_code'] != 0:
                raise ValueError('dispatch-shared control prerequisite missing')
        if checks['dispatch_shared:' + label + ':' + fail]['exit_code'] != 1:
            raise ValueError('shared designated control missing')
    variants = mutations((root / CORE).read_text(), (root / WITNESS).read_text(),
                         loader(root, 'v293-scheduler-caller.py').replace_once)
    for label, (core, witness, failed_rel, declaration) in variants.items():
        fail = 'contract' if failed_rel is None else Path(failed_rel).stem
        text = PROBE if failed_rel is None else core if failed_rel == CORE else witness
        check_rejection(checks['dispatch_shared:' + label + ':' + fail], text, failed_rel, declaration, label)
