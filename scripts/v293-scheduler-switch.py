#!/usr/bin/env python3
"""Actual SCAP normal switch with a shared target cell, not source OS_Sched."""
from pathlib import Path
import re
import shutil

STATE = 'certiucos/v293/proofs/V293DispatchState.v'
CORE = 'certiucos/v293/proofs/V293OSSchedSwitch.v'
WITNESS = 'certiucos/v293/proofs/V293OSSchedSwitchWitness.v'
FILES = [STATE, CORE, WITNESS]
ROOTS = ['V293_dispatch_cell_precise', 'V293_dispatch_store', 'V293_dispatch_good',
         'V293_dispatch_snapshot_open', 'V293_dispatch_snapshot_close',
         'V293_shared_payload_switch_pre', 'V293_shared_normal_switch',
         'V293_pending_switch_precondition_witness']
SCOPE = 'ACTUAL_SCAP_NORMAL_SWITCH_WITH_SHARED_TARGET_NOT_SOURCE_CALLER_OR_PHYSICAL_KERNEL_OR_GOOD_OS'
OBLIGATIONS = {
    'resumed_action_pending_only': (CORE, 'Theorem V293_shared_normal_switch :'),
    'reserved_current_half_removed_only': (CORE, 'Theorem V293_shared_payload_switch_pre :'),
    'switch_false_premise_added_only': (None, 'Definition checked_normal_switch :'),
    'witness_pending_action_removed_only': (WITNESS, 'Theorem V293_pending_switch_precondition_witness :'),
    'full_view_target_cell_omitted_only': (STATE, 'Lemma V293_dispatch_switch_full :'),
}
CONTROLS = {
    'resumed_action_pending_only': 'STATE_COMPILES_REJECTED_AT_V293_shared_normal_switch',
    'reserved_current_half_removed_only': 'STATE_COMPILES_REJECTED_AT_V293_shared_payload_switch_pre_NOT_DOWNSTREAM_CREDIT',
    'switch_false_premise_added_only': 'ALL_THREE_MODULES_COMPILE_FIXED_checked_normal_switch_REJECTS',
    'witness_pending_action_removed_only': 'STATE_AND_SWITCH_COMPILE_REJECTED_AT_PENDING_WITNESS',
    'full_view_target_cell_omitted_only': 'REJECTED_AT_V293_dispatch_switch_full_NOT_DOWNSTREAM_CREDIT',
}

# Independent literal expected interface. Neither inferred from proof text nor
# made weaker in response to a mutant. Target cell and all four slots are fixed.
PROBE = r'''
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchWitness.
Require Import Coq.Lists.List.
Definition checked_fields t tasks events now :=
  Aabsdata curtid (oscurt t) ** (Aabsdata abstcblsid (abstcblist tasks) **
    (Aabsdata absecblsid (absecblist events) ** Aabsdata ostmid (ostm now))).
Definition checked_target target tp := EX v : val,
  [|rule_type_val_match (Tptr tp) v = true|] ** GV target @ (Tptr tp) |-> v.
Definition checked_core target tp :=
  (EX t : tid, EX tasks : TcbMod.map, EX events : EcbMod.map, EX now : int32,
    CurTid t ** checked_fields t tasks events now) ** checked_target target tp.
Definition checked_inv_shape : forall target tp k,
  getinv (V293_dispatch_inv target tp k) =
    match k with O => checked_core target tp | S _ => Aemp end :=
  fun target tp k => match k with O => eq_refl | S _ => eq_refl end.
Definition checked_li_shape : V293_shared_li = (fun _ _ => Aemp) := eq_refl.
Definition checked_target_precise : forall target tp, precise (checked_target target tp) :=
  V293_dispatch_cell_precise.
Definition checked_dispatch_store : forall target tq ct t ge le M M' ir aux O op b tp,
  (ge, le, M, ir, aux, O, op) |= SWINVt (V293_dispatch_inv target tq) ct ->
  get ge OSTCBCur = Some (b, Tptr tp) ->
  store (Tptr tp) M (b, 0%Z) (Vptr t) = Some M' ->
  (ge, le, M', ir, aux, set O curtid (oscurt t), op) |= SWINVt (V293_dispatch_inv target tq) t :=
  V293_dispatch_store.
Definition checked_dispatch_good : forall target tp,
  GoodI (V293_dispatch_inv target tp) V293_scheduler (fun _ _ => Aemp) := V293_dispatch_good.
Definition checked_flags := (isrclr ** Aie false) ** (EX k : hid, ATopis k).
Definition checked_snapshot target tp t tasks events now next :=
  SWINV (V293_dispatch_inv target tp) //\\
    (((CurTid t ** checked_fields t tasks events now) **
      (GV target @ (Tptr tp) |-> (Vptr next))) ** Atrue).
Definition checked_open : forall target tp t tasks events now next,
  checked_snapshot target tp t tasks events now next ==>
    checked_flags ** ((CurTid t ** checked_fields t tasks events now) **
      (GV target @ (Tptr tp) |-> (Vptr next))) := V293_dispatch_snapshot_open.
Definition checked_close : forall target tp t tasks events now next,
  checked_flags ** ((CurTid t ** checked_fields t tasks events now) **
    (GV target @ (Tptr tp) |-> (Vptr next))) ==>
    checked_snapshot target tp t tasks events now next := V293_dispatch_snapshot_close.
Definition checked_payload target tp t tasks events now next aop stack critical :=
  <||sched;;aop||> ** ((checked_snapshot target tp t tasks events now next ** CurTid t) **
    (Ais stack ** Acs critical)).
Definition checked_spatial_switch : forall target tp t tasks events now next aop stack critical,
  indom tasks t -> V293_highest_ready tasks next ->
  checked_payload target tp t tasks events now next aop stack critical ==>
    SWPRE_NDEAD V293_scheduler target t := V293_shared_payload_switch_pre.
Definition checked_normal_switch : forall Spec r ri target tp t aop tasks events now next stack critical px,
  indom tasks t -> V293_highest_ready tasks next -> GoodFrm px ->
  (px ==> LINV (fun _ _ => Aemp) t nil ** Atrue) ->
  InfRules Spec V293_scheduler (fun _ _ => Aemp) (V293_dispatch_inv target tp) r ri
    (checked_payload target tp t tasks events now next aop stack critical ** px)
    (sprim (switch target))
    (<||aop||> ** SWINVt (V293_dispatch_inv target tp) t ** Ais stack ** Acs critical ** px) t :=
  V293_shared_normal_switch.
Definition checked_tasks (different : bool) : TcbMod.map := if different then
  set (sig (7%positive, Int.zero) (Int.repr 4, wait os_stat_time Int.one, Vnull))
    (15%positive, Int.zero) (Int.repr 12, rdy, Vnull)
  else sig (7%positive, Int.zero) (Int.repr 12, rdy, Vnull).
Definition checked_next (different : bool) : tid :=
  if different then (15%positive, Int.zero) else (7%positive, Int.zero).
Definition checked_pending_entry : forall different events now aop, exists s,
  indom (checked_tasks different) (7%positive, Int.zero) /\
  V293_highest_ready (checked_tasks different) (checked_next different) /\
  s |= checked_payload 107%Z Tvoid (7%positive, Int.zero)
    (checked_tasks different) events now (checked_next different) aop nil nil ** Aemp :=
  V293_pending_switch_precondition_witness.
'''

def mutations(state, core, witness, replace):
    resumed = replace(core, '<||aop||> ** SWINVt', '<||sched;;aop||> ** SWINVt')
    half = replace(core, 'next ** CurTid tid) **', 'next ** Aemp) **')
    a = core.index('Theorem V293_shared_normal_switch :')
    false = core[:a] + replace(core[a:],
        '  indom tasks tid -> V293_highest_ready tasks next -> GoodFrm px ->',
        '  False -> indom tasks tid -> V293_highest_ready tasks next -> GoodFrm px ->')
    false = replace(false, 'stack critical px Hmember Hhighest Hpx Hlocal.',
                          'stack critical px Hfalse Hmember Hhighest Hpx Hlocal.')
    pending = replace(witness,
        'O, (sched;;aop)) : RstateOP).', 'O, aop) : RstateOP).')
    a = state.index('Definition V293_dispatch_full ')
    b = state.index('Lemma V293_dispatch_switch_full :', a)
    target = state[:a] + replace(state[a:b],
        '(V293_shared_fields t ts es n ** V293_dispatch_cell target tp).',
        '(V293_shared_fields t ts es n ** Aemp).') + state[b:]
    target = replace(target, 'Definition V293_dispatch_full target tp t :=',
                     'Definition V293_dispatch_full (target : var) (tp : type) t :=')
    texts = {
        'resumed_action_pending_only': (state, resumed, witness),
        'reserved_current_half_removed_only': (state, half, witness),
        'switch_false_premise_added_only': (state, false, witness),
        'witness_pending_action_removed_only': (state, core, pending),
        'full_view_target_cell_omitted_only': (target, core, witness),
    }
    return {label: (*triple, *OBLIGATIONS[label]) for label, triple in texts.items()}

def check_rejection(row, source, failed_rel, declaration, label):
    start = source.index(declaration)
    lo = source[:start].count('\n') + 1
    end = (source.index('.', source.index(':=', start)) + 1
           if failed_rel is None else source.index('Qed.', start) + len('Qed.'))
    hi = source[:end].count('\n') + 1
    match = re.search(r'File "([^"\n]+)", line (\d+), characters', row['stderr'])
    expected_file = '/checks/Contract.v' if failed_rel is None else '/' + failed_rel
    if (row['exit_code'] != 1 or not match or not lo <= int(match[2]) <= hi
            or not ('/' + match[1]).endswith(expected_file) or '\nError:' not in row['stderr']):
        raise ValueError('normal-switch control missed designated obligation: ' + label + ': ' + str(row))


def check(root, work, build, coqbin, run, loader, location):
    caller = loader(root, 'v293-scheduler-caller.py')
    probe = PROBE
    checks = {}
    def record(label, command, cwd):
        if label in checks:
            raise ValueError('duplicate normal-switch command identity: ' + label)
        row = run('normal_switch:' + label, command, cwd); checks[label] = row
        return row

    def compile_tree(label, state, core, witness, assumptions=False):
        dest = work / ('normal_switch_' + label)
        shutil.copytree(build / 'certiucos', dest / 'certiucos')
        (dest / 'checks').mkdir()
        flags = ['-R', str(build / 'framework'), 'CertiOS.framework',
                 '-R', str(build / 'tactics'), 'CertiOS.tactics',
                 '-R', str(dest / 'certiucos'), 'CertiOS.certiucos',
                 '-R', str(dest / 'checks'), 'NormalSwitchCheck']
        for rel, contents in zip(FILES, [state, core, witness]):
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

    state = (root / STATE).read_text(); source = (root / CORE).read_text(); witness = (root / WITNESS).read_text()
    variants = mutations(state, source, witness, caller.replace_once)
    row, flags, dest = compile_tree('positive', state, source, witness, assumptions=True)
    if row['exit_code']:
        raise ValueError('normal-switch proof/probe failed: ' + str(row))
    trust = loader(root, 'check-memory-trust.py'); assumptions = set()
    for part in row['stdout'].split('Axioms:')[1:]:
        assumptions |= set(trust.check_assumptions(part.split('Closed under the global context')[0], trust.FRAMEWORK_ALLOWED))
    if row['stdout'].count('Axioms:') + row['stdout'].count('Closed under the global context') != len(ROOTS):
        raise ValueError('missing normal-switch root assumption output')
    row = record('coqchk', [coqbin + 'coqchk', '-silent', *flags,
        *['CertiOS.' + Path(f).with_suffix('').as_posix().replace('/', '.') for f in FILES],
        'NormalSwitchCheck.Contract'], dest)
    if row['exit_code']:
        raise ValueError('normal-switch coqchk failed: ' + str(row))
    for label, (state, core, wit, failed_rel, declaration) in variants.items():
        row, _, _ = compile_tree(label, state, core, wit)
        failed_source = probe if failed_rel is None else (dict(zip(FILES, [state, core, wit]))[failed_rel])
        check_rejection(row, failed_source, failed_rel, declaration, label)
        for rel in (FILES if failed_rel is None else FILES[:FILES.index(failed_rel)]):
            if checks[label + ':' + Path(rel).stem]['exit_code'] != 0:
                raise ValueError('normal-switch control prerequisite failed')
    return {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS, 'source_location': location,
            'root_assumptions': sorted(assumptions), 'negative_controls': CONTROLS}


def validate(root, checkpoint, checks, loader):
    import json
    inventory = json.loads((root / 'audit/repaired-source-inventory.json').read_text())
    expected = {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS,
        'source_location': next(f for f in inventory['functions'] if f['name'] == 'OS_Sched'),
        'root_assumptions': checkpoint['root_assumptions'], 'negative_controls': CONTROLS}
    if checkpoint != expected:
        raise ValueError('normal-switch checkpoint scope/roots/source/controls differ')
    if not set(checkpoint['root_assumptions']) <= loader(root, 'check-memory-trust.py').FRAMEWORK_ALLOWED:
        raise ValueError('unexpected normal-switch root assumptions')
    for key in ['positive:' + Path(f).stem for f in FILES] + ['positive:contract', 'coqchk']:
        if checks['normal_switch:' + key]['exit_code'] != 0:
            raise ValueError('normal-switch checkpoint positive check failed')
    for label, (failed_rel, _) in OBLIGATIONS.items():
        fail = 'contract' if failed_rel is None else Path(failed_rel).stem
        prerequisites = FILES if failed_rel is None else FILES[:FILES.index(failed_rel)]
        for rel in prerequisites:
            if checks['normal_switch:' + label + ':' + Path(rel).stem]['exit_code'] != 0:
                raise ValueError('normal-switch control prerequisite missing')
        if checks['normal_switch:' + label + ':' + fail]['exit_code'] != 1:
            raise ValueError('shared designated control missing')
    variants = mutations((root / STATE).read_text(), (root / CORE).read_text(), (root / WITNESS).read_text(),
                         loader(root, 'v293-scheduler-caller.py').replace_once)
    for label, (state, core, witness, failed_rel, declaration) in variants.items():
        fail = 'contract' if failed_rel is None else Path(failed_rel).stem
        text = PROBE if failed_rel is None else dict(zip(FILES, [state, core, witness]))[failed_rel]
        check_rejection(checks['normal_switch:' + label + ':' + fail], text, failed_rel, declaration, label)
