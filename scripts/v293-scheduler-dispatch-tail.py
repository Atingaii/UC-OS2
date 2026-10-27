#!/usr/bin/env python3
"""Guarded prefix, comparison, modular increment and actual ordinary switch.

Literal independent contracts; no suffix oracle and no function coverage credit.
"""
from pathlib import Path
import re
import shutil

CORE = 'certiucos/v293/proofs/V293OSSchedDispatchTail.v'
WITNESS = 'certiucos/v293/proofs/V293OSSchedDispatchTailWitness.v'
FILES = [CORE, WITNESS]
ROOTS = ['V293_dispatch_locals_good', 'V293_dispatch_tail_split', 'V293_dispatch_tail_comparison', 'V293_dispatch_tail_increment', 'V293_dispatch_tail_switch', 'V293_dispatch_change_switch', 'V293_dispatch_prefix_change_switch', 'V293_OSSched_guarded_dispatch_switch', 'V293_dispatch_full_precondition_witness']
SCOPE = 'GUARDED_SOURCE_PREFIX_TO_NORMAL_SCAP_SWITCH_NOT_PORT_CORRESPONDENCE_OR_GOOD_OS'
OBLIGATIONS = {
    'counter_post_two_only': (CORE, 'Theorem V293_dispatch_tail_increment :'),
    'resumed_pending_action_only': (CORE, 'Theorem V293_dispatch_tail_switch :'),
    'branch_condition_inverted_only': (CORE, 'Theorem V293_dispatch_change_switch :'),
    'guard_false_premise_only': (None, 'Definition checked_V293_OSSched_guarded_dispatch_switch :'),
    'witness_pending_removed_only': (WITNESS, 'Theorem V293_dispatch_full_precondition_witness :'),
    'reserved_half_neutralized_only': (CORE, 'Lemma V293_dispatch_tail_split :'),
}
CONTROLS = {
    'counter_post_two_only': 'REJECTED_AT_V293_dispatch_tail_increment_NOT_DOWNSTREAM_CREDIT',
    'resumed_pending_action_only': 'REJECTED_AT_V293_dispatch_tail_switch_NOT_DOWNSTREAM_CREDIT',
    'branch_condition_inverted_only': 'REJECTED_AT_V293_dispatch_change_switch_NOT_DOWNSTREAM_CREDIT',
    'guard_false_premise_only': 'CORE_AND_WITNESS_COMPILE_REJECTED_AT_checked_V293_OSSched_guarded_dispatch_switch',
    'witness_pending_removed_only': 'CORE_COMPILES_REJECTED_AT_V293_dispatch_full_precondition_witness',
    'reserved_half_neutralized_only': 'REJECTED_AT_V293_dispatch_tail_split_NOT_DOWNSTREAM_CREDIT',
}

# Static literal contracts. Do not derive expected types from candidate types.
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

Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchTailWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.

Definition checked_switch_payload target tp tid tasks events now next aop stack critical :=
  <||sched;;aop||> ** ((checked_returned_snapshot target tp tid tasks events now next ** CurTid tid) **
    (Ais stack ** Acs critical)).
Definition checked_switch_resume target tp tid aop stack critical px :=
  <||aop||> ** SWINVt (V293_dispatch_inv target tp) tid ** Ais stack ** Acs critical ** px.
Section CheckedDispatchTail.
Variables unmap group rows high : var.
Variables bt bg br bh : block.
Variables lo hi : nat.
Variable tid : Modules.tid.
Variable aop : spec_code.
Variables table target : var.
Variable tp : type.
Variables bp bo : block.
Variable entries : list val.
Variable tasks : TcbMod.map.
Variable events : EcbMod.map.
Variable now : int32.
Variables current counter : var.
Variables bcur bcounter : block.
Variable nc : nat.
Variable frame : asrt.
Variable stack : list hid.
Variable critical : list bool.
Definition checked_dispatch_tail c :=
  checked_lent_post unmap group rows high bt bg br bh lo hi V293_shared_li tid (sched;;aop)
    table target tp bp bo entries tasks events now
    (V293_guard_cell current bcur nc ** (V293_counter_cell counter bcounter c ** frame)) stack critical.

(* This frame contains no current pointer, shared abstract slots, target cell,
   action, interrupt flag or stack. Atrue preserves the CurLINV remainder. *)
Definition checked_dispatch_locals c :=
  ((V293_sched_globals unmap group rows high bt bg br bh **
    V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi)) **
    PV (bh, Int.zero) @ Tint8 |->
      (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
  ((V293_prefix_bindings table high target tp bp bo ** V293_read_pointers tp bp 0 entries) **
    (V293_guard_cell current bcur nc ** (V293_counter_cell counter bcounter c ** (frame ** Atrue)))).

Definition checked_V293_dispatch_locals_good : forall c, GoodFrm frame -> GoodFrm (checked_dispatch_locals c).
Proof. intros; eapply V293_dispatch_locals_good; eassumption. Qed.

Definition checked_V293_dispatch_tail_split : forall c,
  checked_dispatch_tail c ==>
  EX next : Modules.tid, [|V293_highest_ready tasks next|] **
    (checked_switch_payload target tp tid tasks events now next aop stack critical ** checked_dispatch_locals c).
Proof. intros; eapply V293_dispatch_tail_split; eassumption. Qed.

Definition checked_V293_dispatch_tail_comparison : forall c s,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  s |= checked_dispatch_tail c ->
  evalval (V293_OSSched_different high current) (getsmem s) =
    Some (Vint32 (if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc then Int.zero else Int.one)) /\
  evaltype (V293_OSSched_different high current) (getsmem s) = Some Tint32.
Proof. intros; eapply V293_dispatch_tail_comparison; eassumption. Qed.

Definition checked_V293_dispatch_tail_increment : forall Spec sd I r ri c,
  InfRules Spec sd V293_shared_li I r ri (checked_dispatch_tail c)
    (V293_OSSched_increment counter) (checked_dispatch_tail (Int.add c Int.one)) tid.
Proof. intros; eapply V293_dispatch_tail_increment; eassumption. Qed.

Definition checked_dispatch_resumed c :=
  checked_switch_resume target tp tid aop stack critical (checked_dispatch_locals c).
Definition checked_V293_dispatch_tail_switch : forall Spec r ri c,
  indom tasks tid -> GoodFrm frame ->
  InfRules Spec V293_scheduler V293_shared_li (V293_dispatch_inv target tp) r ri
    (checked_dispatch_tail c) (sprim (switch target)) (checked_dispatch_resumed c) tid.
Proof. intros; eapply V293_dispatch_tail_switch; eassumption. Qed.

Definition checked_dispatch_changed c :=
  if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc
  then checked_dispatch_tail c else checked_dispatch_resumed (Int.add c Int.one).
Definition checked_V293_dispatch_change_switch : forall Spec r ri c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) -> nc < 256 ->
  indom tasks tid -> GoodFrm frame ->
  InfRules Spec V293_scheduler V293_shared_li (V293_dispatch_inv target tp) r ri
    (checked_dispatch_tail c)
    (V293_OSSched_change high current counter (sprim (switch target)))
    (checked_dispatch_changed c) tid.
Proof. intros; eapply V293_dispatch_change_switch; eassumption. Qed.

Definition checked_V293_dispatch_prefix_change_switch : forall Spec r ri sched_id c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  V293_current_task tasks tid nc -> GoodFrm frame ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good, (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_dispatch_inv target tp) r ri
    (checked_lent_pre unmap group rows high bt bg br bh lo hi V293_shared_li tid (sched;;aop)
      table target tp bp bo entries tasks events now
      (V293_guard_cell current bcur nc ** (V293_counter_cell counter bcounter c ** frame)) stack critical)
    (sseq (V293_OSSched_unlocked_prefix sched_id table high target)
      (V293_OSSched_change high current counter (sprim (switch target))))
    (checked_dispatch_changed c) tid.
Proof. intros; eapply V293_dispatch_prefix_change_switch; eassumption. Qed.

End CheckedDispatchTail.
Definition checked_V293_OSSched_guarded_dispatch_switch : forall Spec r ri tid aop frame
    sched_id unmap group rows high bt bg br bh lo hi table target tp bp bo entries tasks events now
    stack critical interrupt lock bi bl ni nl current counter bcur bcounter nc c,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  V293_current_task tasks tid nc -> GoodFrm frame -> ni < 256 -> nl < 256 ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good, (Tvoid, nil)) ->
  let gf := V293_guard_cell interrupt bi ni ** (V293_guard_cell lock bl nl ** frame) in
  let pre := checked_lent_pre unmap group rows high bt bg br bh lo hi V293_shared_li tid (sched;;aop)
    table target tp bp bo entries tasks events now
    (V293_guard_cell current bcur nc ** (V293_counter_cell counter bcounter c ** gf)) stack critical in
  let post := checked_dispatch_changed unmap group rows high bt bg br bh lo hi tid aop
    table target tp bp bo entries tasks events now current counter bcur bcounter nc gf stack critical c in
  InfRules Spec V293_scheduler V293_shared_li (V293_dispatch_inv target tp) r ri pre
    (V293_OSSched_guards interrupt lock
      (sseq (V293_OSSched_unlocked_prefix sched_id table high target)
        (V293_OSSched_change high current counter (sprim (switch target)))))
    (if Nat.eqb ni 0 && Nat.eqb nl 0 then post else pre) tid.
Proof. intros; eapply V293_OSSched_guarded_dispatch_switch; eassumption. Qed.

Definition checked_V293_dispatch_full_precondition_witness : forall different ni nl c events now aop,
  ni < 256 -> nl < 256 -> exists s,
  V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
  V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
  V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
  (V293_ready_select 0 16 (V293_ready_group 0 16) <> V293_current_mode_priority different <-> different = true) /\
  s |= checked_lent_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
    0 16 V293_shared_li V293_idle_tid (sched;;aop)
    106%Z 107%Z Tvoid 8%positive 10%positive
    (V293_current_mode_entries different) (V293_current_mode_tasks different) events now
    (V293_guard_cell 110%Z 13%positive (V293_current_mode_priority different) **
      (V293_counter_cell 111%Z 14%positive c **
        (V293_guard_cell 108%Z 11%positive ni ** (V293_guard_cell 109%Z 12%positive nl ** Aemp)))) nil nil.
Proof. intros; eapply V293_dispatch_full_precondition_witness; eassumption. Qed.


'''

def mutations(source, witness, replace):
    def region(text, begin, end, old, new):
        a = text.index(begin); b = text.index(end, a)
        return text[:a] + replace(text[a:b], old, new) + text[b:]
    counter = region(source, 'Theorem V293_dispatch_tail_increment :', 'Proof.',
        '(V293_dispatch_tail (Int.add c Int.one))', '(V293_dispatch_tail (Int.add c (Int.repr 2)))')
    pending = region(source, 'Definition V293_dispatch_resumed ', 'Theorem V293_dispatch_tail_switch :',
        'tp tid aop stack critical', 'tp tid (sched;;aop) stack critical')
    branch = region(source, 'Definition V293_dispatch_changed_post ', 'Theorem V293_dispatch_change_switch :',
        'if Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc',
        'if negb (Nat.eqb (V293_ready_select lo hi (V293_ready_group lo hi)) nc)')
    false = region(source, 'Theorem V293_OSSched_guarded_dispatch_switch :', 'Qed.',
        '  lo < 256 -> hi < 256', '  False -> lo < 256 -> hi < 256')
    false = region(false, 'Theorem V293_OSSched_guarded_dispatch_switch :', 'Qed.',
        'nc c Hlo Hhi', 'nc c Hfalse Hlo Hhi')
    stale = replace(witness,
        '(false, nil, nil), O, (sched;;aop)) : RstateOP)',
        '(false, nil, nil), O, aop) : RstateOP)')
    # Expand only the source post and its internal resource, identically except
    # that the reserved local CurTid half is absent. LINV/Atrue remain intact.
    a = source.index('Definition V293_dispatch_tail c :=')
    b = source.index('(* This frame', a)
    nohalf = source[:a] + r'''Definition V293_dispatch_tail c :=
  EX next : Modules.tid, [|V293_highest_ready tasks next|] **
    ((([|(None : option val) = None /\
      V293_bitmap_ready lo hi (V293_ready_select lo hi (V293_ready_group lo hi)) /\
      (forall p, V293_bitmap_ready lo hi p -> V293_ready_select lo hi (V293_ready_group lo hi) <= p)|] **
      (<||sched;;aop||> **
        (((V293_sched_globals unmap group rows high bt bg br bh **
          V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi)) **
          ((LINV V293_shared_li tid nil ** Atrue) ** Aie false)) **
          PV (bh, Int.zero) @ Tint8 |-> (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))))) **
      (V293_dispatch_snapshot target tp tid tasks events now next ** (Ais stack ** Acs critical))) **
      ((V293_prefix_bindings table high target tp bp bo ** V293_read_pointers tp bp 0 entries) **
        (V293_guard_cell current bcur nc ** (V293_counter_cell counter bcounter c ** frame)))).

''' + source[b:]
    changes = {
        'counter_post_two_only': (counter, witness),
        'resumed_pending_action_only': (pending, witness),
        'branch_condition_inverted_only': (branch, witness),
        'guard_false_premise_only': (false, witness),
        'witness_pending_removed_only': (source, stale),
        'reserved_half_neutralized_only': (nohalf, witness),
    }
    return {label: (c, w, *OBLIGATIONS[label]) for label, (c, w) in changes.items()}


def check_rejection(row, source, failed_rel, declaration, label):
    start = source.index(declaration)
    lo = source[:start].count('\n') + 1
    # Contracts have let-bindings and a proof block; include the entire
    # declaration through its Qed, not just the type-terminating dot.
    end = source.index('Qed.', start) + len('Qed.')
    hi = source[:end].count('\n') + 1
    match = re.search(r'File "([^"\n]+)", line (\d+), characters', row['stderr'])
    expected_file = '/checks/Contract.v' if failed_rel is None else '/' + failed_rel
    if (row['exit_code'] != 1 or not match or not lo <= int(match[2]) <= hi
            or not ('/' + match[1]).endswith(expected_file) or '\nError:' not in row['stderr']):
        raise ValueError('dispatch-tail control missed designated obligation: ' + label + ': ' + str(row))


def check(root, work, build, coqbin, run, loader, location):
    caller = loader(root, 'v293-scheduler-caller.py')
    probe = PROBE
    checks = {}
    def record(label, command, cwd):
        if label in checks:
            raise ValueError('duplicate dispatch-tail command identity: ' + label)
        row = run('dispatch_tail:' + label, command, cwd); checks[label] = row
        return row

    def compile_tree(label, core, witness, assumptions=False):
        dest = work / ('dispatch_tail_' + label)
        shutil.copytree(build / 'certiucos', dest / 'certiucos')
        (dest / 'checks').mkdir()
        flags = ['-R', str(build / 'framework'), 'CertiOS.framework',
                 '-R', str(build / 'tactics'), 'CertiOS.tactics',
                 '-R', str(dest / 'certiucos'), 'CertiOS.certiucos',
                 '-R', str(dest / 'checks'), 'DispatchTailCheck']
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
        raise ValueError('dispatch-tail proof/probe failed: ' + str(row))
    trust = loader(root, 'check-memory-trust.py'); assumptions = set()
    for part in row['stdout'].split('Axioms:')[1:]:
        assumptions |= set(trust.check_assumptions(part.split('Closed under the global context')[0], trust.FRAMEWORK_ALLOWED))
    if row['stdout'].count('Axioms:') + row['stdout'].count('Closed under the global context') != len(ROOTS):
        raise ValueError('missing dispatch-tail root assumption output')
    row = record('coqchk', [coqbin + 'coqchk', '-silent', *flags,
        *['CertiOS.' + Path(f).with_suffix('').as_posix().replace('/', '.') for f in FILES],
        'DispatchTailCheck.Contract'], dest)
    if row['exit_code']:
        raise ValueError('dispatch-tail coqchk failed: ' + str(row))
    # Same expansion as the resource-removal control, with its half restored.
    # It must compile through the independent contract before ablation credit.
    expanded, _, _, _ = variants['reserved_half_neutralized_only']
    expanded = caller.replace_once(expanded,
        '(LINV V293_shared_li tid nil ** Atrue)', 'CurLINV V293_shared_li tid')
    row, _, _ = compile_tree('expanded_half_present', expanded, witness)
    if row['exit_code']:
        raise ValueError('dispatch-tail expanded ownership baseline failed: ' + str(row))
    for label, (core, wit, failed_rel, declaration) in variants.items():
        row, _, _ = compile_tree(label, core, wit)
        failed_source = probe if failed_rel is None else (core if failed_rel == CORE else wit)
        check_rejection(row, failed_source, failed_rel, declaration, label)
        for rel in (FILES if failed_rel is None else FILES[:FILES.index(failed_rel)]):
            if checks[label + ':' + Path(rel).stem]['exit_code'] != 0:
                raise ValueError('dispatch-tail control prerequisite failed')
    return {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS, 'source_location': location,
            'root_assumptions': sorted(assumptions), 'negative_controls': CONTROLS}


def validate(root, checkpoint, checks, loader):
    import json
    inventory = json.loads((root / 'audit/repaired-source-inventory.json').read_text())
    expected = {'scope': SCOPE, 'coverage_credit': False, 'roots': ROOTS,
        'source_location': next(f for f in inventory['functions'] if f['name'] == 'OS_Sched'),
        'root_assumptions': checkpoint['root_assumptions'], 'negative_controls': CONTROLS}
    if checkpoint != expected:
        raise ValueError('dispatch-tail checkpoint scope/roots/source/controls differ')
    if not set(checkpoint['root_assumptions']) <= loader(root, 'check-memory-trust.py').FRAMEWORK_ALLOWED:
        raise ValueError('unexpected dispatch-tail root assumptions')
    for key in ['positive:' + Path(f).stem for f in FILES] + ['positive:contract', 'coqchk']:
        if checks['dispatch_tail:' + key]['exit_code'] != 0:
            raise ValueError('dispatch-tail checkpoint positive check failed')
    for rel in [*FILES, 'checks/Contract.v']:
        suffix = 'contract' if rel == 'checks/Contract.v' else Path(rel).stem
        if checks['dispatch_tail:expanded_half_present:' + suffix]['exit_code'] != 0:
            raise ValueError('dispatch-tail expanded ownership baseline missing')
    for label, (failed_rel, _) in OBLIGATIONS.items():
        fail = 'contract' if failed_rel is None else Path(failed_rel).stem
        prerequisites = FILES if failed_rel is None else FILES[:FILES.index(failed_rel)]
        for rel in prerequisites:
            if checks['dispatch_tail:' + label + ':' + Path(rel).stem]['exit_code'] != 0:
                raise ValueError('dispatch-tail control prerequisite missing')
        if checks['dispatch_tail:' + label + ':' + fail]['exit_code'] != 1:
            raise ValueError('dispatch-tail designated control missing')
    variants = mutations((root / CORE).read_text(), (root / WITNESS).read_text(),
                         loader(root, 'v293-scheduler-caller.py').replace_once)
    for label, (core, witness, failed_rel, declaration) in variants.items():
        fail = 'contract' if failed_rel is None else Path(failed_rel).stem
        text = PROBE if failed_rel is None else core if failed_rel == CORE else witness
        check_rejection(checks['dispatch_tail:' + label + ':' + fail], text, failed_rel, declaration, label)
