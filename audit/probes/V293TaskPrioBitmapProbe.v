(* Independent literal operation shapes; no post-bitmap oracle. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import Coq.Lists.List.
Local Open Scope nat_scope.

Definition checked_rows (lo hi old new : nat) : nat * nat :=
  let cleared := if old <? 8 then (Nat.clearbit lo old,hi)
                 else (lo,Nat.clearbit hi (old-8)) in
  if new <? 8 then (Nat.setbit (fst cleared) new,snd cleared)
  else (fst cleared,Nat.setbit (snd cleared) (new-8)).
Definition checked_group (lo hi old new : nat) : nat :=
  let cleared := if old <? 8 then (Nat.clearbit lo old,hi)
                 else (lo,Nat.clearbit hi (old-8)) in
  Nat.setbit
    (if (if old <? 8 then fst cleared else snd cleared) =? 0
     then Nat.clearbit (V293_ready_group lo hi) (if old <? 8 then 0 else 1)
     else V293_ready_group lo hi) (if new <? 8 then 0 else 1).

Definition checked_byte : forall row bit, row < 256 -> bit < 8 ->
  Nat.clearbit row bit < 256 /\ Nat.setbit row bit < 256 /\
  Int.and (Int.repr (Z.of_nat row))
    (Int.modu (Int.not (Int.shl Int.one (Int.repr (Z.of_nat bit)))) (Int.repr 256)) =
    Int.repr (Z.of_nat (Nat.clearbit row bit)) /\
  Int.or (Int.repr (Z.of_nat row)) (Int.shl Int.one (Int.repr (Z.of_nat bit))) =
    Int.repr (Z.of_nat (Nat.setbit row bit)) := V293_rekey_byte_arithmetic.

Definition checked_expr : forall ge le M row mask r bit,
  r < 256 -> bit < 8 ->
  evaltype row (ge,le,M) = Some Tint8 -> evaltype mask (ge,le,M) = Some Tint8 ->
  evalval row (ge,le,M) = Some (V293_byteval r) ->
  evalval mask (ge,le,M) = Some (Vint32 (Int.shl Int.one (Int.repr (Z.of_nat bit)))) ->
  evaltype (ecast (ebinop obitand (ecast row Tint32)
    (ecast (ecast (eunop negation (ecast mask Tint32)) Tint8) Tint32)) Tint8)
    (ge,le,M) = Some Tint8 /\
  evaltype (ecast (ebinop obitor (ecast row Tint32) (ecast mask Tint32)) Tint8)
    (ge,le,M) = Some Tint8 /\
  evalval (ecast (ebinop obitand (ecast row Tint32)
    (ecast (ecast (eunop negation (ecast mask Tint32)) Tint8) Tint32)) Tint8)
    (ge,le,M) = Some (V293_byteval (Nat.clearbit r bit)) /\
  evalval (ecast (ebinop obitor (ecast row Tint32) (ecast mask Tint32)) Tint8)
    (ge,le,M) = Some (V293_byteval (Nat.setbit r bit)) := V293_task_prio_byte_expr_eval.

Definition checked_membership : forall lo hi old new p,
  old < 13 -> new < 13 -> p < 13 ->
  (V293_bitmap_ready (fst (checked_rows lo hi old new)) (snd (checked_rows lo hi old new)) p <->
   p = new \/ (V293_bitmap_ready lo hi p /\ p <> old)) := V293_ready_rekey_membership.
Definition checked_group_correct : forall lo hi old new,
  checked_group lo hi old new = V293_ready_group
    (fst (checked_rows lo hi old new)) (snd (checked_rows lo hi old new)) :=
  V293_ready_rekey_group_correct.
Definition checked_high_bits : forall lo hi old new bit,
  old < 13 -> new < 13 -> 5 <= bit ->
  Nat.testbit (snd (checked_rows lo hi old new)) bit = Nat.testbit hi bit :=
  V293_ready_rekey_high_bits.
Definition checked_bounds : forall lo hi old new,
  lo < 256 -> hi < 256 -> old < 13 -> new < 13 ->
  fst (checked_rows lo hi old new) < 256 /\ snd (checked_rows lo hi old new) < 256 :=
  V293_ready_rekey_bounds.

Definition checked_preservation :
  forall tp M M1 M2 b entries tasks next old new lo hi message,
  old < 13 -> new < 13 -> old <> new -> lo < 256 -> hi < 256 ->
  V293_priority_table entries tasks -> V293_bitmap_tasks lo hi tasks ->
  get tasks next = Some (Int.repr (Z.of_nat old),rdy,message) ->
  nth new entries Vnull = Vnull -> V293_table_loads tp M b entries ->
  store (Tptr tp) M (b,(4*Z.of_nat old)%Z) Vnull = Some M1 ->
  store (Tptr tp) M1 (b,(4*Z.of_nat new)%Z) (Vptr next) = Some M2 ->
  let rows := checked_rows lo hi old new in
  let tasks' := set tasks next (Int.repr (Z.of_nat new),rdy,message) in
  let entries' := update_nth_val new (update_nth_val old entries Vnull) (Vptr next) in
  V293_bitmap_ready lo hi old /\ fst rows < 256 /\ snd rows < 256 /\
  checked_group lo hi old new = V293_ready_group (fst rows) (snd rows) /\
  V293_bitmap_tasks (fst rows) (snd rows) tasks' /\
  V293_priority_table entries' tasks' /\ V293_table_loads tp M2 b entries' /\
  load (Tptr tp) M2 (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  exists chosen msg,
    get tasks' chosen = Some
      (Int.repr (Z.of_nat (V293_ready_select (fst rows) (snd rows)
        (checked_group lo hi old new))),rdy,msg) /\
    load (Tptr tp) M2 (b,(4*Z.of_nat (V293_ready_select (fst rows) (snd rows)
      (checked_group lo hi old new)))%Z) = Some (Vptr chosen) /\
    V293_highest_ready tasks' chosen /\
    V293_ready_select (fst rows) (snd rows) (checked_group lo hi old new) <> old :=
  V293_task_prio_rekey_ready_correspondence.

Definition checked_controls :
  checked_rows 0 1 8 6 = (64,0) /\ checked_group 0 1 8 6 = 1 /\
  checked_rows 0 1 8 10 = (0,4) /\ checked_group 0 1 8 10 = 2 /\
  checked_rows 20 0 2 6 = (80,0) /\ checked_group 20 0 2 6 = 1 /\
  checked_rows 0 129 8 6 = (64,128) /\ checked_group 0 129 8 6 = 3 :=
  V293_ready_rekey_row_controls.

Print Assumptions checked_byte.
Print Assumptions checked_expr.
Print Assumptions checked_membership.
Print Assumptions checked_group_correct.
Print Assumptions checked_high_bits.
Print Assumptions checked_bounds.
Print Assumptions checked_preservation.
Print Assumptions checked_controls.
