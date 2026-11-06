(* Literal interfaces for the frozen two-write fragment, NOT full API credit. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import Coq.Lists.List.
Local Open Scope nat_scope.
Definition checked_writable (M : mem) b i n :=
  forall k, k < n -> exists v, get M (b,(i+Z.of_nat k)%Z) = Some (true,v).
Definition checked_table_loads tp M b (entries : list val) :=
  forall p, p < 13 -> load (Tptr tp) M (b,(4*Z.of_nat p)%Z) = Some (nth p entries Vnull).
Definition checked_stores : forall tp M b old new next,
  old <> new ->
  checked_writable M b (4*Z.of_nat old)%Z 4 ->
  checked_writable M b (4*Z.of_nat new)%Z 4 ->
  exists M1 M2,
    store (Tptr tp) M (b,(4*Z.of_nat old)%Z) Vnull = Some M1 /\
    store (Tptr tp) M1 (b,(4*Z.of_nat new)%Z) (Vptr next) = Some M2 /\
    load (Tptr tp) M2 (b,(4*Z.of_nat old)%Z) = Some Vnull /\
    load (Tptr tp) M2 (b,(4*Z.of_nat new)%Z) = Some (Vptr next) /\
    (forall other j,
      (other <> b \/ (j < 4*Z.of_nat old)%Z \/ (4*Z.of_nat old+4 <= j)%Z) ->
      (other <> b \/ (j < 4*Z.of_nat new)%Z \/ (4*Z.of_nat new+4 <= j)%Z) ->
      get M2 (other,j) = get M (other,j)) :=
  V293_task_prio_rekey_stores.

Definition checked_execution : forall P ks ge le M table oldprio newprio ptcb tp b bo bn bc old new next,
  old < 13 -> new < 13 -> old <> new ->
  get le table = None -> get ge table = Some (b,Tarray (Tptr tp) 13) ->
  get le oldprio = Some (bo,Tint8) -> get le newprio = Some (bn,Tint8) ->
  get le ptcb = Some (bc,Tptr tp) -> b <> bo -> b <> bn -> b <> bc ->
  load Tint8 M (bo,0%Z) = Some (V293_byteval old) ->
  load Tint8 M (bn,0%Z) = Some (V293_byteval new) ->
  load (Tptr tp) M (bc,0%Z) = Some (Vptr next) ->
  checked_writable M b (4*Z.of_nat old)%Z 4 ->
  checked_writable M b (4*Z.of_nat new)%Z 4 ->
  exists M1 M2,
    store (Tptr tp) M (b,(4*Z.of_nat old)%Z) Vnull = Some M1 /\
    store (Tptr tp) M1 (b,(4*Z.of_nat new)%Z) (Vptr next) = Some M2 /\
    cstepstar P (curs (sseq (sassign (earrayelem (evar table) (evar oldprio)) enull)
         (sassign (earrayelem (evar table) (evar newprio)) (evar ptcb))),(kenil,ks)) (ge,le,M)
      (curs (sskip None),(kenil,ks)) (ge,le,M2) /\
    load (Tptr tp) M2 (b,(4*Z.of_nat old)%Z) = Some Vnull /\
    load (Tptr tp) M2 (b,(4*Z.of_nat new)%Z) = Some (Vptr next) /\
    (forall other j,
      (other <> b \/ (j < 4*Z.of_nat old)%Z \/ (4*Z.of_nat old+4 <= j)%Z) ->
      (other <> b \/ (j < 4*Z.of_nat new)%Z \/ (4*Z.of_nat new+4 <= j)%Z) ->
      get M2 (other,j) = get M (other,j)) :=
  V293_OSTaskChangePrio_table_execution.

Definition checked_table : forall tp M M1 M2 b entries old new next,
  length entries = 13 -> old < 13 -> new < 13 ->
  checked_table_loads tp M b entries ->
  store (Tptr tp) M (b,(4*Z.of_nat old)%Z) Vnull = Some M1 ->
  store (Tptr tp) M1 (b,(4*Z.of_nat new)%Z) (Vptr next) = Some M2 ->
  checked_table_loads tp M2 b
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr next)) :=
  V293_task_prio_rekey_table_model.

Definition checked_choice : forall tp M M1 M2 b entries old new next lo hi tasks,
  length entries = 13 -> old < 13 -> new < 13 -> old <> new ->
  checked_table_loads tp M b entries ->
  store (Tptr tp) M (b,(4*Z.of_nat old)%Z) Vnull = Some M1 ->
  store (Tptr tp) M1 (b,(4*Z.of_nat new)%Z) (Vptr next) = Some M2 ->
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks ->
  V293_priority_table
    (update_nth_val new (update_nth_val old entries Vnull) (Vptr next)) tasks ->
  load (Tptr tp) M2 (b,(4*Z.of_nat old)%Z) = Some Vnull /\
  V293_ready_select lo hi (V293_ready_group lo hi) <> old :=
  V293_task_prio_rekey_ready_choice.

Definition checked_alias : forall tp M b p next,
  checked_writable M b (4*Z.of_nat p)%Z 4 ->
  exists M1 M2,
    store (Tptr tp) M (b,(4*Z.of_nat p)%Z) Vnull = Some M1 /\
    store (Tptr tp) M1 (b,(4*Z.of_nat p)%Z) (Vptr next) = Some M2 /\
    load (Tptr tp) M2 (b,(4*Z.of_nat p)%Z) = Some (Vptr next) /\
    load (Tptr tp) M2 (b,(4*Z.of_nat p)%Z) <> Some Vnull :=
  V293_task_prio_rekey_alias_control.

Definition checked_fixture : forall P ks,
  load (Tptr Tvoid) V293_rekey_fixture_memory (20%positive,32%Z) =
    Some (Vptr (15%positive,Int.zero)) /\
  load (Tptr Tvoid) V293_rekey_fixture_memory (20%positive,24%Z) = Some Vnull /\
  exists M2,
    cstepstar P
      (curs (sseq (sassign (earrayelem (evar 200%Z) (evar 201%Z)) enull)
         (sassign (earrayelem (evar 200%Z) (evar 202%Z)) (evar 203%Z))),(kenil,ks))
      (V293_rekey_fixture_ge,V293_rekey_fixture_le,V293_rekey_fixture_memory)
      (curs (sskip None),(kenil,ks)) (V293_rekey_fixture_ge,V293_rekey_fixture_le,M2) /\
    load (Tptr Tvoid) M2 (20%positive,32%Z) = Some Vnull /\
    load (Tptr Tvoid) M2 (20%positive,24%Z) = Some (Vptr (15%positive,Int.zero)) :=
  V293_task_prio_rekey_fixture_execution.

Print Assumptions checked_stores.
Print Assumptions checked_execution.
Print Assumptions checked_table.
Print Assumptions checked_choice.
Print Assumptions checked_alias.
Print Assumptions checked_fixture.
