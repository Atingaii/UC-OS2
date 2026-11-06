(* Literal independent contracts, not signatures extracted from the candidate. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchPriorityBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import Coq.Lists.List.
Local Open Scope nat_scope.

Definition checked_coherence (b : block) (o : taskst) (O : osabst) :=
  exists tasks t p,
    get O abstcblsid = Some (abstcblist tasks) /\
    get O curtid = Some (oscurt t) /\
    load Tint8 (get_mem (get_smem o)) (b, 0%Z) = Some (V293_byteval p) /\
    (p < 13 /\ exists status message,
      get tasks t = Some (Int.repr (Z.of_nat p), status, message)).
Definition checked_before :
  checked_coherence 2%positive
    (V293_priority_boundary_task V293_priority_boundary_memory) V293_priority_boundary_abs :=
  V293_priority_boundary_before.
Definition checked_pointer_store :
  get V293_priority_boundary_ge OSTCBCur = Some (1%positive, Tptr Tvoid) /\
  load (Tptr Tvoid) V293_priority_boundary_memory (1%positive, 0%Z) = Some (Vptr V293_idle_tid) /\
  store (Tptr Tvoid) V293_priority_boundary_memory (1%positive, 0%Z) (Vptr V293_current_next) =
    Some V293_priority_boundary_pointer_memory /\
  load (Tptr Tvoid) V293_priority_boundary_pointer_memory (1%positive, 0%Z) = Some (Vptr V293_current_next) /\
  load Tint8 V293_priority_boundary_pointer_memory (2%positive, 0%Z) = Some (V293_byteval 4) /\
  get V293_priority_boundary_next_abs curtid = Some (oscurt V293_current_next) /\
  get V293_priority_boundary_next_abs abstcblsid = Some (abstcblist V293_current_tasks) /\
  indom V293_current_tasks V293_idle_tid /\
  V293_highest_ready V293_current_tasks V293_current_next :=
  V293_priority_boundary_pointer_store.
Definition checked_pointer_only_breaks :
  ~ checked_coherence 2%positive
    (V293_priority_boundary_task V293_priority_boundary_pointer_memory) V293_priority_boundary_next_abs :=
  V293_priority_boundary_pointer_only_breaks.
Definition checked_explicit_sync :
  store Tint8 V293_priority_boundary_pointer_memory (2%positive, 0%Z) (V293_byteval 12) =
    Some V293_priority_boundary_synchronized_memory /\
  checked_coherence 2%positive
    (V293_priority_boundary_task V293_priority_boundary_synchronized_memory) V293_priority_boundary_next_abs :=
  V293_priority_boundary_explicit_sync.
Definition checked_GoodI_obstruction : forall (I : Inv) (li : LocalInv),
  (V293_priority_boundary_task V293_priority_boundary_memory,
    V293_priority_boundary_abs, spec_done None) |= SWINVt I V293_idle_tid ->
  (forall o O op t, (o, O, op) |= SWINVt I t -> checked_coherence 2%positive o O) ->
  ~ GoodI I V293_scheduler li :=
  V293_priority_boundary_GoodI_obstruction.

Print Assumptions checked_before.
Print Assumptions checked_pointer_store.
Print Assumptions checked_pointer_only_breaks.
Print Assumptions checked_explicit_sync.
Print Assumptions checked_GoodI_obstruction.
