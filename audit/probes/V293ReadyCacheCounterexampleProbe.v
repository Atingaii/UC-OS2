(* Literal actual-ready counterexample interfaces, not full C/port evidence. *)
Require Import CertiOS.certiucos.v293.proofs.V293SwitchPriorityBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageConnectWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Definition checked_coherent b (o : taskst) (O : osabst) : Prop :=
  exists tasks current nc,
    get O abstcblsid = Some (abstcblist tasks) /\
    get O curtid = Some (oscurt current) /\
    load Tint8 (get_mem (get_smem o)) (b, 0%Z) = Some (V293_byteval nc) /\
    V293_current_task tasks current nc.
Definition checked_ready :=
  V293_ready_inv 1%positive 2%positive 3%positive 4%positive 8%positive Tvoid
    [((13%positive, 0%Z), Tint32); ((12%positive, 0%Z), Tint8)] 107%Z.
Definition checked_task (M : mem) : taskst :=
  (V293_conditional_fixture_ge, emp, M, (fun _ => false), (false, nil, nil)).
Definition checked_abs :=
  V293_shared_fixture_abs V293_idle_tid V293_current_tasks (emp : EcbMod.map) Int.zero.

Definition checked_entry :
  (checked_task V293_ready_boundary_memory, checked_abs, spec_done None) |=
    SWINVt checked_ready V293_idle_tid /\
  load Tint8 V293_ready_boundary_memory (12%positive, 0%Z) = Some (V293_byteval 4) /\
  checked_coherent 12%positive (checked_task V293_ready_boundary_memory) checked_abs :=
  V293_ready_boundary_entry.

Definition checked_pointer_only : exists M',
  store (Tptr Tvoid) V293_ready_boundary_memory (6%positive, 0%Z) (Vptr V293_current_next) = Some M' /\
  (checked_task M', set checked_abs curtid (oscurt V293_current_next), spec_done None) |=
    SWINVt checked_ready V293_current_next /\
  load Tint8 M' (12%positive, 0%Z) = Some (V293_byteval 4) /\
  V293_highest_ready V293_current_tasks V293_current_next /\
  indom V293_current_tasks V293_idle_tid /\
  ~ checked_coherent 12%positive (checked_task M') (set checked_abs curtid (oscurt V293_current_next)) :=
  V293_ready_boundary_pointer_only.

Definition checked_no_entailment :
  ~ (forall o O op t, (o, O, op) |= SWINVt checked_ready t -> checked_coherent 12%positive o O) :=
  V293_ready_boundary_no_cache_entailment.

Print Assumptions checked_entry.
Print Assumptions checked_pointer_only.
Print Assumptions checked_no_entailment.
