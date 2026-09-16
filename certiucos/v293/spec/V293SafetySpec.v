Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Require Import CertiOS.certiucos.v293.model.V293PendModel.
Require Import CertiOS.certiucos.v293.model.V293MutexPriorityModel.
Require Import CertiOS.certiucos.v293.model.V293TaskDeleteModel.

Definition V293_timeout_suspend_resume_safety : Prop :=
  forall s,
    v293_ready (V293_resume (V293_suspend (V293_tick_timeout s))) = true /\
    v293_pend_result (V293_resume (V293_suspend (V293_tick_timeout s))) =
      V293PendTimeout.

Definition V293_nested_mutex_restoration_safety : Prop :=
  forall base remaining,
    V293_restore_priority base remaining = V293_effective_priority base remaining.

Definition V293_locked_self_delete_safety : Prop :=
  forall s,
    V293_execution_ownership_safe s ->
    v293_lock_nesting s <> 0 ->
    fst (V293_delete_current s) = V293DeleteLockedCurrent /\
    V293_execution_ownership_safe (snd (V293_delete_current s)).
