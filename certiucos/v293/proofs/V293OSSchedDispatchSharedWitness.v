(* Reuse the existing full source-prefix fixture, move its SAME target cell
   into dispatch_inv. This fixture uses spec_done None and empty stacks. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSharedWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternalWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Theorem V293_dispatch_prefix_precondition_witness : forall different events now,
  exists s,
  V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
  V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
  V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
  (V293_ready_select 0 16 (V293_ready_group 0 16) <> V293_current_mode_priority different <-> different = true) /\
  s |= V293_dispatch_prefix_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
    0 16 V293_witness_li V293_idle_tid (spec_done None)
    106%Z 107%Z Tvoid 8%positive 10%positive
    (V293_current_mode_entries different) (V293_current_mode_tasks different) events now Aemp nil nil.
Proof.
  intros different events now.
  destruct (V293_OSSched_shared_precondition_witness different events now)
    as (s & Hb & Ht & Hcur & Hd & Hs).
  exists s. split; [exact Hb | ]. split; [exact Ht | ].
  split; [exact Hcur | ]. split; [exact Hd | ].
  unfold V293_shared_prefix_pre in Hs. unfold V293_dispatch_prefix_pre.
  eapply astar_mono in Hs.
  2: { apply astar_mono; [intros st H; exact H | apply astar_mono;
    [apply V293_shared_snapshot_open | intros st H; exact H]]. }
  2: { intros st H; exact H. }
  assert (HP : s |= (V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive **
    V293_prefix_output Tvoid 10%positive Vnull) **
    (V293_shared_flags ** ((CurTid V293_idle_tid ** V293_shared_fields V293_idle_tid
      (V293_current_mode_tasks different) events now) **
      (V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
        0 16 V293_witness_li V293_idle_tid (spec_done None) **
        ((Ais nil ** Acs nil) ** (V293_read_pointers Tvoid 8%positive 0
          (V293_current_mode_entries different) ** Aemp)))))) by (sep auto).
  eapply astar_mono in HP; [ | apply V293_dispatch_output_named | intros st H; exact H].
  assert (HK : s |= (V293_shared_flags ** ((CurTid V293_idle_tid ** V293_shared_fields V293_idle_tid
    (V293_current_mode_tasks different) events now) ** V293_dispatch_cell 107%Z Tvoid)) **
    (V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
      0 16 V293_witness_li V293_idle_tid (spec_done None) **
      ((Ais nil ** Acs nil) ** ((V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive **
        V293_read_pointers Tvoid 8%positive 0 (V293_current_mode_entries different)) ** Aemp)))).
  { unfold V293_dispatch_cell. clear Hs. sep auto. }
  eapply astar_mono in HK; [ | apply V293_dispatch_entry_close | intros st H; exact H].
  clear Hs HP. sep auto.
Qed.
