(* Joint satisfiability fixture, not an implementation of the kernel invariant. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChangeWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_critical_fixture_inv : Inv.
Proof.
  intro k. refine (@mkinvasrt Aemp Logic.I _). split.
  - unfold precise. intros s M1 M2 o1 o2 H1 H2 M o Hm1 Hm2 Ho1 Ho2.
    destruct s as [[[[[[ge le] sm] sr] aux] O] op].
    change (M1 = emp /\ o1 = emp) in H1. change (M2 = emp /\ o2 = emp) in H2.
    intuition congruence.
  - unfold inv_isr_prop. repeat split; intros; destruct s as [[[[[[ge le] M] sr] [[ie stack] critical]] O] op]; exact H.
Defined.
Lemma V293_critical_fixture_starinv : forall ge le low n,
  V293_wstate ge le emp |= starinv_isr V293_critical_fixture_inv low n.
Proof.
  intros ge le low n. revert low. induction n; intro low.
  - change (V293_wstate ge le emp |= EX r : isr,
      ([|r low = true|] //\\ Aisr r) \\// ([|r low = false|] //\\ Aisr r) ** Aemp).
    exists (fun _ : hid => false). right.
    apply astar_r_aemp_intro. repeat split; reflexivity.
  - change (V293_wstate ge le emp |=
      (EX r : isr, ([|r low = true|] //\\ Aisr r) \\// ([|r low = false|] //\\ Aisr r) ** Aemp) **
      starinv_isr V293_critical_fixture_inv (S low) n).
    eapply V293_wstate_star with (m1 := emp) (m2 := emp).
    + apply map_join_emp.
    + exists (fun _ : hid => false). right.
      apply astar_r_aemp_intro. repeat split; reflexivity.
    + apply IHn.
Qed.
Lemma V293_critical_fixture_sat : forall ge le,
  V293_wstate ge le emp |= V293_sched_critical V293_critical_fixture_inv nil nil.
Proof.
  intros. unfold V293_sched_critical, SWINV.
  eapply V293_wstate_star with (m1 := emp) (m2 := emp); [apply map_join_emp | | ].
  - eapply V293_wstate_star with (m1 := emp) (m2 := emp); [apply map_join_emp | | ].
    + eapply V293_wstate_star with (m1 := emp) (m2 := emp); [apply map_join_emp | | ].
      * exists (fun _ : hid => false). repeat split; try reflexivity; auto.
      * repeat split; reflexivity.
    + exists INUM. eapply V293_wstate_star with (m1 := emp) (m2 := emp); [apply map_join_emp | | ].
      * repeat split; reflexivity.
      * apply V293_critical_fixture_starinv.
  - eapply V293_wstate_star with (m1 := emp) (m2 := emp); [apply map_join_emp | repeat split; reflexivity | repeat split; reflexivity].
Qed.

Lemma V293_critical_fixture_attach : forall P ge le M O,
  V293_target_wstate ge le M O |= P ->
  V293_target_wstate ge le M O |= P ** V293_sched_critical V293_critical_fixture_inv nil nil.
Proof.
  intros P ge le M O Hs. eapply V293_target_wstate_star with (m2 := emp) (o2 := emp).
  - apply map_join_emp.
  - apply map_join_emp.
  - exact Hs.
  - apply V293_critical_fixture_sat.
Qed.

Theorem V293_OSSched_critical_precondition_witness : forall different ni nl c,
  ni < 256 -> nl < 256 -> exists s,
  V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
  V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
  V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
  (V293_ready_select 0 16 (V293_ready_group 0 16) <> V293_current_mode_priority different <-> different = true) /\
  s |= (V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
    0 16 V293_witness_li V293_idle_tid (spec_done None) **
      V293_sched_critical V293_critical_fixture_inv nil nil) **
    (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive
      (V293_current_mode_entries different) (V293_current_mode_tasks different)
      (V293_guard_cell 110%Z 13%positive (V293_current_mode_priority different) **
        (V293_guard_cell 108%Z 11%positive ni ** (V293_guard_cell 109%Z 12%positive nl ** Aemp))) **
      (V293_prefix_output Tvoid 10%positive Vnull ** V293_counter_cell 111%Z 14%positive c)).
Proof.

  intros different ni nl c Hni Hnl.
  exists (V293_target_wstate V293_change_fixture_ge emp
    (merge (V293_current_memory different) (V293_change_all_extra ni nl (V293_current_mode_priority different) c))
      (V293_current_abs different)).
  destruct (V293_current_mode_relations different) as [Hb [Ht Hcur]].
  split; [exact Hb | ]. split; [exact Ht | ]. split; [exact Hcur | ]. split.
  - destruct different; vm_compute; intuition congruence.
  - assert (Hs : V293_target_wstate V293_change_fixture_ge emp
      (merge (V293_current_memory different) (V293_change_all_extra ni nl (V293_current_mode_priority different) c))
        (V293_current_abs different) |=
      (V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
        0 16 V293_witness_li V293_idle_tid (spec_done None) **
        (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive
          (V293_current_mode_entries different) (V293_current_mode_tasks different) Aemp **
          V293_prefix_output Tvoid 10%positive Vnull)) **
      ((V293_guard_cell 108%Z 11%positive ni ** V293_guard_cell 109%Z 12%positive nl) **
        (V293_guard_cell 110%Z 13%positive (V293_current_mode_priority different) ** V293_counter_cell 111%Z 14%positive c))).
    { eapply V293_target_wstate_star with (o1 := V293_current_abs different) (o2 := emp).
      - apply map_join_merge. apply map_disjoint. intros [b i].
        destruct (Pos.eq_dec b 11%positive); [subst b; left; V293_current_outside | ].
        destruct (Pos.eq_dec b 12%positive); [subst b; left; V293_current_outside | ].
        destruct (Pos.eq_dec b 13%positive); [subst b; left; V293_current_outside | ].
        destruct (Pos.eq_dec b 14%positive); [subst b; left; V293_current_outside | ].
        right; left. V293_change_outside.
      - apply map_join_emp.
      - apply V293_current_pre_base.
      - apply V293_change_all_extra_witness. }
    apply V293_critical_fixture_attach in Hs.
    unfold V293_prefix_frame in *. sep auto.
Qed.
