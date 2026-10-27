(* Full entry witness: the two halves come from ONE writable current cell.
   This empty-Inv fixture is not GoodI or a reachable initialized kernel. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPre.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCriticalWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChangeWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternalWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_switch_current_memory := V293_encoded_memory 6%positive 0 true
  (encode_val (Tptr Tvoid) (Vptr V293_idle_tid)).
Definition V293_switch_internal_memory :=
  merge (merge V293_witness_inputs V293_switch_current_memory) V293_witness_high.
Definition V293_switch_base_memory different :=
  merge V293_switch_internal_memory (V293_current_caller different).
Ltac V293_switch_outside :=
  unfold V293_switch_base_memory, V293_switch_internal_memory, V293_switch_current_memory;
  repeat rewrite map_merge_semp by reflexivity;
  first [V293_current_outside | idtac];
  repeat rewrite V293_encoded_memory_outside by (left; congruence);
  try V293_prefix_outside; reflexivity.
Ltac V293_switch_single_join k :=
  apply map_join_merge; apply map_disjoint; intros [b i];
  destruct (Pos.eq_dec b k); [subst b | ];
  first [left; V293_switch_outside | right; left; V293_switch_outside].

Lemma V293_switch_current_sat :
  V293_wstate V293_change_fixture_ge emp V293_switch_current_memory |=
  CurLINV V293_witness_li V293_idle_tid ** CurTid V293_idle_tid.
Proof.
  assert (Hfull : V293_wstate V293_change_fixture_ge emp V293_switch_current_memory |=
    GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)).
  { exists 6%positive. eapply V293_wstate_star with (m1 := emp) (m2 := V293_switch_current_memory).
    - apply map_join_comm. apply map_join_emp.
    - exists 6%positive. split; [vm_compute; reflexivity | ]. repeat split; reflexivity.
    - split; [apply V293_encoded_memory_mapsto | reflexivity]. }
  apply GV_separate_rw in Hfull.
  assert (Hlocal : V293_wstate V293_change_fixture_ge emp emp |= LINV V293_witness_li V293_idle_tid nil ** Atrue).
  { eapply V293_wstate_star with (m1 := emp) (m2 := emp); [apply map_join_emp | | exact I].
    unfold LINV, V293_witness_li.
    eapply V293_wstate_star with (m1 := emp) (m2 := emp); [apply map_join_emp | split; reflexivity | ].
    split; [apply V293_witness_li_good | split; reflexivity]. }
  assert (Hs : V293_wstate V293_change_fixture_ge emp V293_switch_current_memory |=
    (GV OSTCBCur @ (Tptr Tvoid) |-r-> (Vptr V293_idle_tid) **
      GV OSTCBCur @ (Tptr Tvoid) |-r-> (Vptr V293_idle_tid)) **
      (LINV V293_witness_li V293_idle_tid nil ** Atrue)).
  { eapply V293_wstate_star with (m1 := V293_switch_current_memory) (m2 := emp);
    [apply map_join_emp | exact Hfull | exact Hlocal]. }
  unfold CurLINV, CurTid. sep auto.
Qed.

Lemma V293_switch_internal_sat :
  V293_wstate V293_change_fixture_ge emp V293_switch_internal_memory |=
  V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
    0 16 V293_witness_li V293_idle_tid (spec_done None) ** CurTid V293_idle_tid.
Proof.
  assert (Hs : V293_wstate V293_change_fixture_ge emp V293_switch_internal_memory |=
    (<||spec_done None||> **
      V293_sched_internal_resource 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
        0 16 V293_witness_li V293_idle_tid (V293_byteval 0)) ** CurTid V293_idle_tid).
  { assert (Hmem : V293_wstate V293_change_fixture_ge emp V293_switch_internal_memory |=
      (V293_sched_inputs 1%positive 2%positive 3%positive 0 16 2 **
        (CurLINV V293_witness_li V293_idle_tid ** CurTid V293_idle_tid)) **
        PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0)).
    { eapply V293_wstate_star; [V293_switch_single_join 4%positive | | ].
      - eapply V293_wstate_star; [V293_switch_single_join 6%positive | apply V293_prefix_fixture_inputs | apply V293_switch_current_sat].
      - split; [apply V293_encoded_memory_mapsto | reflexivity]. }
    assert (Hglobals : V293_wstate V293_change_fixture_ge emp emp |=
      V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive).
    { apply V293_prefix_fixture_globals; vm_compute; reflexivity. }
    assert (Hboth : V293_wstate V293_change_fixture_ge emp V293_switch_internal_memory |=
      (V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive) **
      ((V293_sched_inputs 1%positive 2%positive 3%positive 0 16 2 **
        (CurLINV V293_witness_li V293_idle_tid ** CurTid V293_idle_tid)) **
        PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0))).
    { eapply V293_wstate_star with (m1 := emp) (m2 := V293_switch_internal_memory);
      [apply map_join_comm; apply map_join_emp | exact Hglobals | exact Hmem]. }
    unfold V293_sched_internal_resource.
    apply astar_l_aop'_intro with (aop := spec_done None) in Hboth; [ | reflexivity].
    apply astar_l_aie_intro with (i := false) in Hboth; [ | reflexivity].
    sep auto. }
  eapply astar_mono; [apply V293_sched_insert_bounds | intros s H; exact H | exact Hs].
  split; [lia | ]. split; [lia | ]. exists 12. vm_compute; intuition lia.
Qed.

Lemma V293_switch_pre_base : forall different,
  V293_target_wstate V293_change_fixture_ge emp (V293_switch_base_memory different) (V293_current_abs different) |=
    (V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
      0 16 V293_witness_li V293_idle_tid (spec_done None) ** CurTid V293_idle_tid) **
    (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive
      (V293_current_mode_entries different) (V293_current_mode_tasks different) Aemp **
      V293_prefix_output Tvoid 10%positive Vnull).
Proof.
  intro different. eapply V293_target_wstate_star with (o1 := emp) (o2 := V293_current_abs different).
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 8%positive); [subst b; left; V293_switch_outside | ].
    destruct (Pos.eq_dec b 10%positive); [subst b; left; V293_switch_outside | ].
    right; left. V293_current_outside.
  - apply map_join_comm. apply map_join_emp.
  - apply V293_switch_internal_sat.
  - apply V293_current_caller_sat.
Qed.

Theorem V293_OSSched_switch_precondition_witness : forall different ni nl c,
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
        (V293_guard_cell 108%Z 11%positive ni ** (V293_guard_cell 109%Z 12%positive nl ** (CurTid V293_idle_tid ** Aemp)))) **
      (V293_prefix_output Tvoid 10%positive Vnull ** V293_counter_cell 111%Z 14%positive c)).
Proof.

  intros different ni nl c Hni Hnl.
  exists (V293_target_wstate V293_change_fixture_ge emp
    (merge (V293_switch_base_memory different) (V293_change_all_extra ni nl (V293_current_mode_priority different) c))
      (V293_current_abs different)).
  destruct (V293_current_mode_relations different) as [Hb [Ht Hcur]].
  split; [exact Hb | ]. split; [exact Ht | ]. split; [exact Hcur | ]. split.
  - destruct different; vm_compute; intuition congruence.
  - assert (Hs : V293_target_wstate V293_change_fixture_ge emp
      (merge (V293_switch_base_memory different) (V293_change_all_extra ni nl (V293_current_mode_priority different) c))
        (V293_current_abs different) |=
      ((V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
        0 16 V293_witness_li V293_idle_tid (spec_done None) ** CurTid V293_idle_tid) **
        (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive
          (V293_current_mode_entries different) (V293_current_mode_tasks different) Aemp **
          V293_prefix_output Tvoid 10%positive Vnull)) **
      ((V293_guard_cell 108%Z 11%positive ni ** V293_guard_cell 109%Z 12%positive nl) **
        (V293_guard_cell 110%Z 13%positive (V293_current_mode_priority different) ** V293_counter_cell 111%Z 14%positive c))).
    { eapply V293_target_wstate_star with (o1 := V293_current_abs different) (o2 := emp).
      - apply map_join_merge. apply map_disjoint. intros [b i].
        destruct (Pos.eq_dec b 11%positive); [subst b; left; V293_switch_outside | ].
        destruct (Pos.eq_dec b 12%positive); [subst b; left; V293_switch_outside | ].
        destruct (Pos.eq_dec b 13%positive); [subst b; left; V293_switch_outside | ].
        destruct (Pos.eq_dec b 14%positive); [subst b; left; V293_switch_outside | ].
        right; left. V293_change_outside.
      - apply map_join_emp.
      - apply V293_switch_pre_base.
      - apply V293_change_all_extra_witness. }
    apply V293_critical_fixture_attach in Hs.
    unfold V293_prefix_frame in *. sep auto.
Qed.
