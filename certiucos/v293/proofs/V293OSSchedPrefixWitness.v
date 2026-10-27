(* A concrete spatial witness for the complete two-statement precondition.
   All arrays, current-task storage and both writable outputs coexist. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternalWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_prefix_fixture_ge : env :=
  set (set V293_witness_ge 106%Z (8%positive, Tarray (Tptr Tvoid) 13))
    107%Z (10%positive, Tptr Tvoid).
Definition V293_prefix_fixture_output :=
  V293_encoded_memory 10%positive 0 true (encode_val (Tptr Tvoid) Vnull).
Definition V293_prefix_fixture_internal :=
  merge (merge V293_witness_inputs V293_witness_current) V293_witness_high.
Definition V293_prefix_fixture_caller := merge V293_target_fixture_table V293_prefix_fixture_output.
Definition V293_prefix_fixture_memory := merge V293_prefix_fixture_internal V293_prefix_fixture_caller.
Definition V293_prefix_fixture_state := V293_target_wstate V293_prefix_fixture_ge emp
  V293_prefix_fixture_memory V293_target_fixture_abs.

Ltac V293_prefix_outside :=
  unfold V293_prefix_fixture_internal, V293_prefix_fixture_caller, V293_prefix_fixture_output,
    V293_target_fixture_table, V293_witness_inputs, V293_witness_table,
    V293_witness_rows, V293_witness_group, V293_witness_current, V293_witness_high, V293_nat_memory;
  repeat rewrite map_merge_semp by reflexivity;
  repeat first [rewrite V293_encoded_memory_outside by (left; congruence) |
                rewrite V293_pointer_memory_outside by (left; congruence)]; reflexivity.

Ltac V293_prefix_single_join k :=
  apply map_join_merge; apply map_disjoint; intros [b i];
  destruct (Pos.eq_dec b k); [subst b | ];
  first [left; V293_prefix_outside | right; left; V293_prefix_outside].

Lemma V293_prefix_fixture_inputs :
  V293_wstate V293_prefix_fixture_ge emp V293_witness_inputs |=
    V293_sched_inputs 1%positive 2%positive 3%positive 0 16 2.
Proof.
  eapply V293_wstate_star; [V293_prefix_single_join 1%positive | apply V293_read_bytes_witness | ].
  eapply V293_wstate_star; [V293_prefix_single_join 3%positive | apply V293_read_bytes_witness | ].
  split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.

Lemma V293_prefix_fixture_current :
  V293_wstate V293_prefix_fixture_ge emp V293_witness_current |=
    CurLINV V293_witness_li V293_idle_tid.
Proof.
  exists (nil : list logicvar).
  eapply V293_wstate_star with (m1 := V293_witness_current) (m2 := emp).
  - apply map_join_emp.
  - exists Tvoid. exists 6%positive.
    eapply V293_wstate_star with (m1 := emp) (m2 := V293_witness_current).
    + apply map_join_comm. apply map_join_emp.
    + exists 6%positive. split; [vm_compute; reflexivity | ]. split; [reflexivity | split; reflexivity].
    + split; [apply V293_encoded_memory_mapsto | reflexivity].
  - eapply V293_wstate_star with (m1 := emp) (m2 := emp).
    + apply map_join_emp.
    + unfold LINV, V293_witness_li.
      eapply V293_wstate_star with (m1 := emp) (m2 := emp).
      * apply map_join_emp.
      * split; reflexivity.
      * split; [apply V293_witness_li_good | split; reflexivity].
    + exact I.
Qed.

Lemma V293_prefix_fixture_globals :
  V293_wstate V293_prefix_fixture_ge emp emp |=
    V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive.
Proof.
  unfold V293_sched_globals. repeat split.
  - exists 1%positive. vm_compute; repeat split; reflexivity.
  - exists 2%positive. vm_compute; repeat split; reflexivity.
  - exists 3%positive. vm_compute; repeat split; reflexivity.
  - exists 4%positive. vm_compute; repeat split; reflexivity.
Qed.

Lemma V293_prefix_fixture_internal_sat :
  V293_wstate V293_prefix_fixture_ge emp V293_prefix_fixture_internal |=
    V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
      0 16 V293_witness_li V293_idle_tid (spec_done None).
Proof.
  apply V293_sched_insert_bounds with (hold := V293_byteval 0).
  - split; [lia | ]. split; [lia | ]. exists 12. vm_compute; intuition lia.
  - eapply V293_wstate_star with (m1 := emp) (m2 := V293_prefix_fixture_internal).
    + apply map_join_comm. apply map_join_emp.
    + split; [reflexivity | split; reflexivity].
    + eapply V293_wstate_star; [V293_prefix_single_join 4%positive | | ].
      * eapply V293_wstate_star; [V293_prefix_single_join 6%positive | | ].
        -- eapply V293_wstate_star with (m1 := emp) (m2 := V293_witness_inputs).
           ++ apply map_join_comm. apply map_join_emp.
           ++ apply V293_prefix_fixture_globals.
           ++ apply V293_prefix_fixture_inputs.
        -- apply astar_comm. apply astar_l_aie_intro; [apply V293_prefix_fixture_current | reflexivity].
      * split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.

Lemma V293_prefix_fixture_caller_sat :
  V293_target_wstate V293_prefix_fixture_ge emp V293_prefix_fixture_caller V293_target_fixture_abs |=
    V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive
      V293_idle_entries V293_idle_tasks Aemp ** V293_prefix_output Tvoid 10%positive Vnull.
Proof.
  eapply V293_target_wstate_star; [V293_prefix_single_join 8%positive | apply map_join_emp | | ].
  - apply astar_r_aemp_intro.
    eapply V293_target_wstate_star with (m1 := emp) (m2 := V293_target_fixture_table)
      (o1 := emp) (o2 := V293_target_fixture_abs).
    + apply map_join_comm. apply map_join_emp.
    + apply map_join_comm. apply map_join_emp.
    + unfold V293_prefix_bindings. repeat split.
      * exists 8%positive. vm_compute; repeat split; reflexivity.
      * exists 10%positive. vm_compute; repeat split; reflexivity.
      * intros [v H]; discriminate.
      * intros [v H]; discriminate.
      * intros [v H]; discriminate.
    + eapply V293_target_wstate_star with (m1 := V293_target_fixture_table) (m2 := emp)
        (o1 := emp) (o2 := V293_target_fixture_abs).
      * apply map_join_emp.
      * apply map_join_comm. apply map_join_emp.
      * apply V293_read_pointers_witness.
      * split; reflexivity.
  - split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.

Theorem V293_OSSched_prefix_precondition_witness : exists s,
  V293_bitmap_tasks 0 16 V293_idle_tasks /\ V293_priority_table V293_idle_entries V293_idle_tasks /\
  s |= V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
    0 16 V293_witness_li V293_idle_tid (spec_done None) **
    (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive V293_idle_entries V293_idle_tasks Aemp **
      V293_prefix_output Tvoid 10%positive Vnull).
Proof.
  exists V293_prefix_fixture_state. destruct V293_idle_relations as [Hb Ht].
  split; [exact Hb | ]. split; [exact Ht | ].
  eapply V293_target_wstate_star with (o1 := emp) (o2 := V293_target_fixture_abs).
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 8%positive); [subst b; left; V293_prefix_outside | ].
    destruct (Pos.eq_dec b 10%positive); [subst b; left; V293_prefix_outside | ].
    right; left; V293_prefix_outside.
  - apply map_join_comm. apply map_join_emp.
  - apply V293_prefix_fixture_internal_sat.
  - apply V293_prefix_fixture_caller_sat.
Qed.
