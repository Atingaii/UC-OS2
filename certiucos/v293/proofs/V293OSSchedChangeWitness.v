(* All byte-valued current priorities and all UINT32 counter values coexist
   with the SAME complete prefix resources. This includes equal/different
   priorities and max_unsigned, not just a favorable no-wrap example. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuardsWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_change_fixture_ge :=
  set (set V293_guard_fixture_ge 110%Z (13%positive, Tint8))
    111%Z (14%positive, Tint32).
Definition V293_counter_memory b c := V293_encoded_memory b 0 true (encode_val Tint32 (Vint32 c)).
Definition V293_change_extra nc c := merge (V293_guard_memory 13%positive nc) (V293_counter_memory 14%positive c).

Lemma V293_counter_cell_witness : forall ge x b c,
  get ge x = Some (b, Tint32) ->
  V293_wstate ge emp (V293_counter_memory b c) |= V293_counter_cell x b c.
Proof.
  intros ge x b c G. unfold V293_counter_cell, V293_counter_bindings.
  eapply V293_wstate_star with (m1 := emp) (m2 := V293_counter_memory b c).
  - apply map_join_comm. apply map_join_emp.
  - split.
    + exists b. split; [exact G | ]. repeat split; reflexivity.
    + split; [intros [v E]; discriminate | split; reflexivity].
  - split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.

Lemma V293_change_extra_witness : forall nc c,
  V293_wstate V293_change_fixture_ge emp (V293_change_extra nc c) |=
    V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c.
Proof.
  intros nc c. eapply V293_wstate_star.
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 13%positive) as [E | E].
    + subst b. right; left. apply V293_encoded_memory_outside. left; discriminate.
    + left. apply V293_encoded_memory_outside. left; exact E.
  - apply V293_guard_cell_witness. vm_compute; reflexivity.
  - apply V293_counter_cell_witness. vm_compute; reflexivity.
Qed.

Definition V293_change_all_extra ni nl nc c :=
  merge (V293_guard_pair_memory ni nl) (V293_change_extra nc c).

Ltac V293_change_outside :=
  unfold V293_change_all_extra, V293_guard_pair_memory, V293_change_extra,
    V293_guard_memory, V293_counter_memory;
  repeat rewrite map_merge_semp by reflexivity;
  repeat rewrite V293_encoded_memory_outside by (left; congruence); reflexivity.

Lemma V293_change_all_extra_witness : forall ni nl nc c,
  V293_wstate V293_change_fixture_ge emp (V293_change_all_extra ni nl nc c) |=
    (V293_guard_cell 108%Z 11%positive ni ** V293_guard_cell 109%Z 12%positive nl) **
    (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c).
Proof.
  intros ni nl nc c. eapply V293_wstate_star.
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 11%positive) as [E | E].
    + subst b. right; left. unfold V293_change_extra, V293_guard_memory, V293_counter_memory.
      repeat rewrite map_merge_semp by reflexivity.
      repeat rewrite V293_encoded_memory_outside by (left; discriminate). reflexivity.
    + destruct (Pos.eq_dec b 12%positive) as [E' | E'].
      * subst b. right; left. unfold V293_change_extra, V293_guard_memory, V293_counter_memory.
        repeat rewrite map_merge_semp by reflexivity.
        repeat rewrite V293_encoded_memory_outside by (left; discriminate). reflexivity.
      * left. unfold V293_guard_pair_memory, V293_guard_memory.
        repeat rewrite map_merge_semp by reflexivity.
        repeat rewrite V293_encoded_memory_outside by (left; assumption). reflexivity.
  - eapply V293_wstate_star.
    + apply map_join_merge. apply map_disjoint. intros [b i].
      destruct (Pos.eq_dec b 11%positive) as [E | E].
      * subst b. right; left. apply V293_encoded_memory_outside. left; discriminate.
      * left. apply V293_encoded_memory_outside. left; exact E.
    + apply V293_guard_cell_witness. vm_compute; reflexivity.
    + apply V293_guard_cell_witness. vm_compute; reflexivity.
  - apply V293_change_extra_witness.
Qed.

Theorem V293_OSSched_changed_precondition_witness : forall ni nl nc c,
  ni < 256 -> nl < 256 -> nc < 256 -> exists s,
  V293_bitmap_tasks 0 16 V293_idle_tasks /\ V293_priority_table V293_idle_entries V293_idle_tasks /\
  s |= V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
    0 16 V293_witness_li V293_idle_tid (spec_done None) **
    (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive V293_idle_entries V293_idle_tasks
      (V293_guard_cell 110%Z 13%positive nc **
        (V293_guard_cell 108%Z 11%positive ni ** (V293_guard_cell 109%Z 12%positive nl ** Aemp))) **
      (V293_prefix_output Tvoid 10%positive Vnull ** V293_counter_cell 111%Z 14%positive c)).
Proof.
  intros ni nl nc c Hni Hnl Hnc.
  exists (V293_target_wstate V293_change_fixture_ge emp
    (merge V293_prefix_fixture_memory (V293_change_all_extra ni nl nc c)) V293_target_fixture_abs).
  destruct V293_idle_relations as [Hb Ht]. split; [exact Hb | ]. split; [exact Ht | ].
  assert (Hs : V293_target_wstate V293_change_fixture_ge emp
    (merge V293_prefix_fixture_memory (V293_change_all_extra ni nl nc c)) V293_target_fixture_abs |=
      (V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
        0 16 V293_witness_li V293_idle_tid (spec_done None) **
        (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive V293_idle_entries V293_idle_tasks Aemp **
          V293_prefix_output Tvoid 10%positive Vnull)) **
      ((V293_guard_cell 108%Z 11%positive ni ** V293_guard_cell 109%Z 12%positive nl) **
        (V293_guard_cell 110%Z 13%positive nc ** V293_counter_cell 111%Z 14%positive c))).
  { eapply V293_target_wstate_star with (o1 := V293_target_fixture_abs) (o2 := emp).
    - apply map_join_merge. apply map_disjoint. intros [b i].
      destruct (Pos.eq_dec b 11%positive) as [E | E].
      + subst b. left. unfold V293_prefix_fixture_memory. V293_prefix_outside.
      + destruct (Pos.eq_dec b 12%positive) as [E' | E'].
        * subst b. left. unfold V293_prefix_fixture_memory. V293_prefix_outside.
        * destruct (Pos.eq_dec b 13%positive) as [E'' | E''].
          -- subst b. left. unfold V293_prefix_fixture_memory. V293_prefix_outside.
          -- destruct (Pos.eq_dec b 14%positive) as [Efour | Efour].
             ++ subst b. left. unfold V293_prefix_fixture_memory. V293_prefix_outside.
             ++ right; left. V293_change_outside.
    - apply map_join_emp.
    - apply V293_prefix_pre_with_env; vm_compute; reflexivity.
    - apply V293_change_all_extra_witness. }
  unfold V293_prefix_frame in *. sep auto.
Qed.
