(* The guarded prefix precondition is simultaneously satisfiable for EVERY
   pair of byte-valued nesting counters, not just the enabled branch. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
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

Definition V293_guard_fixture_ge :=
  set (set V293_prefix_fixture_ge 108%Z (11%positive, Tint8))
    109%Z (12%positive, Tint8).
Definition V293_guard_memory b n := V293_encoded_memory b 0 false (encode_val Tint8 (V293_byteval n)).
Definition V293_guard_pair_memory ni nl := merge (V293_guard_memory 11%positive ni) (V293_guard_memory 12%positive nl).

Lemma V293_guard_cell_witness : forall ge x b n,
  get ge x = Some (b, Tint8) ->
  V293_wstate ge emp (V293_guard_memory b n) |= V293_guard_cell x b n.
Proof.
  intros ge x b n G. unfold V293_guard_cell.
  eapply V293_wstate_star with (m1 := emp) (m2 := V293_guard_memory b n).
  - apply map_join_comm. apply map_join_emp.
  - split.
    + exists b. split; [exact G | ]. repeat split; reflexivity.
    + split; [intros [v E]; discriminate | split; reflexivity].
  - split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.

Lemma V293_guard_pair_witness : forall ni nl,
  V293_wstate V293_guard_fixture_ge emp (V293_guard_pair_memory ni nl) |=
    V293_guard_cell 108%Z 11%positive ni ** V293_guard_cell 109%Z 12%positive nl.
Proof.
  intros ni nl. eapply V293_wstate_star.
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 11%positive) as [E | E].
    + subst b. right; left. apply V293_encoded_memory_outside. left; discriminate.
    + left. apply V293_encoded_memory_outside. left; exact E.
  - apply V293_guard_cell_witness. vm_compute; reflexivity.
  - apply V293_guard_cell_witness. vm_compute; reflexivity.
Qed.

Theorem V293_OSSched_guarded_precondition_witness : forall ni nl,
  ni < 256 -> nl < 256 -> exists s,
  V293_bitmap_tasks 0 16 V293_idle_tasks /\ V293_priority_table V293_idle_entries V293_idle_tasks /\
  s |= V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
    0 16 V293_witness_li V293_idle_tid (spec_done None) **
    (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive V293_idle_entries V293_idle_tasks
      (V293_guard_cell 108%Z 11%positive ni ** (V293_guard_cell 109%Z 12%positive nl ** Aemp)) **
      V293_prefix_output Tvoid 10%positive Vnull).
Proof.
  intros ni nl Hni Hnl.
  exists (V293_target_wstate V293_guard_fixture_ge emp
    (merge V293_prefix_fixture_memory (V293_guard_pair_memory ni nl)) V293_target_fixture_abs).
  destruct V293_idle_relations as [Hb Ht]. split; [exact Hb | ]. split; [exact Ht | ].
  assert (Hs : V293_target_wstate V293_guard_fixture_ge emp
    (merge V293_prefix_fixture_memory (V293_guard_pair_memory ni nl)) V293_target_fixture_abs |=
      (V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
        0 16 V293_witness_li V293_idle_tid (spec_done None) **
        (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive V293_idle_entries V293_idle_tasks Aemp **
          V293_prefix_output Tvoid 10%positive Vnull)) **
      (V293_guard_cell 108%Z 11%positive ni ** V293_guard_cell 109%Z 12%positive nl)).
  { eapply V293_target_wstate_star with (o1 := V293_target_fixture_abs) (o2 := emp).
    - apply map_join_merge. apply map_disjoint. intros [b i].
      destruct (Pos.eq_dec b 11%positive) as [E | E].
      + subst b. left. unfold V293_prefix_fixture_memory. V293_prefix_outside.
      + destruct (Pos.eq_dec b 12%positive) as [E' | E'].
        * subst b. left. unfold V293_prefix_fixture_memory. V293_prefix_outside.
        * right; left. unfold V293_guard_pair_memory, V293_guard_memory.
          rewrite map_merge_semp by reflexivity.
          repeat rewrite V293_encoded_memory_outside by (left; assumption). reflexivity.
    - apply map_join_emp.
    - apply V293_prefix_pre_with_env; vm_compute; reflexivity.
    - apply V293_guard_pair_witness. }
  unfold V293_prefix_frame in *. sep auto.
Qed.
