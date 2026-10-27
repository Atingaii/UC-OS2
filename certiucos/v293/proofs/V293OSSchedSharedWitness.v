(* Same-state entry witness, not initialization or reachability. Physical
   pointer, bitmap, priority array and unique abstract table coexist. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPreWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChangeWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternalWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Definition V293_shared_prefix_extra_abs (es : EcbMod.map) (n : int32) : osabst :=
  merge (sig curtid (oscurt V293_idle_tid))
    (merge (sig absecblsid (absecblist es)) (sig ostmid (ostm n))).
Lemma V293_shared_prefix_extra_sat : forall es n,
  V293_target_wstate V293_change_fixture_ge emp emp (V293_shared_prefix_extra_abs es n) |=
  Aabsdata curtid (oscurt V293_idle_tid) **
    (Aabsdata absecblsid (absecblist es) ** Aabsdata ostmid (ostm n)).
Proof.
  intros. unfold V293_shared_prefix_extra_abs.
  repeat (eapply V293_target_wstate_star; [apply map_join_emp | apply map_join_merge; apply map_disjoint; intros key; destruct key; simpl; auto | split; reflexivity | ]).
  split; reflexivity.
Qed.
Lemma V293_shared_prefix_flags :
  V293_target_wstate V293_change_fixture_ge emp emp emp |=
  V293_shared_flags ** (Ais nil ** Acs nil).
Proof.
  unfold V293_shared_flags.
  repeat (eapply V293_target_wstate_star with (m1 := emp) (m2 := emp) (o1 := emp) (o2 := emp);
    [apply map_join_emp | apply map_join_emp | | ]).
  - exists (fun _ : hid => false). split; repeat split; reflexivity.
  - repeat split; reflexivity.
  - exists INUM. repeat split; reflexivity.
  - repeat split; reflexivity.
  - repeat split; reflexivity.
Qed.
Theorem V293_OSSched_shared_precondition_witness : forall different es n,
  exists s,
  V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
  V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
  V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
  (V293_ready_select 0 16 (V293_ready_group 0 16) <> V293_current_mode_priority different <-> different = true) /\
  s |= V293_shared_prefix_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
    0 16 V293_witness_li V293_idle_tid (spec_done None)
    106%Z 107%Z Tvoid 8%positive 10%positive
    (V293_current_mode_entries different) (V293_current_mode_tasks different) es n Aemp Vnull nil nil.
Proof.
  intros different es n.
  exists (V293_target_wstate V293_change_fixture_ge emp (V293_switch_base_memory different)
    (merge (V293_current_abs different) (V293_shared_prefix_extra_abs es n))).
  destruct (V293_current_mode_relations different) as [Hb [Ht Hcur]].
  split; [exact Hb | ]. split; [exact Ht | ]. split; [exact Hcur | ]. split.
  - destruct different; vm_compute; intuition congruence.
  - assert (HP : V293_target_wstate V293_change_fixture_ge emp (V293_switch_base_memory different)
      (merge (V293_current_abs different) (V293_shared_prefix_extra_abs es n)) |=
      ((V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
        0 16 V293_witness_li V293_idle_tid (spec_done None) ** CurTid V293_idle_tid) **
        (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive
          (V293_current_mode_entries different) (V293_current_mode_tasks different) Aemp **
          V293_prefix_output Tvoid 10%positive Vnull)) **
      (Aabsdata curtid (oscurt V293_idle_tid) **
        (Aabsdata absecblsid (absecblist es) ** Aabsdata ostmid (ostm n)))).
    { eapply V293_target_wstate_star with (m2 := emp) (o1 := V293_current_abs different)
        (o2 := V293_shared_prefix_extra_abs es n).
      - apply map_join_emp.
      - apply map_join_merge. apply map_disjoint. intro key. destruct key; simpl; auto.
      - apply V293_switch_pre_base.
      - apply V293_shared_prefix_extra_sat. }
    assert (HS : V293_target_wstate V293_change_fixture_ge emp (V293_switch_base_memory different)
      (merge (V293_current_abs different) (V293_shared_prefix_extra_abs es n)) |=
      (V293_shared_flags ** (Ais nil ** Acs nil)) **
      (((V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
        0 16 V293_witness_li V293_idle_tid (spec_done None) ** CurTid V293_idle_tid) **
        (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive
          (V293_current_mode_entries different) (V293_current_mode_tasks different) Aemp **
          V293_prefix_output Tvoid 10%positive Vnull)) **
      (Aabsdata curtid (oscurt V293_idle_tid) **
        (Aabsdata absecblsid (absecblist es) ** Aabsdata ostmid (ostm n))))).
    { eapply V293_target_wstate_star with (m1 := emp) (o1 := emp).
      - apply map_join_comm. apply map_join_emp.
      - apply map_join_comm. apply map_join_emp.
      - apply V293_shared_prefix_flags.
      - exact HP. }
    clear HP. unfold V293_shared_prefix_pre, V293_prefix_frame.
    assert (HK : V293_target_wstate V293_change_fixture_ge emp (V293_switch_base_memory different)
      (merge (V293_current_abs different) (V293_shared_prefix_extra_abs es n)) |=
      (V293_shared_flags ** (CurTid V293_idle_tid **
        V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) es n)) **
      (V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
        0 16 V293_witness_li V293_idle_tid (spec_done None) **
        ((Ais nil ** Acs nil) **
          ((V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive **
            V293_read_pointers Tvoid 8%positive 0 (V293_current_mode_entries different)) **
            (Aemp ** V293_prefix_output Tvoid 10%positive Vnull)))))
      by (unfold V293_shared_fields, V293_prefix_frame in *; sep auto).
    eapply astar_mono in HK; [ | apply V293_shared_snapshot_close | intros st H; exact H].
    clear HS. sep auto.
Qed.
