(* Pending full guarded entry in one concrete state. Not initialization or reachability. *)
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
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
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

Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPreWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSharedWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.

Lemma V293_dispatch_fixture_spatial : forall different ni nl c,
  V293_target_wstate V293_change_fixture_ge emp
      (merge (V293_switch_base_memory different) (V293_change_all_extra ni nl (V293_current_mode_priority different) c))
        (V293_current_abs different) |=
      ((V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
        0 16 V293_witness_li V293_idle_tid (spec_done None) ** CurTid V293_idle_tid) **
        (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive
          (V293_current_mode_entries different) (V293_current_mode_tasks different) Aemp **
          V293_prefix_output Tvoid 10%positive Vnull)) **
      ((V293_guard_cell 108%Z 11%positive ni ** V293_guard_cell 109%Z 12%positive nl) **
        (V293_guard_cell 110%Z 13%positive (V293_current_mode_priority different) ** V293_counter_cell 111%Z 14%positive c)).
Proof.
  intros different ni nl c.
  eapply V293_target_wstate_star with (o1 := V293_current_abs different) (o2 := emp).
      - apply map_join_merge. apply map_disjoint. intros [b i].
        destruct (Pos.eq_dec b 11%positive); [subst b; left; V293_switch_outside | ].
        destruct (Pos.eq_dec b 12%positive); [subst b; left; V293_switch_outside | ].
        destruct (Pos.eq_dec b 13%positive); [subst b; left; V293_switch_outside | ].
        destruct (Pos.eq_dec b 14%positive); [subst b; left; V293_switch_outside | ].
        right; left. V293_change_outside.
      - apply map_join_emp.
      - apply V293_switch_pre_base.
      - apply V293_change_all_extra_witness.
Qed.

Theorem V293_dispatch_full_precondition_witness : forall different ni nl c events now aop,
  ni < 256 -> nl < 256 -> exists s,
  V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
  V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
  V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
  (V293_ready_select 0 16 (V293_ready_group 0 16) <> V293_current_mode_priority different <-> different = true) /\
  s |= V293_dispatch_prefix_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
    0 16 V293_shared_li V293_idle_tid (sched;;aop)
    106%Z 107%Z Tvoid 8%positive 10%positive
    (V293_current_mode_entries different) (V293_current_mode_tasks different) events now
    (V293_guard_cell 110%Z 13%positive (V293_current_mode_priority different) **
      (V293_counter_cell 111%Z 14%positive c **
        (V293_guard_cell 108%Z 11%positive ni ** (V293_guard_cell 109%Z 12%positive nl ** Aemp)))) nil nil.
Proof.
  intros different ni nl c events now aop Hni Hnl.
  set (M := merge (V293_switch_base_memory different)
    (V293_change_all_extra ni nl (V293_current_mode_priority different) c)).
  set (O := merge (V293_current_abs different) (V293_shared_prefix_extra_abs events now)).
  assert (HP : V293_target_wstate V293_change_fixture_ge emp M O |=
    (((V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
      0 16 V293_witness_li V293_idle_tid (spec_done None) ** CurTid V293_idle_tid) **
      (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive
        (V293_current_mode_entries different) (V293_current_mode_tasks different) Aemp **
        V293_prefix_output Tvoid 10%positive Vnull)) **
      ((V293_guard_cell 108%Z 11%positive ni ** V293_guard_cell 109%Z 12%positive nl) **
        (V293_guard_cell 110%Z 13%positive (V293_current_mode_priority different) ** V293_counter_cell 111%Z 14%positive c))) **
    (Aabsdata curtid (oscurt V293_idle_tid) ** (Aabsdata absecblsid (absecblist events) ** Aabsdata ostmid (ostm now)))).
  { eapply V293_target_wstate_star with (m2 := emp) (o1 := V293_current_abs different)
      (o2 := V293_shared_prefix_extra_abs events now).
    - apply map_join_emp.
    - apply map_join_merge. apply map_disjoint. intro key. destruct key; simpl; auto.
    - apply V293_dispatch_fixture_spatial.
    - apply V293_shared_prefix_extra_sat. }
  assert (HS : V293_target_wstate V293_change_fixture_ge emp M O |=
    (V293_shared_flags ** (Ais nil ** Acs nil)) **
    ((((V293_sched_internal_pre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
      0 16 V293_witness_li V293_idle_tid (spec_done None) ** CurTid V293_idle_tid) **
      (V293_prefix_frame 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive
        (V293_current_mode_entries different) (V293_current_mode_tasks different) Aemp **
        V293_prefix_output Tvoid 10%positive Vnull)) **
      ((V293_guard_cell 108%Z 11%positive ni ** V293_guard_cell 109%Z 12%positive nl) **
        (V293_guard_cell 110%Z 13%positive (V293_current_mode_priority different) ** V293_counter_cell 111%Z 14%positive c))) **
    (Aabsdata curtid (oscurt V293_idle_tid) ** (Aabsdata absecblsid (absecblist events) ** Aabsdata ostmid (ostm now))))).
  { eapply V293_target_wstate_star with (m1 := emp) (o1 := emp).
    - apply map_join_comm. apply map_join_emp.
    - apply map_join_comm. apply map_join_emp.
    - apply V293_shared_prefix_flags.
    - exact HP. }
  clear HP. unfold V293_sched_internal_pre in HS. sep normal in HS. sep destruct HS. sep split in HS.
  set (R := V293_sched_internal_resource 100%Z 101%Z 102%Z 103%Z
    1%positive 2%positive 3%positive 4%positive 0 16 V293_shared_li V293_idle_tid x **
    ((V293_shared_flags ** ((CurTid V293_idle_tid **
      V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now) **
      V293_prefix_output Tvoid 10%positive Vnull)) **
    ((Ais nil ** Acs nil) **
      ((V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive **
        V293_read_pointers Tvoid 8%positive 0 (V293_current_mode_entries different)) **
      (V293_guard_cell 110%Z 13%positive (V293_current_mode_priority different) **
        (V293_counter_cell 111%Z 14%positive c **
          (V293_guard_cell 108%Z 11%positive ni ** (V293_guard_cell 109%Z 12%positive nl ** Aemp)))))))).
  assert (HR : V293_target_wstate V293_change_fixture_ge emp M O |= R).
  { unfold R, V293_shared_fields. change V293_witness_li with V293_shared_li in HS.
    unfold V293_prefix_frame in HS. sep auto. }
  assert (HC : can_change_aop R).
  { assert (HB : forall b off vs, can_change_aop (V293_read_bytes b off vs)).
    { intros b off vs. revert off. induction vs; intros; simpl; auto. }
    assert (HV : forall tp b off vs, can_change_aop (V293_read_pointers tp b off vs)).
    { intros tp b off vs. revert off. induction vs; intros; simpl; auto. }
    unfold R, V293_sched_internal_resource, V293_sched_globals, V293_sched_inputs,
      CurLINV, CurTid, LINV, V293_shared_li, V293_shared_fields, V293_shared_flags,
      V293_prefix_output, V293_prefix_bindings, V293_guard_cell, V293_counter_cell,
      V293_counter_bindings, Agvarmapsto, Aptrmapsto.
    simpl. repeat split; intros; auto. }
  pose proof (@change_aop_rule _ _ _ (sched;;aop) _ HR HC) as Hpending.
  set (s := ((V293_change_fixture_ge, emp, M, (fun _ : hid => false), (false, nil, nil), O, (sched;;aop)) : RstateOP)).
  exists s. destruct (V293_current_mode_relations different) as [Hb [Ht Hcur]].
  split; [exact Hb | ]. split; [exact Ht | ]. split; [exact Hcur | ]. split.
  - destruct different; vm_compute; intuition congruence.
  - change (s |= R) in Hpending. clear HS HR.
    apply astar_l_aop'_intro with (aop := sched;;aop) in Hpending; [ | reflexivity].
    assert (HK : s |=
      ((V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive **
        V293_prefix_output Tvoid 10%positive Vnull)) **
      (V293_shared_flags ** ((CurTid V293_idle_tid **
        V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now) **
        ((<||sched;;aop||> ** V293_sched_internal_resource 100%Z 101%Z 102%Z 103%Z
          1%positive 2%positive 3%positive 4%positive 0 16 V293_shared_li V293_idle_tid x) **
        ((Ais nil ** Acs nil) **
          (V293_read_pointers Tvoid 8%positive 0 (V293_current_mode_entries different) **
          (V293_guard_cell 110%Z 13%positive (V293_current_mode_priority different) **
            (V293_counter_cell 111%Z 14%positive c **
              (V293_guard_cell 108%Z 11%positive ni ** (V293_guard_cell 109%Z 12%positive nl ** Aemp)))))))))).
    { unfold R in Hpending. sep auto. }
    eapply astar_mono in HK; [ | apply V293_dispatch_output_named | intros st Hz; exact Hz].
    assert (HL : s |=
      (V293_shared_flags ** ((CurTid V293_idle_tid **
        V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now) **
        V293_dispatch_cell 107%Z Tvoid)) **
      ((<||sched;;aop||> ** V293_sched_internal_resource 100%Z 101%Z 102%Z 103%Z
        1%positive 2%positive 3%positive 4%positive 0 16 V293_shared_li V293_idle_tid x) **
      ((Ais nil ** Acs nil) **
        ((V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive **
          V293_read_pointers Tvoid 8%positive 0 (V293_current_mode_entries different)) **
        (V293_guard_cell 110%Z 13%positive (V293_current_mode_priority different) **
          (V293_counter_cell 111%Z 14%positive c **
            (V293_guard_cell 108%Z 11%positive ni ** (V293_guard_cell 109%Z 12%positive nl ** Aemp)))))))).
    { clear Hpending. unfold V293_dispatch_cell. sep auto. }
    eapply astar_mono in HL; [ | apply V293_dispatch_entry_close | intros st Hz; exact Hz].
    clear Hpending HK. unfold V293_dispatch_prefix_pre, V293_sched_internal_pre.
    sep auto.
Qed.
