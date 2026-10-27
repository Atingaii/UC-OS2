(* Same-state pending-switch witnesses, not initialization/reachability.
   Both current-ready/same-target and current-time-wait/different-target exist. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.
Definition V293_switch_fixture_ge : env :=
  set V293_shared_fixture_ge 107%Z (2%positive, Tptr Tvoid).
Definition V293_switch_target (different : bool) := if different then V293_current_next else V293_idle_tid.
Definition V293_switch_fixture_target next := V293_encoded_memory 2%positive 0 true (encode_val (Tptr Tvoid) (Vptr next)).
Definition V293_switch_fixture_mem next := merge (V293_shared_fixture_mem V293_idle_tid) (V293_switch_fixture_target next).

Lemma V293_switch_fixture_pointer : forall var block t,
  get V293_switch_fixture_ge var = Some (block, Tptr Tvoid) ->
  V293_target_wstate V293_switch_fixture_ge emp
    (V293_encoded_memory block 0 true (encode_val (Tptr Tvoid) (Vptr t))) emp |=
    GV var @ (Tptr Tvoid) |-> (Vptr t).
Proof.
  intros var block t HG. exists block. eapply V293_target_wstate_star with
    (m1 := emp) (o1 := emp) (o2 := emp).
  - apply map_join_comm. apply map_join_emp.
  - apply map_join_emp.
  - exists block. split; [exact HG | ]. repeat split; reflexivity.
  - split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Lemma V293_switch_fixture_spatial : forall tasks events now next,
  V293_target_wstate V293_switch_fixture_ge emp (V293_switch_fixture_mem next)
    (V293_shared_fixture_abs V293_idle_tid tasks events now) |=
    V293_shared_flags **
      ((GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
        (V293_shared_fields V293_idle_tid tasks events now **
          (GV 107%Z @ (Tptr Tvoid) |-> (Vptr next)))) ** (Ais nil ** Acs nil).
Proof.
  intros tasks events now next.
  assert (HF : V293_target_wstate V293_switch_fixture_ge emp emp emp |=
    V293_shared_flags ** (Ais nil ** Acs nil)).
  { unfold V293_shared_flags.
    repeat (eapply V293_target_wstate_star with (m1 := emp) (m2 := emp) (o1 := emp) (o2 := emp);
      [apply map_join_emp | apply map_join_emp | | ]).
    - exists (fun _ : hid => false). split; repeat split; reflexivity.
    - repeat split; reflexivity.
    - exists INUM. repeat split; reflexivity.
    - repeat split; reflexivity.
    - repeat split; reflexivity. }
  assert (HA : V293_target_wstate V293_switch_fixture_ge emp emp
    (V293_shared_fixture_abs V293_idle_tid tasks events now) |=
    V293_shared_fields V293_idle_tid tasks events now).
  { unfold V293_shared_fields, V293_shared_fixture_abs.
    repeat (eapply V293_target_wstate_star; [apply map_join_emp | apply map_join_merge;
      apply map_disjoint; intros key; destruct key; simpl; auto | split; reflexivity | ]).
    split; reflexivity. }
  assert (HP : V293_target_wstate V293_switch_fixture_ge emp (V293_switch_fixture_mem next) emp |=
    (GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
    (GV 107%Z @ (Tptr Tvoid) |-> (Vptr next))).
  { eapply V293_target_wstate_star.
    - apply map_join_merge. apply map_disjoint. intros [b i].
      destruct (Pos.eq_dec b 1%positive) as [E | E].
      + subst b. right; left. apply V293_encoded_memory_outside. left; discriminate.
      + left. apply V293_encoded_memory_outside. left; exact E.
    - apply map_join_emp.
    - apply V293_switch_fixture_pointer. vm_compute; reflexivity.
    - apply V293_switch_fixture_pointer. apply map_get_set. }
  assert (HK : V293_target_wstate V293_switch_fixture_ge emp (V293_switch_fixture_mem next)
    (V293_shared_fixture_abs V293_idle_tid tasks events now) |=
    (((GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
      (GV 107%Z @ (Tptr Tvoid) |-> (Vptr next))) ** V293_shared_fields V293_idle_tid tasks events now) **
      (V293_shared_flags ** (Ais nil ** Acs nil))).
  { eapply V293_target_wstate_star with (m2 := emp) (o2 := emp).
    - apply map_join_emp.
    - apply map_join_emp.
    - eapply V293_target_wstate_star with (m2 := emp) (o1 := emp).
      + apply map_join_emp.
      + apply map_join_comm. apply map_join_emp.
      + exact HP.
      + exact HA.
    - exact HF. }
  clear HF HA HP. sep auto.
Qed.

Theorem V293_pending_switch_precondition_witness : forall different events now aop,
  exists s,
    indom (V293_current_mode_tasks different) V293_idle_tid /\
    V293_highest_ready (V293_current_mode_tasks different) (V293_switch_target different) /\
    s |= V293_switch_payload 107%Z Tvoid V293_idle_tid
      (V293_current_mode_tasks different) events now (V293_switch_target different) aop nil nil ** Aemp.
Proof.
  intros different events now aop.
  set (M := V293_switch_fixture_mem (V293_switch_target different)).
  set (O := V293_shared_fixture_abs V293_idle_tid (V293_current_mode_tasks different) events now).
  exists ((V293_switch_fixture_ge, emp, M, (fun _ : hid => false), (false, nil, nil), O, (sched;;aop)) : RstateOP).
  split.
  - destruct different; vm_compute; eexists; reflexivity.
  - split.
    + destruct different.
      * apply (V293_shared_case_highest true).
      * exists (Int.repr 12). exists Vnull. split; [apply map_get_sig | ].
        intros t' p' m' H. unfold V293_current_mode_tasks, V293_idle_tasks in H.
        destruct (tid_eq_dec V293_idle_tid t') as [E | E].
        -- subst t'. rewrite map_get_sig in H. inversion H; subst. lia.
        -- rewrite map_get_sig' in H by exact E. discriminate.
    + pose proof (V293_switch_fixture_spatial (V293_current_mode_tasks different) events now (V293_switch_target different)) as HS.
      assert (HC : can_change_aop
        (V293_shared_flags ** ((GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
          (V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now **
            (GV 107%Z @ (Tptr Tvoid) |-> (Vptr (V293_switch_target different))))) ** (Ais nil ** Acs nil))).
      { unfold V293_shared_flags, V293_shared_fields, Agvarmapsto, Aptrmapsto.
        simpl. repeat split; auto. }
      pose proof (@change_aop_rule _ _ _ ((sched;;aop)) _ HS HC) as HP.
      assert (HK : (V293_switch_fixture_ge, emp, M, (fun _ : hid => false), (false, nil, nil), O, (sched;;aop)) |=
        (CurTid V293_idle_tid ** CurTid V293_idle_tid) **
          (V293_shared_flags ** (V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now **
            (GV 107%Z @ (Tptr Tvoid) |-> (Vptr (V293_switch_target different)))) ** (Ais nil ** Acs nil))).
      { eapply astar_mono with (P := GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)).
        - intros st H. apply GV_separate_rw in H. unfold CurTid. sep auto.
        - intros st H; exact H.
        - clear HS. sep auto. }
      assert (HR : (V293_switch_fixture_ge, emp, M, (fun _ : hid => false), (false, nil, nil), O, (sched;;aop)) |=
        (V293_shared_flags ** ((CurTid V293_idle_tid **
          V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now) **
          (GV 107%Z @ (Tptr Tvoid) |-> (Vptr (V293_switch_target different))))) **
          (CurTid V293_idle_tid ** (Ais nil ** Acs nil))) by (clear HS HP; sep auto).
      eapply astar_mono in HR; [ | apply V293_dispatch_snapshot_close | intros st H; exact H].
      clear HS HP HK. unfold V293_switch_payload. sep auto.
Qed.
