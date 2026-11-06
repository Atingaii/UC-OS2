(* Constructed same-state CLOSED prefix entry. Full physical arrays, two
   current-pointer halves and the unique abstract slots coexist. This is not
   an initialization/reachability theorem; extra storage and stacks are empty. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Fixpoint V293_full_array_memory (b : block) (offset : Z) (tau : type) (vs : list val) : mem :=
  match vs with
  | nil => emp
  | v :: tail => merge (V293_encoded_memory b offset true (encode_val tau v))
      (V293_full_array_memory b (offset + Z.of_nat (typelen tau))%Z tau tail)
  end.
Lemma V293_full_array_outside : forall vs b offset tau b' i,
  b' <> b \/ (i < offset)%Z \/
    (offset + Z.of_nat (typelen tau) * Z.of_nat (length vs) <= i)%Z ->
  get (V293_full_array_memory b offset tau vs) (b', i) = None.
Proof.
  induction vs as [ | v tail IH]; intros b offset tau b' i H; [apply map_emp_get | ].
  cbn [V293_full_array_memory]. rewrite map_merge_semp by reflexivity.
  rewrite V293_encoded_memory_outside.
  - rewrite IH; [reflexivity | simpl length in H; rewrite Nat2Z.inj_succ in H; intuition nia].
  - rewrite encode_val_length. simpl length in H. rewrite Nat2Z.inj_succ in H.
    pose proof (Nat2Z.is_nonneg (length tail)). pose proof (Nat2Z.is_nonneg (typelen tau)). intuition nia.
Qed.

Lemma V293_full_array_join : forall vs b offset tau v,
  join (V293_encoded_memory b offset true (encode_val tau v))
    (V293_full_array_memory b (offset + Z.of_nat (typelen tau))%Z tau vs)
    (V293_full_array_memory b offset tau (v :: vs)).
Proof.
  intros. apply map_join_merge. apply map_disjoint. intros [b' i].
  destruct (Pos.eq_dec b' b) as [E | E].
  - subst b'. destruct (Z_lt_dec i (offset + Z.of_nat (typelen tau))) as [H | H].
    + right; left. apply V293_full_array_outside. right; left; exact H.
    + left. apply V293_encoded_memory_outside. right; right. rewrite encode_val_length. lia.
  - left. apply V293_encoded_memory_outside. left; exact E.
Qed.
Lemma V293_full_array_witness : forall vs ge le b offset tau,
  V293_wstate ge le (V293_full_array_memory b offset tau vs) |=
    V293_array true b offset (Z.of_nat (typelen tau)) tau vs.
Proof.
  induction vs as [ | v tail IH]; intros ge le b offset tau; [split; reflexivity | ].
  eapply V293_wstate_star; [apply V293_full_array_join | | apply IH].
  split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Lemma V293_array_aop_independent : forall w b offset step tau vs,
  can_change_aop (V293_array w b offset step tau vs).
Proof. intros w b offset step tau vs. revert offset. induction vs; intros; simpl; auto. Qed.

Definition V293_storage_prefix_inputs_memory :=
  merge (V293_full_array_memory 1%positive 0 Tint8 (map V293_byteval V293_ready_table))
    (merge (V293_full_array_memory 3%positive 0 Tint8 (map V293_byteval [0;16]))
      (V293_encoded_memory 2%positive 0 true (encode_val Tint8 (V293_byteval 2)))).
Definition V293_storage_prefix_local_memory different :=
  merge V293_witness_high
    (V293_full_array_memory 8%positive 0 (Tptr Tvoid) (V293_current_mode_entries different)).
Definition V293_storage_prefix_shared_memory :=
  merge (V293_encoded_memory 6%positive 0 true (encode_val (Tptr Tvoid) (Vptr V293_idle_tid)))
    (V293_encoded_memory 10%positive 0 true (encode_val (Tptr Tvoid) (Vptr V293_idle_tid))).
Definition V293_storage_prefix_memory different :=
  merge V293_storage_prefix_inputs_memory
    (merge (V293_storage_prefix_local_memory different) V293_storage_prefix_shared_memory).

Ltac V293_storage_prefix_outside :=
  unfold V293_storage_prefix_inputs_memory, V293_storage_prefix_local_memory,
    V293_storage_prefix_shared_memory, V293_witness_high;
  repeat rewrite map_merge_semp by reflexivity;
  repeat first [rewrite V293_full_array_outside by (left; congruence) |
    rewrite V293_encoded_memory_outside by (left; congruence)]; reflexivity.

Lemma V293_storage_prefix_inputs_witness : forall ge,
  V293_wstate ge emp V293_storage_prefix_inputs_memory |=
    V293_inputs_full 1%positive 2%positive 3%positive 0 16.
Proof.
  intro ge. assert (HS : V293_wstate ge emp V293_storage_prefix_inputs_memory |=
    V293_array true 1%positive 0 1 Tint8 (map V293_byteval V293_ready_table) **
      (V293_array true 3%positive 0 1 Tint8 (map V293_byteval [0;16]) **
        Amapsto (2%positive, 0%Z) Tint8 true (V293_byteval 2))).
  { eapply V293_wstate_star.
    - apply map_join_merge. apply map_disjoint. intros [b i].
      destruct (Pos.eq_dec b 1%positive); [subst b; right; left | left]; V293_storage_prefix_outside.
    - apply V293_full_array_witness.
    - eapply V293_wstate_star.
      + apply map_join_merge. apply map_disjoint. intros [b i].
        destruct (Pos.eq_dec b 3%positive); [subst b; right; left | left]; V293_storage_prefix_outside.
      + apply V293_full_array_witness.
      + split; [apply V293_encoded_memory_mapsto | reflexivity]. }
  unfold V293_inputs_full. change (V293_ready_group 0 16) with 2. sep auto.
Qed.
Lemma V293_storage_prefix_local_witness : forall ge different,
  V293_wstate ge emp (V293_storage_prefix_local_memory different) |=
    (PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0)) **
      V293_array true 8%positive 0 4 (Tptr Tvoid) (V293_current_mode_entries different).
Proof.
  intros ge different. eapply V293_wstate_star.
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 4%positive); [subst b; right; left | left]; V293_storage_prefix_outside.
  - split; [apply V293_encoded_memory_mapsto | reflexivity].
  - apply V293_full_array_witness.
Qed.
Lemma V293_storage_prefix_pointer_witness : forall ge x b t,
  get ge x = Some (b, Tptr Tvoid) ->
  V293_wstate ge emp
    (V293_encoded_memory b 0 true (encode_val (Tptr Tvoid) (Vptr t))) |=
    GV x @ (Tptr Tvoid) |-> (Vptr t).
Proof.
  intros ge x b t HG. exists b. eapply V293_wstate_star with (m1 := emp).
  - apply map_join_comm. apply map_join_emp.
  - exists b. split; [exact HG | ]. repeat split; reflexivity.
  - split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.
Lemma V293_storage_prefix_shared_witness : forall ge,
  get ge OSTCBCur = Some (6%positive, Tptr Tvoid) ->
  get ge 107%Z = Some (10%positive, Tptr Tvoid) ->
  V293_wstate ge emp V293_storage_prefix_shared_memory |=
    (GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
      (GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)).
Proof.
  intros ge Hcur Htarget. eapply V293_wstate_star.
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 6%positive); [subst b; right; left | left]; V293_storage_prefix_outside.
  - apply V293_storage_prefix_pointer_witness; assumption.
  - apply V293_storage_prefix_pointer_witness; assumption.
Qed.
Lemma V293_storage_prefix_physical_witness : forall ge different,
  get ge OSTCBCur = Some (6%positive, Tptr Tvoid) ->
  get ge 107%Z = Some (10%positive, Tptr Tvoid) ->
  V293_wstate ge emp (V293_storage_prefix_memory different) |=
    V293_inputs_full 1%positive 2%positive 3%positive 0 16 **
      (((PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0)) **
        V293_array true 8%positive 0 4 (Tptr Tvoid) (V293_current_mode_entries different)) **
        ((GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
          (GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)))).
Proof.
  intros ge different Hcur Htarget. eapply V293_wstate_star.
  - apply map_join_merge. apply map_disjoint. intros [b i].
    destruct (Pos.eq_dec b 1%positive); [subst b; right; left; V293_storage_prefix_outside | ].
    destruct (Pos.eq_dec b 2%positive); [subst b; right; left; V293_storage_prefix_outside | ].
    destruct (Pos.eq_dec b 3%positive); [subst b; right; left; V293_storage_prefix_outside | ].
    left. V293_storage_prefix_outside.
  - apply V293_storage_prefix_inputs_witness.
  - eapply V293_wstate_star.
    + apply map_join_merge. apply map_disjoint. intros [b i].
      destruct (Pos.eq_dec b 4%positive); [subst b; right; left; V293_storage_prefix_outside | ].
      destruct (Pos.eq_dec b 8%positive); [subst b; right; left; V293_storage_prefix_outside | ].
      left. V293_storage_prefix_outside.
    + apply V293_storage_prefix_local_witness.
    + apply V293_storage_prefix_shared_witness; assumption.
Qed.

Theorem V293_storage_closed_prefix_entry_witness : forall different events now aop,
  exists s,
    V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
    V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
    V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
    Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) (V293_current_mode_entries different) /\
    s |= V293_storage_prefix_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z
      1%positive 2%positive 3%positive 4%positive 8%positive 10%positive Tvoid 0 16
      (V293_current_mode_entries different) nil V293_idle_tid
      (V293_current_mode_tasks different) events now aop nil nil Aemp V293_idle_tid (V293_byteval 0).
Proof.
  intros different events now aop.
  set (M := V293_storage_prefix_memory different).
  set (O := V293_shared_fixture_abs V293_idle_tid (V293_current_mode_tasks different) events now).
  set (s := ((V293_prefix_fixture_ge, emp, M, (fun _ : hid => false),
    (false, nil, nil), O, aop) : RstateOP)).
  exists s. destruct (V293_current_mode_relations different) as [Hb [Ht Hcur]].
  split; [exact Hb | ]. split; [exact Ht | ]. split; [exact Hcur | ].
  assert (Hptr : Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true)
    (V293_current_mode_entries different)) by (destruct different; vm_compute; repeat constructor).
  split; [exact Hptr | ].
  assert (HP : V293_target_wstate V293_prefix_fixture_ge emp M O |=
    (V293_inputs_full 1%positive 2%positive 3%positive 0 16 **
      (((PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0)) **
        V293_array true 8%positive 0 4 (Tptr Tvoid) (V293_current_mode_entries different)) **
        ((GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
          (GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid))))) **
      V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now).
  { eapply V293_target_wstate_star with (m2 := emp) (o1 := emp).
    - apply map_join_emp.
    - apply map_join_comm. apply map_join_emp.
    - apply V293_storage_prefix_physical_witness; vm_compute; reflexivity.
    - unfold O, V293_shared_fixture_abs, V293_shared_fields.
      repeat (eapply V293_target_wstate_star; [apply map_join_emp | apply map_join_merge;
        apply map_disjoint; intros key; destruct key; simpl; auto | split; reflexivity | ]).
      split; reflexivity. }
  assert (HF : V293_target_wstate V293_prefix_fixture_ge emp emp emp |=
    V293_shared_flags ** ((Ais nil ** Acs nil) **
      (V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
        V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive))).
  { unfold V293_shared_flags.
    repeat (eapply V293_target_wstate_star with (m1 := emp) (m2 := emp) (o1 := emp) (o2 := emp);
      [apply map_join_emp | apply map_join_emp | | ]).
    - exists (fun _ : hid => false). split; repeat split; reflexivity.
    - repeat split; reflexivity.
    - exists INUM. repeat split; reflexivity.
    - repeat split; reflexivity.
    - repeat split; reflexivity.
    - apply V293_prefix_fixture_globals; vm_compute; reflexivity.
    - unfold V293_prefix_bindings. repeat split.
      + exists 8%positive. split; [vm_compute; reflexivity | ]. repeat split; reflexivity.
      + exists 10%positive. split; [vm_compute; reflexivity | ]. repeat split; reflexivity.
      + intros [v H]; discriminate.
      + intros [v H]; discriminate.
      + intros [v H]; discriminate. }
  assert (HS : V293_target_wstate V293_prefix_fixture_ge emp M O |=
    (V293_shared_flags ** ((Ais nil ** Acs nil) **
      (V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
        V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive))) **
    ((V293_inputs_full 1%positive 2%positive 3%positive 0 16 **
      (((PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0)) **
        V293_array true 8%positive 0 4 (Tptr Tvoid) (V293_current_mode_entries different)) **
        ((GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
          (GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid))))) **
      V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now)).
  { eapply V293_target_wstate_star with (m1 := emp) (o1 := emp);
      [apply map_join_comm; apply map_join_emp | apply map_join_comm; apply map_join_emp | exact HF | exact HP]. }
  assert (HC : can_change_aop
    ((V293_shared_flags ** ((Ais nil ** Acs nil) **
      (V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
        V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive))) **
    ((V293_inputs_full 1%positive 2%positive 3%positive 0 16 **
      (((PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0)) **
        V293_array true 8%positive 0 4 (Tptr Tvoid) (V293_current_mode_entries different)) **
        ((GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
          (GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid))))) **
      V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now))).
  { unfold V293_shared_flags, V293_sched_globals, V293_prefix_bindings,
      V293_shared_fields, V293_inputs_full, Agvarmapsto, Aptrmapsto.
    cbn [can_change_aop]. repeat split; try exact I; intros; repeat split; try exact I;
      apply V293_array_aop_independent. }
  pose proof (@change_aop_rule _ _ _ aop _ HS HC) as HK. fold s in HK.
  assert (HJ : s |= (CurTid V293_idle_tid ** CurTid V293_idle_tid) **
    ((V293_shared_flags ** (V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now **
      (GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)))) **
      ((V293_inputs_full 1%positive 2%positive 3%positive 0 16 **
        ((PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0)) **
          V293_array true 8%positive 0 4 (Tptr Tvoid) (V293_current_mode_entries different))) **
        ((Ais nil ** Acs nil) ** (V293_sched_globals 100%Z 101%Z 102%Z 103%Z
          1%positive 2%positive 3%positive 4%positive **
          V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive))))).
  { eapply astar_mono with (P := GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)).
    - intros st H. apply GV_separate_rw in H. unfold CurTid. sep auto.
    - intros st H; exact H.
    - clear HP HS HF. sep auto. }
  assert (HL : s |=
    (V293_storage_open 107%Z Tvoid V293_idle_tid (V293_current_mode_tasks different) events now V293_idle_tid **
      V293_prefix_entry_heap 1%positive 2%positive 3%positive 4%positive 8%positive Tvoid
        0 16 (V293_current_mode_entries different) nil (V293_byteval 0)) **
      (CurTid V293_idle_tid ** ((Ais nil ** Acs nil) **
        (V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
          V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive)))).
  { unfold V293_storage_open, V293_prefix_entry_heap. cbn [V293_storage]. clear HP HS HK HF. sep auto. }
  eapply astar_mono in HL.
  2: { apply V293_prefix_entry_close; try lia; [apply V293_byte_type; lia | exact Hptr]. }
  2: { intros st H; exact H. }
  apply astar_assoc_intro in HL.
  eapply astar_mono in HL.
  2: { intros st H; exact H. }
  2: { apply astar_mono; [intros st H; exact H | apply astar_r_aemp_intro]. }
  apply astar_l_aop'_intro with (aop := aop) in HL; [ | reflexivity].
  exact HL.
Qed.

(* Reuse the physical state above, not an independent mathematical fixture.
   Both current-task modes have one shared task map and the same full arrays. *)
Theorem V293_ready_invariant_witness : forall different events now (aop : spec_code),
  exists s,
    (s |= <||aop||> ** (SWINVt (V293_ready_inv 1%positive 2%positive 3%positive 4%positive
      8%positive Tvoid nil 107%Z) V293_idle_tid ** Atrue)) /\
    (s |= V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now **
      (V293_prefix_entry_heap 1%positive 2%positive 3%positive 4%positive 8%positive Tvoid
        0 16 (V293_current_mode_entries different) nil (V293_byteval 0) ** Atrue)).
Proof.
  intros different events now aop.
  destruct (V293_storage_closed_prefix_entry_witness different events now aop)
    as (s & Hb & Ht & Hcur & Hptr & Hs).
  unfold V293_storage_prefix_entry in Hs.
  eapply astar_mono in Hs; [ | intros st H; exact H | apply astar_mono].
  2: { apply astar_mono; [intros st [_ H]; exact H | intros st H; exact H]. }
  2: { intros st H; exact H. }
  exists s. split.
  - assert (HP : s |=
      (V293_shared_flags **
        (CurTid V293_idle_tid ** (V293_shared_fields V293_idle_tid
          (V293_current_mode_tasks different) events now **
            (V293_dispatch_cell 107%Z Tvoid **
              V293_ready_resources 1%positive 2%positive 3%positive 4%positive
                8%positive Tvoid nil (V293_current_mode_tasks different))))) **
      (CurTid V293_idle_tid ** (<||aop||> ** Atrue))).
    { unfold V293_storage_open, V293_prefix_entry_heap in Hs.
      unfold V293_ready_resources, V293_retained_prefix_entry_heap, V293_dispatch_cell.
      assert (Hr : exists p, V293_bitmap_ready 0 16 p).
      { exists 12. right. split; [lia | ]. split; [lia | vm_compute; reflexivity]. }
      assert (Hhv : rule_type_val_match Tint8 (V293_byteval 0) = true)
        by (apply V293_byte_type; lia).
      cbn [V293_storage] in *. sep auto. repeat first [assumption | split | lia]. }
    eapply astar_mono in HP.
    2: { intros st H. apply V293_ready_switch_close. unfold V293_ready_core. sep auto. }
    2: { intros st H; exact H. }
    unfold SWINVt. clear Hs. unfold CurTid in HP. sep auto.
  - unfold V293_storage_open in Hs. sep auto.
Qed.

Theorem V293_ready_enabled_entry_witness : forall aop critical,
  exists s, s |= <||aop||> **
    OS[(fun _ : hid => false), true, nil, critical] ** ATopis INUM ** Aemp.
Proof.
  intros aop critical.
  exists ((emp : env), (emp : env), (emp : mem), (fun _ : hid => false),
    (true, (@nil hid), critical), (emp : osabst), aop).
  repeat (apply sat_split'; exists (emp : mem); exists (emp : mem);
    exists (emp : osabst); exists (emp : osabst);
    split; [apply map_join_emp | ]; split; [apply map_join_emp | ]; split).
  all: repeat split; reflexivity.
Qed.

(* The execution precondition is inhabited by the same full physical fixture.
   This local witness does not assert global initialization or reachability. *)
Theorem V293_ready_prefix_execution_witness : forall different events now aop,
  exists s, (s |= V293_ready_prefix_open 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z
    1%positive 2%positive 3%positive 4%positive 8%positive 10%positive Tvoid nil
    V293_idle_tid aop nil nil Aemp) /\
    (s |= V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now ** Atrue).
Proof.
  intros different events now aop.
  destruct (V293_storage_closed_prefix_entry_witness different events now aop)
    as (s & Hb & Ht & Hcur & Hptr & Hs).
  unfold V293_storage_prefix_entry in Hs.
  eapply astar_mono in Hs; [ | intros st H; exact H | apply astar_mono].
  2: { apply astar_mono; [intros st [_ H]; exact H | intros st H; exact H]. }
  2: { intros st H; exact H. }
  exists s. split.
  - unfold V293_ready_prefix_open, V293_ready_snapshot, V293_dispatch_cell,
    V293_storage_open, V293_prefix_entry_heap in *.
  assert (Hr : exists p, V293_bitmap_ready 0 16 p).
  { exists 12. right. split; [lia | ]. split; [lia | vm_compute; reflexivity]. }
  assert (Hhv : rule_type_val_match Tint8 (V293_byteval 0) = true)
    by (apply V293_byte_type; lia).
  unfold V293_retained_prefix_entry_heap. cbn [V293_storage] in *.
  sep auto. repeat first [assumption | split | lia | reflexivity].
  - unfold V293_storage_open in Hs. sep auto.
Qed.

(* Keep only the actual private current half and global bindings from the
   physical fixture. No shared ready value is assumed while interrupts are on. *)
Theorem V293_ready_roundtrip_entry_witness : forall aop critical,
  exists s, s |= V293_ready_roundtrip_pre 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z
    1%positive 2%positive 3%positive 4%positive 8%positive 10%positive Tvoid
    V293_idle_tid aop critical Aemp.
Proof.
  intros aop critical.
  destruct (V293_storage_closed_prefix_entry_witness false EcbMod.emp Int.zero aop)
    as (s & Hb & Ht & Hcur & Hptr & Hs).
  set (P := CurTid V293_idle_tid **
    ((V293_sched_globals 100%Z 101%Z 102%Z 103%Z
      1%positive 2%positive 3%positive 4%positive **
      V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive) ** Aemp)).
  assert (HF : GoodFrm P).
  { unfold P, CurTid, Agvarmapsto, Aptrmapsto, V293_sched_globals,
      V293_prefix_bindings. simpl. repeat split; exact I. }
  assert (HP : s |= P ** Atrue).
  { unfold V293_storage_prefix_entry in Hs. unfold P. sep auto. }
  destruct s as [[[[[[ge le] M] ir] aux] O] op].
  apply sat_split in HP. destruct HP as (m1 & m2 & o1 & o2 & JM & JO & HP & _).
  assert (HQ : (ge, le, m1, (fun _ : hid => false), (true, (@nil hid), critical), o1, aop) |= P).
  { eapply goodfrm_prop; [exact HF | exact HP]. }
  exists (ge, le, m1, (fun _ : hid => false), (true, (@nil hid), critical), o1, aop).
  apply astar_l_atopis_intro with (i := INUM) in HQ; [ | reflexivity].
  apply astar_l_acs_intro with (i := critical) in HQ; [ | reflexivity].
  apply astar_l_ais_intro with (i := nil) in HQ; [ | reflexivity].
  apply astar_l_aie_intro with (i := true) in HQ; [ | reflexivity].
  apply astar_l_aisr_intro with (i := (fun _ : hid => false)) in HQ; [ | reflexivity].
  apply astar_l_aop'_intro with (aop := aop) in HQ; [ | reflexivity].
  unfold V293_ready_roundtrip_pre. fold P. sep auto.
Qed.
