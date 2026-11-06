(* Nonempty same-state entry for the connected segment. The counter is a
   separate full-write block included in prefix_cells, NOT a private frame.
   Both ready/current modes, arbitrary initial UINT32, events, time and aop.
   This constructs a fixture, not initialization or reachability. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageConnect.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_connect_fixture_ge : env :=
  set V293_prefix_fixture_ge 108%Z (12%positive, Tint32).
Definition V293_connect_counter_memory c :=
  V293_encoded_memory 12%positive 0 true (encode_val Tint32 (Vint32 c)).

Lemma V293_storage_connected_entry_witness_empty_locals : forall different c events now aop,
  exists s,
    V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
    V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
    V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
    Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) (V293_current_mode_entries different) /\
    getlenv s = emp /\
    s |= (V293_storage_prefix_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z
      1%positive 2%positive 3%positive 4%positive 8%positive 10%positive Tvoid 0 16
      (V293_current_mode_entries different) [((12%positive, 0%Z), Tint32)] V293_idle_tid
      (V293_current_mode_tasks different) events now (sched;;aop) nil nil
      (V293_counter_bindings 108%Z 12%positive ** Aemp) V293_idle_tid (V293_byteval 0)) //\\
      ((PV (12%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** Atrue).
Proof.
  intros different c events now aop.
  set (base := V293_inputs_full 1%positive 2%positive 3%positive 0 16 **
    (((PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0)) **
      V293_array true 8%positive 0 4 (Tptr Tvoid) (V293_current_mode_entries different)) **
      ((GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
        (GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid))))).
  set (fields := V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now).
  set (locals := V293_shared_flags ** ((Ais nil ** Acs nil) **
    ((V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
      V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive) **
      (V293_counter_bindings 108%Z 12%positive ** Aemp)))).
  set (raw := locals ** (base ** ((PV (12%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** fields))).
  set (M := merge (V293_storage_prefix_memory different) (V293_connect_counter_memory c)).
  set (O := V293_shared_fixture_abs V293_idle_tid (V293_current_mode_tasks different) events now).
  set (s := ((V293_connect_fixture_ge, emp, M, (fun _ : hid => false),
    (false, nil, nil), O, (sched;;aop)) : RstateOP)).
  exists s. destruct (V293_current_mode_relations different) as [Hb [Ht Hcur]].
  split; [exact Hb | ]. split; [exact Ht | ]. split; [exact Hcur | ].
  assert (Hptr : Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true)
    (V293_current_mode_entries different)) by (destruct different; vm_compute; repeat constructor).
  split; [exact Hptr | ]. split; [reflexivity | ].
  assert (HP : V293_wstate V293_connect_fixture_ge emp M |=
    base ** (PV (12%positive, Int.zero) @ Tint32 |-> (Vint32 c))).
  { eapply V293_wstate_star.
    - apply map_join_merge. apply map_disjoint. intros [b i].
      destruct (Pos.eq_dec b 12%positive); [subst b; left | right; left].
      + unfold V293_storage_prefix_memory. V293_storage_prefix_outside.
      + unfold V293_connect_counter_memory. apply V293_encoded_memory_outside. left; congruence.
    - unfold base. apply V293_storage_prefix_physical_witness; vm_compute; reflexivity.
    - split; [apply V293_encoded_memory_mapsto | reflexivity]. }
  assert (HA : V293_target_wstate V293_connect_fixture_ge emp emp O |= fields).
  { unfold O, fields, V293_shared_fixture_abs, V293_shared_fields.
    repeat (eapply V293_target_wstate_star; [apply map_join_emp | apply map_join_merge;
      apply map_disjoint; intros key; destruct key; simpl; auto | split; reflexivity | ]).
    split; reflexivity. }
  assert (HF : V293_target_wstate V293_connect_fixture_ge emp emp emp |= locals).
  { unfold locals, V293_shared_flags.
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
      + intros [v H]; discriminate.
    - unfold V293_counter_bindings. repeat split.
      + exists 12%positive. split; [vm_compute; reflexivity | ]. repeat split; reflexivity.
      + intros [v H]; discriminate.
    - split; reflexivity. }
  assert (HS : V293_target_wstate V293_connect_fixture_ge emp M O |= raw).
  { unfold raw. eapply V293_target_wstate_star with (m1 := emp) (o1 := emp).
    - apply map_join_comm. apply map_join_emp.
    - apply map_join_comm. apply map_join_emp.
    - exact HF.
    - assert (HK : V293_target_wstate V293_connect_fixture_ge emp M O |=
        (base ** (PV (12%positive, Int.zero) @ Tint32 |-> (Vint32 c))) ** fields).
      { eapply V293_target_wstate_star with (m2 := emp) (o1 := emp);
          [apply map_join_emp | apply map_join_comm; apply map_join_emp | exact HP | exact HA]. }
      clear HP HF HA. sep auto. }
  assert (HC : can_change_aop raw).
  { unfold raw, locals, base, fields, V293_shared_flags, V293_sched_globals, V293_prefix_bindings,
      V293_counter_bindings, V293_shared_fields, V293_inputs_full, Agvarmapsto, Aptrmapsto.
    cbn [can_change_aop]. repeat split; try exact I; intros; repeat split; try exact I;
      apply V293_array_aop_independent. }
  pose proof (@change_aop_rule _ _ _ (sched;;aop) _ HS HC) as HK. fold s in HK.
  assert (Hcounter : s |= (PV (12%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** Atrue).
  { unfold raw in HK. clear HP HA HF HS. sep auto. }
  split; [ | exact Hcounter].
  assert (HJ : s |= (CurTid V293_idle_tid ** CurTid V293_idle_tid) **
    ((locals ** fields) ** ((V293_inputs_full 1%positive 2%positive 3%positive 0 16 **
      ((PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0)) **
        V293_array true 8%positive 0 4 (Tptr Tvoid) (V293_current_mode_entries different))) **
      ((PV (12%positive, Int.zero) @ Tint32 |-> (Vint32 c)) **
        (GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)))))).
  { eapply astar_mono with (P := GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)).
    - intros st H. apply GV_separate_rw in H. unfold CurTid. sep auto.
    - intros st H; exact H.
    - clear HP HA HF HS Hcounter. unfold raw, base in HK. sep auto. }
  assert (HL : s |=
    (V293_storage_open 107%Z Tvoid V293_idle_tid (V293_current_mode_tasks different) events now V293_idle_tid **
      V293_prefix_entry_heap 1%positive 2%positive 3%positive 4%positive 8%positive Tvoid
        0 16 (V293_current_mode_entries different) [((12%positive, 0%Z), Tint32)] (V293_byteval 0)) **
      (CurTid V293_idle_tid ** ((Ais nil ** Acs nil) **
        ((V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
          V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive) **
          (V293_counter_bindings 108%Z 12%positive ** Aemp))))).
  { assert (HR : (PV (12%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ==>
      V293_storage ([((12%positive, 0%Z), Tint32)])).
    { intros st H. cbn [V293_storage]. apply astar_r_aemp_intro.
      unfold V293_storage_cell. exists (Vint32 c). sep auto. }
    clear HP HA HF HS HK Hcounter.
    unfold V293_storage_open, V293_prefix_entry_heap, locals, fields in *.
    assert (HT : s |= (PV (12%positive, Int.zero) @ Tint32 |-> (Vint32 c)) **
      ((CurTid V293_idle_tid ** CurTid V293_idle_tid) **
        ((locals ** fields) ** ((V293_inputs_full 1%positive 2%positive 3%positive 0 16 **
          ((PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0)) **
            V293_array true 8%positive 0 4 (Tptr Tvoid) (V293_current_mode_entries different))) **
          (GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)))))) by (unfold locals, fields; sep auto).
    eapply astar_mono in HT; [ | exact HR | intros st H; exact H].
    clear HJ. unfold locals, fields in HT. sep auto. }
  eapply astar_mono in HL.
  2: { apply V293_prefix_entry_close; try lia; [apply V293_byte_type; lia | exact Hptr]. }
  2: { intros st H; exact H. }
  apply astar_assoc_intro in HL.
  apply astar_l_aop'_intro with (aop := (sched;;aop)) in HL; [ | reflexivity].
  exact HL.
Qed.

Theorem V293_storage_connected_entry_witness : forall different c events now aop,
  exists s,
    V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
    V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
    V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
    Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) (V293_current_mode_entries different) /\
    s |= (V293_storage_prefix_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z
      1%positive 2%positive 3%positive 4%positive 8%positive 10%positive Tvoid 0 16
      (V293_current_mode_entries different) [((12%positive, 0%Z), Tint32)] V293_idle_tid
      (V293_current_mode_tasks different) events now (sched;;aop) nil nil
      (V293_counter_bindings 108%Z 12%positive ** Aemp) V293_idle_tid (V293_byteval 0)) //\\
      ((PV (12%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** Atrue).
Proof.
  intros different c events now aop.
  destruct (V293_storage_connected_entry_witness_empty_locals different c events now aop)
    as (s & Hb & Ht & Hcur & Hptr & Hle & Hs).
  exists s. split; [exact Hb | ]. split; [exact Ht | ].
  split; [exact Hcur | ]. split; [exact Hptr | ]. exact Hs.
Qed.

(* Exact physical current priority shares the layout with the retained prefix;
   both task modes are inhabited, without an extra private copy of this byte. *)
Definition V293_priority_fixture_ge : env :=
  set V293_prefix_fixture_ge 108%Z (12%positive, Tint8).
Definition V293_priority_fixture_memory (different : bool) :=
  V293_encoded_memory 12%positive 0 true
    (encode_val Tint8 (V293_byteval (V293_current_mode_priority different))).

Theorem V293_storage_priority_entry_witness : forall different events now aop,
  exists s,
    V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
    V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
    V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
    Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) (V293_current_mode_entries different) /\
    s |= V293_priority_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 108%Z
      1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 12%positive Tvoid 0 16
      (V293_current_mode_priority different) (V293_current_mode_entries different) nil V293_idle_tid
      (V293_current_mode_tasks different) events now (sched;;aop) nil nil Aemp
      V293_idle_tid (V293_byteval 0).
Proof.
  intros different events now aop.
  set (base := V293_inputs_full 1%positive 2%positive 3%positive 0 16 **
    (((PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0)) **
      V293_array true 8%positive 0 4 (Tptr Tvoid) (V293_current_mode_entries different)) **
      ((GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
        (GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid))))).
  set (fields := V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now).
  set (locals := V293_shared_flags ** ((Ais nil ** Acs nil) **
    ((V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
      V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive) **
      ((Agvarenv 108%Z Tint8 (12%positive, 0%Z) //\\ A_notin_lenv 108%Z) ** Aemp)))).
  set (raw := locals ** (base ** ((PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different))) ** fields))).
  set (M := merge (V293_storage_prefix_memory different) (V293_priority_fixture_memory different)).
  set (O := V293_shared_fixture_abs V293_idle_tid (V293_current_mode_tasks different) events now).
  set (s := ((V293_priority_fixture_ge, emp, M, (fun _ : hid => false),
    (false, nil, nil), O, (sched;;aop)) : RstateOP)).
  exists s. destruct (V293_current_mode_relations different) as [Hb [Ht Hcur]].
  split; [exact Hb | ]. split; [exact Ht | ]. split; [exact Hcur | ].
  assert (Hptr : Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true)
    (V293_current_mode_entries different)) by (destruct different; vm_compute; repeat constructor).
  split; [exact Hptr | ].
  assert (HP : V293_wstate V293_priority_fixture_ge emp M |=
    base ** (PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different)))).
  { eapply V293_wstate_star.
    - apply map_join_merge. apply map_disjoint. intros [b i].
      destruct (Pos.eq_dec b 12%positive); [subst b; left | right; left].
      + unfold V293_storage_prefix_memory. V293_storage_prefix_outside.
      + unfold V293_priority_fixture_memory. apply V293_encoded_memory_outside. left; congruence.
    - unfold base. apply V293_storage_prefix_physical_witness; vm_compute; reflexivity.
    - split; [apply V293_encoded_memory_mapsto | reflexivity]. }
  assert (HA : V293_target_wstate V293_priority_fixture_ge emp emp O |= fields).
  { unfold O, fields, V293_shared_fixture_abs, V293_shared_fields.
    repeat (eapply V293_target_wstate_star; [apply map_join_emp | apply map_join_merge;
      apply map_disjoint; intros key; destruct key; simpl; auto | split; reflexivity | ]).
    split; reflexivity. }
  assert (HF : V293_target_wstate V293_priority_fixture_ge emp emp emp |= locals).
  { unfold locals, V293_shared_flags.
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
      + intros [v H]; discriminate.
    - repeat split.
      + exists 12%positive. split; [vm_compute; reflexivity | ]. repeat split; reflexivity.
      + intros [v H]; discriminate.
    - split; reflexivity. }
  assert (HS : V293_target_wstate V293_priority_fixture_ge emp M O |= raw).
  { unfold raw. eapply V293_target_wstate_star with (m1 := emp) (o1 := emp).
    - apply map_join_comm. apply map_join_emp.
    - apply map_join_comm. apply map_join_emp.
    - exact HF.
    - assert (HK : V293_target_wstate V293_priority_fixture_ge emp M O |=
        (base ** (PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different)))) ** fields).
      { eapply V293_target_wstate_star with (m2 := emp) (o1 := emp);
          [apply map_join_emp | apply map_join_comm; apply map_join_emp | exact HP | exact HA]. }
      clear HP HF HA. sep auto. }
  assert (HC : can_change_aop raw).
  { unfold raw, locals, base, fields, V293_shared_flags, V293_sched_globals, V293_prefix_bindings,
      V293_shared_fields, V293_inputs_full, Agvarmapsto, Aptrmapsto.
    cbn [can_change_aop]. repeat split; try exact I; intros; repeat split; try exact I;
      apply V293_array_aop_independent. }
  pose proof (@change_aop_rule _ _ _ (sched;;aop) _ HS HC) as HK. fold s in HK.
  assert (HJ : s |= (CurTid V293_idle_tid ** CurTid V293_idle_tid) **
    ((locals ** fields) ** ((V293_inputs_full 1%positive 2%positive 3%positive 0 16 **
      ((PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0)) **
        V293_array true 8%positive 0 4 (Tptr Tvoid) (V293_current_mode_entries different))) **
      ((PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different))) **
        (GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)))))).
  { eapply astar_mono with (P := GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)).
    - intros st H. apply GV_separate_rw in H. unfold CurTid. sep auto.
    - intros st H; exact H.
    - clear HP HA HF HS. unfold raw, base in HK. sep auto. }
  assert (HL : s |=
    (V293_storage_open 107%Z Tvoid V293_idle_tid (V293_current_mode_tasks different) events now V293_idle_tid **
      V293_retained_prefix_entry_heap 1%positive 2%positive 3%positive 4%positive 8%positive Tvoid
        0 16 (V293_current_mode_entries different)
        ((PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different))) **
          V293_storage nil) (V293_byteval 0)) **
      (CurTid V293_idle_tid ** ((Ais nil ** Acs nil) **
        ((V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
          V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive) **
          ((Agvarenv 108%Z Tint8 (12%positive, 0%Z) //\\ A_notin_lenv 108%Z) ** Aemp))))).
  { clear HP HA HF HS HK. unfold V293_storage_open, V293_retained_prefix_entry_heap,
      locals, fields in *. cbn [V293_storage]. sep auto. }
  eapply astar_mono in HL.
  2: { apply V293_retained_prefix_entry_close with
      (rest := [((12%positive, 0%Z), Tint8)]); try lia.
    - change (V293_priority_kept 12%positive (V293_current_mode_priority different) nil ==>
        V293_storage ([((12%positive, 0%Z), Tint8)])).
      apply V293_priority_kept_erase. destruct different; simpl; lia.
    - apply V293_byte_type; lia.
    - exact Hptr. }
  2: { intros st H; exact H. }
  apply astar_assoc_intro in HL.
  apply astar_l_aop'_intro with (aop := (sched;;aop)) in HL; [ | reflexivity].
  exact HL.
Qed.

(* The same entry contains BOTH scalar blocks; no separate witnesses are conjoined. *)
Definition V293_conditional_fixture_ge : env :=
  set V293_priority_fixture_ge 109%Z (13%positive, Tint32).
Definition V293_conditional_priority_memory (different : bool) :=
  V293_encoded_memory 12%positive 0 true
    (encode_val Tint8 (V293_byteval (V293_current_mode_priority different))).
Definition V293_conditional_counter_memory c :=
  V293_encoded_memory 13%positive 0 true (encode_val Tint32 (Vint32 c)).

Definition V293_conditional_fixture_base different := V293_inputs_full 1%positive 2%positive 3%positive 0 16 **
    (((PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0)) **
      V293_array true 8%positive 0 4 (Tptr Tvoid) (V293_current_mode_entries different)) **
      ((GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) **
        (GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)))).

Lemma V293_conditional_fixture_physical : forall ge different n c,
  get ge OSTCBCur = Some (6%positive, Tptr Tvoid) ->
  get ge 107%Z = Some (10%positive, Tptr Tvoid) ->
  V293_wstate ge emp
    (merge (merge (V293_storage_prefix_memory different)
      (V293_encoded_memory 12%positive 0 true (encode_val Tint8 (V293_byteval n))))
      (V293_encoded_memory 13%positive 0 true (encode_val Tint32 (Vint32 c)))) |=
    (V293_conditional_fixture_base different **
      (PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval n))) **
      (PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)).
Proof.
  intros ge different n c Hcur Htarget.
  set (base := V293_conditional_fixture_base different).
  set (Mb := merge (V293_storage_prefix_memory different)
    (V293_encoded_memory 12%positive 0 true (encode_val Tint8 (V293_byteval n)))).
  set (M := merge Mb (V293_encoded_memory 13%positive 0 true (encode_val Tint32 (Vint32 c)))).
  assert (HP0 : V293_wstate ge emp Mb |=
    base ** (PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval n))).
  { eapply V293_wstate_star.
    - apply map_join_merge. apply map_disjoint. intros [b i].
      destruct (Pos.eq_dec b 12%positive); [subst b; left | right; left].
      + unfold V293_storage_prefix_memory. V293_storage_prefix_outside.
      + apply V293_encoded_memory_outside. left; congruence.
    - unfold base, V293_conditional_fixture_base. apply V293_storage_prefix_physical_witness; assumption.
    - split; [apply V293_encoded_memory_mapsto | reflexivity]. }
  assert (HP : V293_wstate ge emp M |=
    (base ** (PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval n))) **
      (PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c))).
  { eapply V293_wstate_star.
    - apply map_join_merge. apply map_disjoint. intros [b i].
      destruct (Pos.eq_dec b 13%positive); [subst b; left | right; left].
      + unfold Mb, V293_storage_prefix_memory.
        V293_storage_prefix_outside.
      + apply V293_encoded_memory_outside. left; congruence.
    - exact HP0.
    - split; [apply V293_encoded_memory_mapsto | reflexivity]. }
  exact HP.
Qed.

Theorem V293_storage_conditional_entry_witness : forall different c events now aop,
  exists s,
    V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
    V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
    V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
    Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) (V293_current_mode_entries different) /\
    s |= (V293_conditional_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 108%Z 109%Z
      1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 12%positive 13%positive Tvoid 0 16
      (V293_current_mode_priority different) (V293_current_mode_entries different) nil V293_idle_tid
      (V293_current_mode_tasks different) events now aop nil nil Aemp
      V293_idle_tid (V293_byteval 0)) //\\
      ((PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** Atrue).
Proof.
  intros different c events now aop.
  set (base := V293_conditional_fixture_base different).
  set (fields := V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now).
  set (locals := V293_shared_flags ** ((Ais nil ** Acs nil) **
    ((V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
      V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive) **
      (V293_counter_bindings 109%Z 13%positive **
        ((Agvarenv 108%Z Tint8 (12%positive, 0%Z) //\\ A_notin_lenv 108%Z) ** Aemp))))).
  set (raw := locals ** (base ** ((PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different))) **
    ((PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** fields)))).
  set (Mb := merge (V293_storage_prefix_memory different) (V293_conditional_priority_memory different)).
  set (M := merge Mb (V293_conditional_counter_memory c)).
  set (O := V293_shared_fixture_abs V293_idle_tid (V293_current_mode_tasks different) events now).
  set (s := ((V293_conditional_fixture_ge, emp, M, (fun _ : hid => false),
    (false, nil, nil), O, (sched;;aop)) : RstateOP)).
  exists s. destruct (V293_current_mode_relations different) as [Hb [Ht Hcur]].
  split; [exact Hb | ]. split; [exact Ht | ]. split; [exact Hcur | ].
  assert (Hptr : Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true)
    (V293_current_mode_entries different)) by (destruct different; vm_compute; repeat constructor).
  split; [exact Hptr | ].
  assert (HP : V293_wstate V293_conditional_fixture_ge emp M |=
    (base ** (PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different)))) **
      (PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c))).
  { (* Normalize the small scalar map BEFORE comparing the large merged map. *)
    assert (Epriority : V293_conditional_priority_memory different =
      V293_encoded_memory 12%positive 0 true
        (encode_val Tint8 (V293_byteval (V293_current_mode_priority different)))) by reflexivity.
    unfold M, Mb. rewrite Epriority. apply V293_conditional_fixture_physical; vm_compute; reflexivity. }
  assert (HA : V293_target_wstate V293_conditional_fixture_ge emp emp O |= fields).
  { unfold O, fields, V293_shared_fixture_abs, V293_shared_fields.
    repeat (eapply V293_target_wstate_star; [apply map_join_emp | apply map_join_merge;
      apply map_disjoint; intros key; destruct key; simpl; auto | split; reflexivity | ]).
    split; reflexivity. }
  assert (HF : V293_target_wstate V293_conditional_fixture_ge emp emp emp |= locals).
  { unfold locals, V293_shared_flags.
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
      + intros [v H]; discriminate.
    - unfold V293_counter_bindings. repeat split.
      + exists 13%positive. split; [vm_compute; reflexivity | ]. repeat split; reflexivity.
      + intros [v H]; discriminate.
    - repeat split.
      + exists 12%positive. split; [vm_compute; reflexivity | ]. repeat split; reflexivity.
      + intros [v H]; discriminate.
    - split; reflexivity. }
  assert (HS : V293_target_wstate V293_conditional_fixture_ge emp M O |= raw).
  { unfold raw. eapply V293_target_wstate_star with (m1 := emp) (o1 := emp).
    - apply map_join_comm. apply map_join_emp.
    - apply map_join_comm. apply map_join_emp.
    - exact HF.
    - assert (HK : V293_target_wstate V293_conditional_fixture_ge emp M O |=
        ((base ** (PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different)))) **
          (PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c))) ** fields).
      { eapply V293_target_wstate_star with (m2 := emp) (o1 := emp);
          [apply map_join_emp | apply map_join_comm; apply map_join_emp | exact HP | exact HA]. }
      clear HP HF HA. sep auto. }
  assert (HC : can_change_aop raw).
  { unfold raw, locals, base, V293_conditional_fixture_base, fields, V293_shared_flags, V293_sched_globals, V293_prefix_bindings,
      V293_shared_fields, V293_inputs_full, V293_counter_bindings, Agvarmapsto, Aptrmapsto.
    cbn [can_change_aop]. repeat split; try exact I; intros; repeat split; try exact I;
      apply V293_array_aop_independent. }
  pose proof (@change_aop_rule _ _ _ (sched;;aop) _ HS HC) as HK. fold s in HK.
  assert (Hcounter : s |= (PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** Atrue).
  { unfold raw in HK. clear HP HA HF HS. sep auto. }
  split; [ | exact Hcounter]. clear Hcounter.
  assert (HJ : s |= (CurTid V293_idle_tid ** CurTid V293_idle_tid) **
    ((locals ** fields) ** ((V293_inputs_full 1%positive 2%positive 3%positive 0 16 **
      ((PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0)) **
        V293_array true 8%positive 0 4 (Tptr Tvoid) (V293_current_mode_entries different))) **
      ((PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) **
        ((PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different))) **
        (GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid))))))).
  { eapply astar_mono with (P := GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)).
    - intros st H. apply GV_separate_rw in H. unfold CurTid. sep auto.
    - intros st H; exact H.
    - clear HP HA HF HS. unfold raw, base, V293_conditional_fixture_base in HK. sep auto. }
  assert (HL : s |=
    (V293_storage_open 107%Z Tvoid V293_idle_tid (V293_current_mode_tasks different) events now V293_idle_tid **
      V293_retained_prefix_entry_heap 1%positive 2%positive 3%positive 4%positive 8%positive Tvoid
        0 16 (V293_current_mode_entries different)
        (V293_storage_cell (13%positive, 0%Z) Tint32 **
          ((PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different))) **
            V293_storage nil)) (V293_byteval 0)) **
      (CurTid V293_idle_tid ** ((Ais nil ** Acs nil) **
        ((V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
          V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive) **
          (V293_counter_bindings 109%Z 13%positive **
        ((Agvarenv 108%Z Tint8 (12%positive, 0%Z) //\\ A_notin_lenv 108%Z) ** Aemp)))))).
  { assert (Htypedcounter : PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c) ==>
        V293_storage_cell (13%positive, 0%Z) Tint32).
    { intros st H. unfold V293_storage_cell. exists (Vint32 c). sep auto. }
    clear HP HA HF HS HK. unfold V293_storage_open, V293_retained_prefix_entry_heap,
      locals, fields in *. cbn [V293_storage].
    assert (HK : s |= (PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) **
      (V293_storage_open 107%Z Tvoid V293_idle_tid (V293_current_mode_tasks different) events now V293_idle_tid **
        ((V293_inputs_full 1%positive 2%positive 3%positive 0 16 **
          ((PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0)) **
            V293_array true 8%positive 0 4 (Tptr Tvoid) (V293_current_mode_entries different))) **
          ((PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different))) **
            (CurTid V293_idle_tid ** ((Ais nil ** Acs nil) **
              ((V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
                V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive) **
                (V293_counter_bindings 109%Z 13%positive **
                  ((Agvarenv 108%Z Tint8 (12%positive, 0%Z) //\\ A_notin_lenv 108%Z) ** Aemp)))))))))
      by (unfold V293_storage_open; sep auto).
    eapply astar_mono in HK; [ | exact Htypedcounter | intros st H; exact H]. clear HJ. unfold V293_storage_open in HK. sep auto. }
  eapply astar_mono in HL.
  2: { apply V293_retained_prefix_entry_close with
      (rest := [((13%positive, 0%Z), Tint32); ((12%positive, 0%Z), Tint8)]); try lia.
    - change (V293_conditional_kept 12%positive 13%positive (V293_current_mode_priority different) nil ==>
        V293_storage ([((13%positive, 0%Z), Tint32); ((12%positive, 0%Z), Tint8)])).
      apply V293_conditional_kept_erase. destruct different; simpl; lia.
    - apply V293_byte_type; lia.
    - exact Hptr. }
  2: { intros st H; exact H. }
  apply astar_assoc_intro in HL.
  apply astar_l_aop'_intro with (aop := (sched;;aop)) in HL; [ | reflexivity].
  exact HL.
Qed.

(* Accurate guard bytes live in the same shared memory as arrays and scalars. *)
Definition V293_guarded_fixture_ge : env :=
  set (set V293_conditional_fixture_ge 110%Z (14%positive, Tint8)) 111%Z (15%positive, Tint8).
Definition V293_guarded_interrupt_memory (ni : nat) :=
  V293_encoded_memory 14%positive 0 true (encode_val Tint8 (V293_byteval ni)).
Definition V293_guarded_lock_memory (nl : nat) :=
  V293_encoded_memory 15%positive 0 true (encode_val Tint8 (V293_byteval nl)).

Theorem V293_storage_guarded_entry_witness : forall different c ni nl events now aop,
  ni < 256 -> nl < 256 ->
  exists s,
    V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
    V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
    V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
    Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) (V293_current_mode_entries different) /\
    s |= (V293_storage_guarded_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 108%Z 109%Z 110%Z 111%Z
      1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 12%positive 13%positive 14%positive 15%positive
      Tvoid 0 16 (V293_current_mode_priority different) ni nl (V293_current_mode_entries different) nil V293_idle_tid
      (V293_current_mode_tasks different) events now aop nil nil Aemp
      V293_idle_tid (V293_byteval 0)) //\\
      ((PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** Atrue).
Proof.
  intros different c ni nl events now aop Hni Hnl.
  set (base := V293_conditional_fixture_base different).
  set (fields := V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now).
  set (gb := (Agvarenv 110%Z Tint8 (14%positive, 0%Z) //\\ A_notin_lenv 110%Z) **
    ((Agvarenv 111%Z Tint8 (15%positive, 0%Z) //\\ A_notin_lenv 111%Z) ** Aemp)).
  set (gf := (PV (14%positive, Int.zero) @ Tint8 |-> (V293_byteval ni)) **
    (PV (15%positive, Int.zero) @ Tint8 |-> (V293_byteval nl))).
  set (locals := V293_shared_flags ** ((Ais nil ** Acs nil) **
    ((V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
      V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive) **
      (V293_counter_bindings 109%Z 13%positive **
        ((Agvarenv 108%Z Tint8 (12%positive, 0%Z) //\\ A_notin_lenv 108%Z) ** gb))))).
  set (raw := locals ** (base ** ((PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different))) **
    ((PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** (gf ** fields))))).
  set (M0 := merge (merge (V293_storage_prefix_memory different) (V293_conditional_priority_memory different))
    (V293_conditional_counter_memory c)).
  set (Mg := merge (V293_guarded_interrupt_memory ni) (V293_guarded_lock_memory nl)).
  set (M := merge M0 Mg).
  set (O := V293_shared_fixture_abs V293_idle_tid (V293_current_mode_tasks different) events now).
  set (s := ((V293_guarded_fixture_ge, emp, M, (fun _ : hid => false),
    (false, nil, nil), O, (sched;;aop)) : RstateOP)).
  exists s. destruct (V293_current_mode_relations different) as [Hb [Ht Hcur]].
  split; [exact Hb | ]. split; [exact Ht | ]. split; [exact Hcur | ].
  assert (Hptr : Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true)
    (V293_current_mode_entries different)) by (destruct different; vm_compute; repeat constructor).
  split; [exact Hptr | ].
  assert (HP0 : V293_wstate V293_guarded_fixture_ge emp M0 |=
    (base ** (PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different)))) **
      (PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c))).
  { apply V293_conditional_fixture_physical; vm_compute; reflexivity. }
  assert (HG : V293_wstate V293_guarded_fixture_ge emp Mg |= gf).
  { eapply V293_wstate_star.
    - apply map_join_merge. apply map_disjoint. intros [b i].
      destruct (Pos.eq_dec b 14%positive); [subst b; right; left | left];
        unfold V293_guarded_interrupt_memory, V293_guarded_lock_memory;
        apply V293_encoded_memory_outside; left; congruence.
    - split; [apply V293_encoded_memory_mapsto | reflexivity].
    - split; [apply V293_encoded_memory_mapsto | reflexivity]. }
  assert (HP : V293_wstate V293_guarded_fixture_ge emp M |=
    ((base ** (PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different)))) **
      (PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c))) ** gf).
  { eapply V293_wstate_star.
    - apply map_join_merge. apply map_disjoint. intros [b i].
      destruct (Pos.eq_dec b 14%positive); [subst b; left | ];
      try (unfold M0, V293_conditional_priority_memory, V293_conditional_counter_memory,
        V293_storage_prefix_memory; V293_storage_prefix_outside).
      destruct (Pos.eq_dec b 15%positive); [subst b; left | right; left].
      + unfold M0, V293_conditional_priority_memory, V293_conditional_counter_memory,
          V293_storage_prefix_memory. V293_storage_prefix_outside.
      + unfold Mg, V293_guarded_interrupt_memory, V293_guarded_lock_memory.
        repeat rewrite map_merge_semp by reflexivity; repeat rewrite V293_encoded_memory_outside by (left; congruence); reflexivity.
    - exact HP0.
    - exact HG. }
  assert (HA : V293_target_wstate V293_guarded_fixture_ge emp emp O |= fields).
  { unfold O, fields, V293_shared_fixture_abs, V293_shared_fields.
    repeat (eapply V293_target_wstate_star; [apply map_join_emp | apply map_join_merge;
      apply map_disjoint; intros key; destruct key; simpl; auto | split; reflexivity | ]).
    split; reflexivity. }
  assert (HF : V293_target_wstate V293_guarded_fixture_ge emp emp emp |= locals).
  { unfold locals, gb, V293_shared_flags.
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
      + intros [v H]; discriminate.
    - unfold V293_counter_bindings. repeat split.
      + exists 13%positive. split; [vm_compute; reflexivity | ]. repeat split; reflexivity.
      + intros [v H]; discriminate.
    - repeat split.
      + exists 12%positive. split; [vm_compute; reflexivity | ]. repeat split; reflexivity.
      + intros [v H]; discriminate.
    - repeat split.
      + exists 14%positive. split; [vm_compute; reflexivity | ]. repeat split; reflexivity.
      + intros [v H]; discriminate.
    - repeat split.
      + exists 15%positive. split; [vm_compute; reflexivity | ]. repeat split; reflexivity.
      + intros [v H]; discriminate.
    - split; reflexivity. }
  assert (HS : V293_target_wstate V293_guarded_fixture_ge emp M O |= raw).
  { unfold raw. eapply V293_target_wstate_star with (m1 := emp) (o1 := emp).
    - apply map_join_comm. apply map_join_emp.
    - apply map_join_comm. apply map_join_emp.
    - exact HF.
    - assert (HK : V293_target_wstate V293_guarded_fixture_ge emp M O |=
        (((base ** (PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different)))) **
          (PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c))) ** gf) ** fields).
      { eapply V293_target_wstate_star with (m2 := emp) (o1 := emp);
          [apply map_join_emp | apply map_join_comm; apply map_join_emp | exact HP | exact HA]. }
      clear HP0 HG HP HF HA. sep auto. }
  assert (HC : can_change_aop raw).
  { unfold raw, locals, gb, gf, base, V293_conditional_fixture_base, fields, V293_shared_flags,
      V293_sched_globals, V293_prefix_bindings, V293_shared_fields, V293_inputs_full,
      V293_counter_bindings, Agvarmapsto, Aptrmapsto.
    cbn [can_change_aop]. repeat split; try exact I; intros; repeat split; try exact I;
      apply V293_array_aop_independent. }
  pose proof (@change_aop_rule _ _ _ (sched;;aop) _ HS HC) as HK. fold s in HK.
  clear HP0 HG HP HA HF HS.
  assert (Hcounter : s |= (PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** Atrue)
    by (unfold raw in HK; sep auto).
  split; [ | exact Hcounter]. clear Hcounter.
  unfold V293_storage_guarded_entry. split.
  2: { assert (HO : s |= gf ** (gb ** Atrue)) by (unfold raw, locals in HK; sep auto).
    eapply astar_mono in HO.
    2: { unfold gf. apply astar_mono; apply separate_rw2ro. }
    2: { intros st H; exact H. }
    clear HK. unfold gb, V293_guard_cell in *. cbn [addrval_to_addr] in HO. change (Int.unsigned Int.zero) with 0%Z in HO. sep auto. }
  assert (Hkeep : (PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) **
      ((PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different))) ** gf) ==>
    V293_conditional_kept 12%positive 13%positive (V293_current_mode_priority different)
      [((14%positive, 0%Z), Tint8); ((15%positive, 0%Z), Tint8)]).
  { unfold V293_conditional_kept, V293_priority_kept. apply astar_mono.
    - intros st H. unfold V293_storage_cell. exists (Vint32 c). sep auto.
    - apply astar_mono; [intros st H; exact H | ].
      unfold gf. cbn [V293_storage]. intros st H.
      assert (HT : (PV (14%positive, Int.zero) @ Tint8 |-> (V293_byteval ni)) **
        (PV (15%positive, Int.zero) @ Tint8 |-> (V293_byteval nl)) ==>
        V293_storage_cell (14%positive, 0%Z) Tint8 ** V293_storage_cell (15%positive, 0%Z) Tint8).
      { apply astar_mono; intros st0 H0; unfold V293_storage_cell.
        - exists (V293_byteval ni). pose proof (V293_byte_type ni Hni). sep auto.
        - exists (V293_byteval nl). pose proof (V293_byte_type nl Hnl). sep auto. }
      apply HT in H. clear HT. sep auto. }
  assert (HJ : s |=
    ((PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) **
      ((PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different))) ** gf)) **
    (base ** (locals ** fields))) by (unfold raw in HK; sep auto).
  eapply astar_mono in HJ; [ | exact Hkeep | intros st H; exact H]. clear HK.
  assert (HL : s |=
    (V293_storage_open 107%Z Tvoid V293_idle_tid (V293_current_mode_tasks different) events now V293_idle_tid **
      V293_retained_prefix_entry_heap 1%positive 2%positive 3%positive 4%positive 8%positive Tvoid
        0 16 (V293_current_mode_entries different)
        (V293_conditional_kept 12%positive 13%positive (V293_current_mode_priority different)
          [((14%positive, 0%Z), Tint8); ((15%positive, 0%Z), Tint8)]) (V293_byteval 0)) **
      (CurTid V293_idle_tid ** ((Ais nil ** Acs nil) **
        ((V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
          V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive) **
          (V293_counter_bindings 109%Z 13%positive **
            ((Agvarenv 108%Z Tint8 (12%positive, 0%Z) //\\ A_notin_lenv 108%Z) ** gb)))))).
  { assert (HS : s |= (CurTid V293_idle_tid ** CurTid V293_idle_tid) **
      ((V293_conditional_kept 12%positive 13%positive (V293_current_mode_priority different)
          [((14%positive, 0%Z), Tint8); ((15%positive, 0%Z), Tint8)]) **
        ((V293_inputs_full 1%positive 2%positive 3%positive 0 16 **
          ((PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0)) **
            V293_array true 8%positive 0 4 (Tptr Tvoid) (V293_current_mode_entries different))) **
          ((GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) ** (locals ** fields))))).
    { eapply astar_mono with (P := GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)).
      - intros st H. apply GV_separate_rw in H. unfold CurTid. sep auto.
      - intros st H; exact H.
      - unfold base, V293_conditional_fixture_base in HJ. sep auto. }
    clear HJ. unfold V293_storage_open, V293_retained_prefix_entry_heap, locals, fields in *. sep auto. }
  eapply astar_mono in HL.
  2: { apply V293_retained_prefix_entry_close with
      (rest := [((13%positive, 0%Z), Tint32); ((12%positive, 0%Z), Tint8);
        ((14%positive, 0%Z), Tint8); ((15%positive, 0%Z), Tint8)]); try lia.
    - apply V293_conditional_kept_erase. destruct different; simpl; lia.
    - apply V293_byte_type; lia.
    - exact Hptr. }
  2: { intros st H; exact H. }
  apply astar_assoc_intro in HL.
  apply astar_l_aop'_intro with (aop := (sched;;aop)) in HL; [ | reflexivity]. exact HL.
Qed.

(* SAME physical entry, with ready relation; the exact counter observation is
   retained on that same state, for both task modes and arbitrary UINT32. *)
Lemma V293_ready_connected_entry_witness_empty_locals : forall different c events now aop,
  exists s,
    V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
    V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
    V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
    Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) (V293_current_mode_entries different) /\
    getlenv s = emp /\
    s |= (V293_ready_connected_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 108%Z
      1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 12%positive Tvoid 0 16
      (V293_current_mode_entries different) nil V293_idle_tid
      (V293_current_mode_tasks different) events now aop nil nil Aemp (Vptr V293_idle_tid) (V293_byteval 0)) //\\
      ((PV (12%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** Atrue).
Proof.
  intros different c events now aop.
  destruct (V293_storage_connected_entry_witness_empty_locals different c events now aop)
    as (s & Hb & Ht & Hcur & Hptr & Hle & Hs & Hcounter).
  exists s. split; [exact Hb | ]. split; [exact Ht | ].
  split; [exact Hcur | ]. split; [exact Hptr | ]. split; [exact Hle | ]. split; [ | exact Hcounter].
  assert (Hr : exists p, V293_bitmap_ready 0 16 p).
  { exists 12. right. split; [lia | ]. split; [lia | vm_compute; reflexivity]. }
  assert (Hhv : rule_type_val_match Tint8 (V293_byteval 0) = true)
    by (apply V293_byte_type; lia).
  assert (HC :
    ((V293_shared_flags **
      ((CurTid V293_idle_tid ** V293_shared_fields V293_idle_tid
        (V293_current_mode_tasks different) events now) **
        (GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)))) **
      V293_retained_prefix_entry_heap 1%positive 2%positive 3%positive 4%positive 8%positive
        Tvoid 0 16 (V293_current_mode_entries different)
        (V293_storage ([((12%positive, 0%Z), Tint32)])) (V293_byteval 0)) ==>
    SWINV (V293_ready_inv 1%positive 2%positive 3%positive 4%positive 8%positive Tvoid
      [((12%positive, 0%Z), Tint32)] 107%Z)).
  { intros st H. apply V293_ready_switch_close.
    unfold V293_ready_core, V293_ready_resources, V293_dispatch_cell,
      V293_retained_prefix_entry_heap in *.
    sep auto. repeat first [assumption | split | lia | reflexivity]. }
  unfold V293_storage_prefix_entry in Hs.
  unfold V293_ready_connected_entry.
  eapply astar_mono in Hs; [ | intros st H; exact H | apply astar_mono].
  2: { apply astar_mono with
      (P' := SWINV (V293_ready_inv 1%positive 2%positive 3%positive 4%positive 8%positive
          Tvoid [((12%positive, 0%Z), Tint32)] 107%Z) //\\
        ((V293_shared_flags ** ((CurTid V293_idle_tid **
          V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now) **
          (GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)))) **
          V293_retained_prefix_entry_heap 1%positive 2%positive 3%positive 4%positive 8%positive
            Tvoid 0 16 (V293_current_mode_entries different)
            (V293_storage ([((12%positive, 0%Z), Tint32)])) (V293_byteval 0)));
      [ | intros st H; exact H].
    intros st [_ H]. unfold V293_storage_open, V293_prefix_entry_heap in H.
    exact (conj (HC st H) H). }
  2: { intros st H; exact H. }
  exact Hs.
Qed.

Theorem V293_ready_connected_entry_witness : forall different c events now aop,
  exists s,
    V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
    V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
    V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
    Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) (V293_current_mode_entries different) /\
    s |= (V293_ready_connected_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 108%Z
      1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 12%positive Tvoid 0 16
      (V293_current_mode_entries different) nil V293_idle_tid
      (V293_current_mode_tasks different) events now aop nil nil Aemp (Vptr V293_idle_tid) (V293_byteval 0)) //\\
      ((PV (12%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** Atrue).
Proof.
  intros different c events now aop.
  destruct (V293_ready_connected_entry_witness_empty_locals different c events now aop)
    as (s & Hb & Ht & Hcur & Hptr & Hle & Hs).
  exists s. split; [exact Hb | ]. split; [exact Ht | ].
  split; [exact Hcur | ]. split; [exact Hptr | ]. exact Hs.
Qed.

(* Reuse the SAME two-mode fixture, including accurate current byte and counter.
   Hcur is an explicit local-entry fact, not derived from readyI preservation. *)
Theorem V293_ready_conditional_entry_witness : forall different c events now aop,
  exists s,
    V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
    V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
    V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
    Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) (V293_current_mode_entries different) /\
    s |= (V293_ready_conditional_entry 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 108%Z 109%Z
      1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 12%positive 13%positive Tvoid 0 16
      (V293_current_mode_priority different) (V293_current_mode_entries different) nil V293_idle_tid
      (V293_current_mode_tasks different) events now aop nil nil Aemp
      (Vptr V293_idle_tid) (V293_byteval 0)) //\\
      ((PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** Atrue).
Proof.
  intros different c events now aop.
  destruct (V293_storage_conditional_entry_witness different c events now aop)
    as (s & Hb & Ht & Hcur & Hptr & Hs & Hcounter).
  exists s. split; [exact Hb | ]. split; [exact Ht | ].
  split; [exact Hcur | ]. split; [exact Hptr | ]. split; [ | exact Hcounter].
  assert (Hr : exists p, V293_bitmap_ready 0 16 p).
  { exists 12. right. split; [lia | ]. split; [lia | vm_compute; reflexivity]. }
  set (extra := [((13%positive, 0%Z), Tint32); ((12%positive, 0%Z), Tint8)]).
  set (kept := V293_conditional_kept 12%positive 13%positive (V293_current_mode_priority different) nil).
  assert (HK : kept ==> V293_storage extra).
  { apply V293_conditional_kept_erase. destruct different; simpl; lia. }
  assert (HC :
    (V293_storage_open 107%Z Tvoid V293_idle_tid (V293_current_mode_tasks different)
      events now V293_idle_tid **
      V293_retained_prefix_entry_heap 1%positive 2%positive 3%positive 4%positive 8%positive
        Tvoid 0 16 (V293_current_mode_entries different) kept (V293_byteval 0)) ==>
    SWINV (V293_ready_inv 1%positive 2%positive 3%positive 4%positive 8%positive Tvoid extra 107%Z)).
  { intros st H. unfold V293_retained_prefix_entry_heap in H.
    eapply astar_mono in H; [ | intros st0 H0; exact H0 | apply astar_mono;
      [intros st0 H0; exact H0 | apply astar_mono;
        [intros st0 H0; exact H0 | apply astar_mono; [intros st0 H0; exact H0 | exact HK]]]].
    apply V293_ready_switch_close.
    unfold V293_storage_open, V293_ready_core, V293_ready_resources,
      V293_dispatch_cell, V293_retained_prefix_entry_heap in *.
    sep auto. repeat first [assumption | split | lia | reflexivity]. }
  unfold V293_conditional_entry, V293_retained_storage_prefix_entry in Hs.
  unfold V293_ready_conditional_entry.
  eapply astar_mono in Hs; [ | intros st H; exact H | apply astar_mono].
  2: { apply astar_mono with
      (P' := SWINV (V293_ready_inv 1%positive 2%positive 3%positive 4%positive 8%positive Tvoid extra 107%Z) //\\
        (V293_storage_open 107%Z Tvoid V293_idle_tid (V293_current_mode_tasks different)
          events now V293_idle_tid **
          V293_retained_prefix_entry_heap 1%positive 2%positive 3%positive 4%positive 8%positive
            Tvoid 0 16 (V293_current_mode_entries different) kept (V293_byteval 0)));
      [ | intros st H; exact H].
    intros st [_ H]. exact (conj (HC st H) H). }
  2: { intros st H; exact H. }
  exact Hs.
Qed.

(* Both modes, arbitrary legal guard bytes and counter, all in ONE physical
   entry. The cache observation is accurate HERE, not across a switch. The
   private frame owns bindings/no-shadow facts only, never guard/cache bytes.
   This is a fixture, not initialization or reachability from OSStart. *)
Theorem V293_ready_guard_entry_witness : forall different c ni nl events now aop,
  ni < 256 -> nl < 256 ->
  exists s,
    V293_bitmap_tasks 0 16 (V293_current_mode_tasks different) /\
    V293_priority_table (V293_current_mode_entries different) (V293_current_mode_tasks different) /\
    V293_current_task (V293_current_mode_tasks different) V293_idle_tid (V293_current_mode_priority different) /\
    Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true) (V293_current_mode_entries different) /\
    getlenv s = emp /\
    s |= (V293_ready_guard_observed 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 109%Z 110%Z 111%Z
      1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 13%positive 14%positive 15%positive
      Tvoid [((12%positive, 0%Z), Tint8)] V293_idle_tid aop nil nil
      ((Agvarenv 108%Z Tint8 (12%positive, 0%Z) //\\ A_notin_lenv 108%Z) ** A_notin_lenv OSTCBCur) ni nl) //\\
      (((PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) **
        (PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different)))) **
        (V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now ** Atrue)).
Proof.
  intros different c ni nl events now aop Hni Hnl.
  set (base := V293_conditional_fixture_base different).
  set (fields := V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now).
  set (gb := (Agvarenv 110%Z Tint8 (14%positive, 0%Z) //\\ A_notin_lenv 110%Z) **
    ((Agvarenv 111%Z Tint8 (15%positive, 0%Z) //\\ A_notin_lenv 111%Z) ** Aemp)).
  set (gf := (PV (14%positive, Int.zero) @ Tint8 |-> (V293_byteval ni)) **
    (PV (15%positive, Int.zero) @ Tint8 |-> (V293_byteval nl))).
  set (locals := V293_shared_flags ** ((Ais nil ** Acs nil) **
    ((V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
      V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive) **
      (V293_counter_bindings 109%Z 13%positive **
        ((Agvarenv 108%Z Tint8 (12%positive, 0%Z) //\\ A_notin_lenv 108%Z) ** (gb ** A_notin_lenv OSTCBCur)))))).
  set (raw := locals ** (base ** ((PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different))) **
    ((PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) ** (gf ** fields))))).
  set (M0 := merge (merge (V293_storage_prefix_memory different) (V293_conditional_priority_memory different))
    (V293_conditional_counter_memory c)).
  set (Mg := merge (V293_guarded_interrupt_memory ni) (V293_guarded_lock_memory nl)).
  set (M := merge M0 Mg).
  set (O := V293_shared_fixture_abs V293_idle_tid (V293_current_mode_tasks different) events now).
  set (s := ((V293_guarded_fixture_ge, emp, M, (fun _ : hid => false),
    (false, nil, nil), O, (sched;;aop)) : RstateOP)).
  exists s. destruct (V293_current_mode_relations different) as [Hb [Ht Hcur]].
  split; [exact Hb | ]. split; [exact Ht | ]. split; [exact Hcur | ].
  assert (Hptr : Forall (fun v => rule_type_val_match (Tptr Tvoid) v = true)
    (V293_current_mode_entries different)) by (destruct different; vm_compute; repeat constructor).
  split; [exact Hptr | ]. split; [reflexivity | ].
  assert (HP0 : V293_wstate V293_guarded_fixture_ge emp M0 |=
    (base ** (PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different)))) **
      (PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c))).
  { apply V293_conditional_fixture_physical; vm_compute; reflexivity. }
  assert (HG : V293_wstate V293_guarded_fixture_ge emp Mg |= gf).
  { eapply V293_wstate_star.
    - apply map_join_merge. apply map_disjoint. intros [b i].
      destruct (Pos.eq_dec b 14%positive); [subst b; right; left | left];
        unfold V293_guarded_interrupt_memory, V293_guarded_lock_memory;
        apply V293_encoded_memory_outside; left; congruence.
    - split; [apply V293_encoded_memory_mapsto | reflexivity].
    - split; [apply V293_encoded_memory_mapsto | reflexivity]. }
  assert (HP : V293_wstate V293_guarded_fixture_ge emp M |=
    ((base ** (PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different)))) **
      (PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c))) ** gf).
  { eapply V293_wstate_star.
    - apply map_join_merge. apply map_disjoint. intros [b i].
      destruct (Pos.eq_dec b 14%positive); [subst b; left | ];
      try (unfold M0, V293_conditional_priority_memory, V293_conditional_counter_memory,
        V293_storage_prefix_memory; V293_storage_prefix_outside).
      destruct (Pos.eq_dec b 15%positive); [subst b; left | right; left].
      + unfold M0, V293_conditional_priority_memory, V293_conditional_counter_memory,
          V293_storage_prefix_memory. V293_storage_prefix_outside.
      + unfold Mg, V293_guarded_interrupt_memory, V293_guarded_lock_memory.
        repeat rewrite map_merge_semp by reflexivity; repeat rewrite V293_encoded_memory_outside by (left; congruence); reflexivity.
    - exact HP0.
    - exact HG. }
  assert (HA : V293_target_wstate V293_guarded_fixture_ge emp emp O |= fields).
  { unfold O, fields, V293_shared_fixture_abs, V293_shared_fields.
    repeat (eapply V293_target_wstate_star; [apply map_join_emp | apply map_join_merge;
      apply map_disjoint; intros key; destruct key; simpl; auto | split; reflexivity | ]).
    split; reflexivity. }
  assert (HF : V293_target_wstate V293_guarded_fixture_ge emp emp emp |= locals).
  { unfold locals, gb, V293_shared_flags.
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
      + intros [v H]; discriminate.
    - unfold V293_counter_bindings. repeat split.
      + exists 13%positive. split; [vm_compute; reflexivity | ]. repeat split; reflexivity.
      + intros [v H]; discriminate.
    - repeat split.
      + exists 12%positive. split; [vm_compute; reflexivity | ]. repeat split; reflexivity.
      + intros [v H]; discriminate.
    - repeat split.
      + exists 14%positive. split; [vm_compute; reflexivity | ]. repeat split; reflexivity.
      + intros [v H]; discriminate.
    - repeat split.
      + exists 15%positive. split; [vm_compute; reflexivity | ]. repeat split; reflexivity.
      + intros [v H]; discriminate.
    - split; reflexivity.
    - repeat split. intros [v H]; discriminate. }
  assert (HS : V293_target_wstate V293_guarded_fixture_ge emp M O |= raw).
  { unfold raw. eapply V293_target_wstate_star with (m1 := emp) (o1 := emp).
    - apply map_join_comm. apply map_join_emp.
    - apply map_join_comm. apply map_join_emp.
    - exact HF.
    - assert (HK : V293_target_wstate V293_guarded_fixture_ge emp M O |=
        (((base ** (PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different)))) **
          (PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c))) ** gf) ** fields).
      { eapply V293_target_wstate_star with (m2 := emp) (o1 := emp);
          [apply map_join_emp | apply map_join_comm; apply map_join_emp | exact HP | exact HA]. }
      clear HP0 HG HP HF HA. sep auto. }
  assert (HC : can_change_aop raw).
  { unfold raw, locals, gb, gf, base, V293_conditional_fixture_base, fields, V293_shared_flags,
      V293_sched_globals, V293_prefix_bindings, V293_shared_fields, V293_inputs_full,
      V293_counter_bindings, Agvarmapsto, Aptrmapsto.
    cbn [can_change_aop]. repeat split; try exact I; intros; repeat split; try exact I;
      apply V293_array_aop_independent. }
  pose proof (@change_aop_rule _ _ _ (sched;;aop) _ HS HC) as HK. fold s in HK.
  clear HP0 HG HP HA HF HS.
  assert (Hobservations : s |=
    ((PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) **
      (PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different)))) **
        (V293_shared_fields V293_idle_tid (V293_current_mode_tasks different) events now ** Atrue))
    by (unfold raw, fields in HK; sep auto).
  split; [ | exact Hobservations]. clear Hobservations.
  unfold V293_ready_guard_observed. split.
  2: { assert (HO : s |= gf ** (gb ** Atrue)) by (unfold raw, locals in HK; sep auto).
    eapply astar_mono in HO.
    2: { unfold gf. apply astar_mono; apply separate_rw2ro. }
    2: { intros st H; exact H. }
    clear HK. unfold gb, V293_guard_cell in *. cbn [addrval_to_addr] in HO.
    change (Int.unsigned Int.zero) with 0%Z in HO. sep auto. }
  assert (Hkeep : (PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) **
      ((PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different))) ** gf) ==>
    V293_conditional_kept 12%positive 13%positive (V293_current_mode_priority different)
      [((14%positive, 0%Z), Tint8); ((15%positive, 0%Z), Tint8)]).
  { unfold V293_conditional_kept, V293_priority_kept. apply astar_mono.
    - intros st H. unfold V293_storage_cell. exists (Vint32 c). sep auto.
    - apply astar_mono; [intros st H; exact H | ].
      unfold gf. cbn [V293_storage]. intros st H.
      assert (HT : (PV (14%positive, Int.zero) @ Tint8 |-> (V293_byteval ni)) **
        (PV (15%positive, Int.zero) @ Tint8 |-> (V293_byteval nl)) ==>
        V293_storage_cell (14%positive, 0%Z) Tint8 ** V293_storage_cell (15%positive, 0%Z) Tint8).
      { apply astar_mono; intros st0 H0; unfold V293_storage_cell.
        - exists (V293_byteval ni). pose proof (V293_byte_type ni Hni). sep auto.
        - exists (V293_byteval nl). pose proof (V293_byte_type nl Hnl). sep auto. }
      apply HT in H. clear HT. sep auto. }
  assert (HJ : s |=
    ((PV (13%positive, Int.zero) @ Tint32 |-> (Vint32 c)) **
      ((PV (12%positive, Int.zero) @ Tint8 |-> (V293_byteval (V293_current_mode_priority different))) ** gf)) **
    (base ** (locals ** fields))) by (unfold raw in HK; sep auto).
  eapply astar_mono in HJ; [ | exact Hkeep | intros st H; exact H]. clear HK.
  assert (HL : s |=
    (V293_storage_open 107%Z Tvoid V293_idle_tid (V293_current_mode_tasks different) events now V293_idle_tid **
      V293_retained_prefix_entry_heap 1%positive 2%positive 3%positive 4%positive 8%positive Tvoid
        0 16 (V293_current_mode_entries different)
        (V293_conditional_kept 12%positive 13%positive (V293_current_mode_priority different)
          [((14%positive, 0%Z), Tint8); ((15%positive, 0%Z), Tint8)]) (V293_byteval 0)) **
      (CurTid V293_idle_tid ** ((Ais nil ** Acs nil) **
        ((V293_sched_globals 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive **
          V293_prefix_bindings 106%Z 103%Z 107%Z Tvoid 8%positive 10%positive) **
          (V293_counter_bindings 109%Z 13%positive **
            ((Agvarenv 108%Z Tint8 (12%positive, 0%Z) //\\ A_notin_lenv 108%Z) ** (gb ** A_notin_lenv OSTCBCur))))))).
  { assert (HS : s |= (CurTid V293_idle_tid ** CurTid V293_idle_tid) **
      ((V293_conditional_kept 12%positive 13%positive (V293_current_mode_priority different)
          [((14%positive, 0%Z), Tint8); ((15%positive, 0%Z), Tint8)]) **
        ((V293_inputs_full 1%positive 2%positive 3%positive 0 16 **
          ((PV (4%positive, Int.zero) @ Tint8 |-> (V293_byteval 0)) **
            V293_array true 8%positive 0 4 (Tptr Tvoid) (V293_current_mode_entries different))) **
          ((GV 107%Z @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)) ** (locals ** fields))))).
    { eapply astar_mono with (P := GV OSTCBCur @ (Tptr Tvoid) |-> (Vptr V293_idle_tid)).
      - intros st H. apply GV_separate_rw in H. unfold CurTid. sep auto.
      - intros st H; exact H.
      - unfold base, V293_conditional_fixture_base in HJ. sep auto. }
    clear HJ. unfold V293_storage_open, V293_retained_prefix_entry_heap, locals, fields in *. sep auto. }
  assert (HR : exists p, V293_bitmap_ready 0 16 p).
  { exists 12. right. split; [lia | ]. split; [lia | vm_compute; reflexivity]. }
  assert (Hclose :
    (V293_storage_open 107%Z Tvoid V293_idle_tid (V293_current_mode_tasks different) events now V293_idle_tid **
      V293_retained_prefix_entry_heap 1%positive 2%positive 3%positive 4%positive 8%positive Tvoid
        0 16 (V293_current_mode_entries different)
        (V293_conditional_kept 12%positive 13%positive (V293_current_mode_priority different)
          [((14%positive, 0%Z), Tint8); ((15%positive, 0%Z), Tint8)]) (V293_byteval 0)) ==>
    V293_shared_flags **
      V293_ready_snapshot 1%positive 2%positive 3%positive 4%positive 8%positive Tvoid
        [((13%positive, 0%Z), Tint32); ((14%positive, 0%Z), Tint8);
         ((15%positive, 0%Z), Tint8); ((12%positive, 0%Z), Tint8)] 107%Z).
  { intros st H. unfold V293_retained_prefix_entry_heap in H.
    eapply astar_mono in H; [ | intros st0 H0; exact H0 | apply astar_mono;
      [intros st0 H0; exact H0 | apply astar_mono;
        [intros st0 H0; exact H0 | apply astar_mono; [intros st0 H0; exact H0 | ]]]].
    2: { apply V293_conditional_kept_erase. destruct different; simpl; lia. }
    unfold V293_ready_snapshot, V293_storage_open, V293_dispatch_cell,
      V293_retained_prefix_entry_heap in *.
    sep auto. repeat first [assumption | split | lia | reflexivity].
    cbn [V293_storage] in *. sep auto.
    repeat first [assumption | split | lia | reflexivity]. }
  eapply astar_mono in HL; [ | exact Hclose | intros st H; exact H].
  apply astar_l_aop'_intro with (aop := (sched;;aop)) in HL; [ | reflexivity].
  unfold V293_ready_guard_open, V293_ready_prefix_open, gb in *.
  sep auto.
Qed.
