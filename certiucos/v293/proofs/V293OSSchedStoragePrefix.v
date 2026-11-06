(* Opened physical resources for the real call/assignment prefix. Read halves
   are borrowed, retained, and reunited before the storage invariant closes.
   This is NOT the guarded full OS_Sched body or an initialization theorem. *)
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedDispatchShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchPre.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia Coq.Logic.Classical_Prop.
Import ListNotations.
Local Open Scope nat_scope.

Fixpoint V293_array (writable : bool) (b : block) (offset step : Z)
    (tau : type) (vs : list val) : asrt :=
  match vs with
  | nil => Aemp
  | v :: tail => Amapsto (b, offset) tau writable v **
      V293_array writable b (offset + step)%Z step tau tail
  end.
Fixpoint V293_array_cells (b : block) (offset step : Z) (tau : type) (n : nat) :=
  match n with
  | O => nil
  | S n' => ((b, offset), tau) :: V293_array_cells b (offset + step)%Z step tau n'
  end.
Lemma V293_array_good : forall w b offset step tau vs,
  GoodFrm (V293_array w b offset step tau vs).
Proof. intros w b offset step tau vs. revert offset. induction vs; intros; simpl; auto. Qed.
Lemma V293_array_borrow : forall b offset step tau vs,
  V293_array true b offset step tau vs ==>
  V293_array false b offset step tau vs ** V293_array false b offset step tau vs.
Proof.
  intros b offset step tau vs. revert offset. induction vs as [ | v tail IH]; intros offset s Hs; cbn [V293_array] in *.
  - sep auto.
  - eapply astar_mono in Hs; [ | apply separate_rw2ro | apply IH]. sep auto.
Qed.
Lemma V293_array_reunite : forall b offset step tau vs,
  V293_array false b offset step tau vs ** V293_array false b offset step tau vs ==>
  V293_array true b offset step tau vs.
Proof.
  intros b offset step tau vs. revert offset. induction vs as [ | v tail IH]; intros offset s Hs; cbn [V293_array] in *.
  - sep auto.
  - assert (HP : s |=
      (Amapsto (b, offset) tau false v ** Amapsto (b, offset) tau false v) **
      (V293_array false b (offset + step)%Z step tau tail **
       V293_array false b (offset + step)%Z step tau tail)) by (sep auto).
    eapply astar_mono; [apply combine_ro2rw_p1 | apply IH | exact HP].
Qed.
Lemma V293_array_to_storage : forall b offset step tau vs,
  Forall (fun v => rule_type_val_match tau v = true) vs ->
  V293_array true b offset step tau vs ==>
  V293_storage (V293_array_cells b offset step tau (length vs)).
Proof.
  intros b offset step tau vs HT. revert offset.
  induction HT as [ | v vs Hv HT IH]; intros offset s Hs; cbn [V293_array V293_array_cells length V293_storage] in *; [exact Hs | ].
  eapply astar_mono; [ | apply IH | exact Hs].
  intros st H. unfold V293_storage_cell. exists v. sep auto.
Qed.
Lemma V293_storage_frame_good : forall cells, GoodFrm (V293_storage cells).
Proof.
  induction cells as [ | [a tau] tail IH]; cbn [V293_storage]; [exact I | ].
  unfold V293_storage_cell. simpl. auto.
Qed.
Lemma V293_storage_append : forall left right,
  V293_storage left ** V293_storage right ==> V293_storage (left ++ right).
Proof.
  induction left as [ | [a tau] tail IH]; intros right s Hs; cbn [V293_storage app] in *.
  - apply astar_l_aemp_elim in Hs. exact Hs.
  - assert (HP : s |= V293_storage_cell a tau ** (V293_storage tail ** V293_storage right)) by (sep auto).
    eapply astar_mono; [intros st Hz; exact Hz | apply IH | exact HP].
Qed.
Lemma V293_read_bytes_array : forall b offset vs,
  V293_read_bytes b offset vs = V293_array false b offset 1 Tint8 (map V293_byteval vs).
Proof. intros b offset vs. revert offset. induction vs; intros; simpl; [reflexivity | rewrite IHvs; reflexivity]. Qed.
Lemma V293_read_pointers_array : forall tp b offset vs,
  V293_read_pointers tp b offset vs = V293_array false b offset 4 (Tptr tp) vs.
Proof. intros tp b offset vs. revert offset. induction vs; intros; simpl; [reflexivity | rewrite IHvs; reflexivity]. Qed.

Definition V293_inputs_full bt bg br lo hi :=
  (V293_array true bt 0 1 Tint8 (map V293_byteval V293_ready_table) **
   V293_array true br 0 1 Tint8 (map V293_byteval [lo;hi])) **
  Amapsto (bg, 0%Z) Tint8 true (V293_byteval (V293_ready_group lo hi)).
Definition V293_input_cells bt bg br :=
  V293_array_cells bt 0 1 Tint8 (length V293_ready_table) ++
  V293_array_cells br 0 1 Tint8 2 ++ [((bg, 0%Z), Tint8)].
Lemma V293_inputs_borrow : forall bt bg br lo hi,
  V293_inputs_full bt bg br lo hi ==>
  V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi) **
  V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi).
Proof.
  intros bt bg br lo hi s Hs.
  unfold V293_inputs_full, V293_sched_inputs in *.
  repeat rewrite V293_read_bytes_array.
  eapply astar_mono in Hs; [ | apply astar_mono; apply V293_array_borrow | apply separate_rw2ro].
  sep auto.
Qed.
Lemma V293_inputs_reunite : forall bt bg br lo hi,
  V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi) **
  V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi) ==>
  V293_inputs_full bt bg br lo hi.
Proof.
  intros bt bg br lo hi s Hs.
  unfold V293_inputs_full, V293_sched_inputs in *.
  repeat rewrite V293_read_bytes_array in Hs.
  assert (HP : s |=
    ((V293_array false bt 0 1 Tint8 (map V293_byteval V293_ready_table) **
      V293_array false bt 0 1 Tint8 (map V293_byteval V293_ready_table)) **
     (V293_array false br 0 1 Tint8 (map V293_byteval [lo;hi]) **
      V293_array false br 0 1 Tint8 (map V293_byteval [lo;hi]))) **
    (Amapsto (bg, 0%Z) Tint8 false (V293_byteval (V293_ready_group lo hi)) **
     Amapsto (bg, 0%Z) Tint8 false (V293_byteval (V293_ready_group lo hi)))) by (sep auto).
  eapply astar_mono; [apply astar_mono; apply V293_array_reunite | apply combine_ro2rw_p1 | exact HP].
Qed.
Lemma V293_inputs_to_storage : forall bt bg br lo hi,
  lo < 256 -> hi < 256 ->
  V293_inputs_full bt bg br lo hi ==> V293_storage (V293_input_cells bt bg br).
Proof.
  intros bt bg br lo hi Hlo Hhi s Hs.
  assert (HT : Forall (fun v => rule_type_val_match Tint8 v = true)
    (map V293_byteval V293_ready_table)) by (vm_compute; repeat constructor).
  assert (HR : Forall (fun v => rule_type_val_match Tint8 v = true) (map V293_byteval [lo;hi])).
  { repeat constructor; apply V293_byte_type; assumption. }
  assert (HG : rule_type_val_match Tint8 (V293_byteval (V293_ready_group lo hi)) = true).
  { apply V293_byte_type. unfold V293_ready_group. destruct (Nat.eqb lo 0), (Nat.eqb hi 0); simpl; lia. }
  pose proof (V293_array_to_storage bt 0 1 Tint8 (map V293_byteval V293_ready_table) HT) as HA.
  rewrite map_length in HA.
  pose proof (V293_array_to_storage br 0 1 Tint8 (map V293_byteval [lo;hi]) HR) as HB.
  change (V293_array true br 0 1 Tint8 (map V293_byteval [lo;hi]) ==>
    V293_storage (V293_array_cells br 0 1 Tint8 2)) in HB.
  assert (HC : Amapsto (bg, 0%Z) Tint8 true (V293_byteval (V293_ready_group lo hi)) ==>
    V293_storage ([((bg, 0%Z), Tint8)])).
  { intros st H. cbn [V293_storage]. apply astar_r_aemp_intro.
    unfold V293_storage_cell. exists (V293_byteval (V293_ready_group lo hi)). sep auto. }
  unfold V293_inputs_full in Hs.
  eapply astar_mono in Hs; [ | apply astar_mono; [exact HA | exact HB] | exact HC].
  eapply astar_mono in Hs; [ | apply V293_storage_append | intros st Hz; exact Hz].
  unfold V293_input_cells. rewrite app_assoc.
  apply V293_storage_append. exact Hs.
Qed.

(* Exact remainder resources are framed through the call and assignment.
   The erasure premise is used only to close the SAME storage invariant.
   The old exported interfaces below instantiate kept with typed storage. *)
Section RetainedStoragePrefix.
Variables unmap group rows high table target : var.
Variables bt bg br bh bp bo : block.
Variable tp : type.
Variables lo hi : nat.
Variable entries : list val.
Variable rest : list (addr * type).
Variable kept : asrt.
Variable tid : Modules.tid.
Variable tasks : TcbMod.map.
Variable events : EcbMod.map.
Variable now : int32.
Variable aop : spec_code.
Variable stack : list hid.
Variable critical : list bool.
Variable px : asrt.
Definition V293_retained_prefix_cells :=
  V293_input_cells bt bg br ++
  [((bh, 0%Z), Tint8)] ++ V293_array_cells bp 0 4 (Tptr tp) (length entries) ++ rest.
Definition V293_retained_prefix_reserve :=
  V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi) **
  (V293_read_pointers tp bp 0 entries ** (kept ** px)).
(* This is an OPENED borrowing boundary. The old target and the callee's
   initial output value are not claimed reachable from initialization. *)
Definition V293_retained_storage_prefix_borrowed old :=
  (V293_sched_internal_pre unmap group rows high bt bg br bh lo hi V293_shared_li tid aop **
    V293_sched_critical V293_opened_inv stack critical) **
  (V293_prefix_frame table high target tp bp bo entries tasks
    (V293_shared_remainder tid events now ** V293_retained_prefix_reserve) ** V293_prefix_output tp bo old).
Definition V293_retained_prefix_physical :=
  V293_inputs_full bt bg br lo hi **
  ((PV (bh, Int.zero) @ Tint8 |->
      (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
    (V293_array true bp 0 4 (Tptr tp) entries ** kept)).
Definition V293_retained_prefix_returned next :=
  V293_storage_open target tp tid tasks events now next ** V293_retained_prefix_physical.
Definition V293_retained_prefix_snapshot next :=
  SWINV (V293_storage_inv V293_retained_prefix_cells target tp) //\\
  (((CurTid tid ** V293_shared_fields tid tasks events now) **
    (GV target @ (Tptr tp) |-> (Vptr next))) ** (V293_retained_prefix_physical ** Atrue)).
Definition V293_retained_storage_prefix_closed :=
  EX next : Modules.tid, [|V293_highest_ready tasks next|] **
  ((<||aop||> ** ((V293_retained_prefix_snapshot next ** CurTid tid) ** (Ais stack ** Acs critical))) **
    ((V293_sched_globals unmap group rows high bt bg br bh **
      V293_prefix_bindings table high target tp bp bo) ** (px ** Atrue))).

Lemma V293_retained_prefix_physical_return :
  (kept ==> V293_storage rest) ->
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_retained_prefix_physical ==> V293_storage V293_retained_prefix_cells.
Proof.
  intros Hforget Hlo Hhi Hr Hptr s Hs.
  assert (HT : rule_type_val_match Tint8
    (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) = true).
  { apply V293_byte_type.
    pose proof (V293_ready_selection_range lo hi (V293_ready_group lo hi) Hlo Hhi eq_refl Hr). lia. }
  assert (HH : (PV (bh, Int.zero) @ Tint8 |->
      (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) ==>
    V293_storage ([((bh, 0%Z), Tint8)])).
  { intros st H. cbn [V293_storage]. apply astar_r_aemp_intro.
    unfold V293_storage_cell. exists (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))). sep auto. }
  pose proof (V293_array_to_storage bp 0 4 (Tptr tp) entries Hptr) as HP.
  unfold V293_retained_prefix_physical in Hs. unfold V293_retained_prefix_cells.
  eapply astar_mono in Hs; [ | apply V293_inputs_to_storage; assumption | ].
  2: { apply astar_mono; [exact HH | apply astar_mono; [exact HP | exact Hforget]]. }
  apply V293_storage_append. eapply astar_mono; [intros st Hz; exact Hz | | exact Hs].
  intros st H. apply V293_storage_append.
  eapply astar_mono; [intros st0 H0; exact H0 | apply V293_storage_append | exact H].
Qed.
Lemma V293_retained_prefix_return_snapshot : forall next,
  (kept ==> V293_storage rest) ->
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_retained_prefix_returned next ==> V293_retained_prefix_snapshot next.
Proof.
  intros next Hforget Hlo Hhi Hr Hptr s Hs. split.
  - unfold V293_retained_prefix_returned in Hs.
    eapply astar_mono in Hs; [ | intros st Hz; exact Hz | apply V293_retained_prefix_physical_return; assumption].
    eapply V293_storage_return; exact Hs.
  - unfold V293_retained_prefix_returned, V293_storage_open in Hs. sep auto.
Qed.

Definition V293_retained_storage_prefix_returned :=
  EX next : Modules.tid, [|V293_highest_ready tasks next|] **
  ((<||aop||> ** ((V293_retained_prefix_returned next ** CurTid tid) ** (Ais stack ** Acs critical))) **
    ((V293_sched_globals unmap group rows high bt bg br bh **
      V293_prefix_bindings table high target tp bp bo) ** (px ** Atrue))).

Theorem V293_retained_OSSched_storage_prefix_returned : forall Spec (RI : Inv) r ri sched_id old,
  GoodFrm kept ->
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  GoodFrm px ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li RI r ri
    (V293_retained_storage_prefix_borrowed old)
    (V293_OSSched_unlocked_prefix sched_id table high target)
    V293_retained_storage_prefix_returned tid.
Proof.
  intros Spec RI r ri sched_id old Hkept Hlo Hhi Hr Hb Htable Hpx Hspec.
  eapply conseq_rule.
  3: { eapply V293_resource_OSSched_critical_prefix with
      (I := V293_opened_inv) (Hli := V293_switch_li_good)
      (frame := V293_shared_remainder tid events now ** V293_retained_prefix_reserve)
      (unmap := unmap) (group := group) (rows := rows) (bt := bt) (bg := bg) (br := br) (bh := bh)
      (lo := lo) (hi := hi) (tp := tp) (bp := bp) (bo := bo) (entries := entries) (tasks := tasks)
      (aop := aop) (old := old) (stack := stack) (critical := critical); try eassumption.
    split; [apply V293_shared_remainder_good | ].
    unfold V293_retained_prefix_reserve, V293_sched_inputs.
    repeat rewrite V293_read_bytes_array. rewrite V293_read_pointers_array.
    repeat split; try apply V293_array_good; try exact Hkept; try exact I; exact Hpx. }
  - intros s Hs. exact Hs.
  - intros s [next Hs]. unfold V293_retained_storage_prefix_returned. exists next.
    unfold V293_sched_internal_post, V293_sched_internal_resource,
      V293_prefix_frame, V293_shared_remainder, V293_retained_prefix_reserve, V293_sched_critical in Hs.
    unfold CurLINV, LINV, V293_shared_li in Hs.
    sep normal in Hs. sep destruct Hs. sep split in Hs.
    assert (HP : s |= SWINV V293_opened_inv **
      ([|V293_highest_ready tasks next|] **
        ((V293_prefix_bindings table high target tp bp bo ** V293_prefix_output tp bo (Vptr next)) **
          ((CurTid tid ** V293_shared_fields tid tasks events now) **
            ((V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi) **
              V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi)) **
              ((V293_read_pointers tp bp 0 entries ** V293_read_pointers tp bp 0 entries) **
                ((PV (bh, Int.zero) @ Tint8 |->
                  (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
                  (kept **
                    ((<||aop||> ** CurTid tid) ** ((Ais stack ** Acs critical) **
                      (V293_sched_globals unmap group rows high bt bg br bh ** (px ** Atrue))))))))))))
      by (unfold V293_shared_fields; sep auto).
    eapply astar_mono in HP; [ | apply V293_opened_switch_open | intros st Hz; exact Hz].
    assert (HK : s |=
      ((V293_prefix_bindings table high target tp bp bo ** V293_prefix_output tp bo (Vptr next)) **
        ((V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi) **
          V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi)) **
          (V293_read_pointers tp bp 0 entries ** V293_read_pointers tp bp 0 entries))) **
      (V293_shared_flags ** ([|V293_highest_ready tasks next|] **
        ((CurTid tid ** V293_shared_fields tid tasks events now) **
          ((PV (bh, Int.zero) @ Tint8 |->
            (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
            (kept **
              ((<||aop||> ** CurTid tid) ** ((Ais stack ** Acs critical) **
                (V293_sched_globals unmap group rows high bt bg br bh ** (px ** Atrue))))))))))
      by (clear Hs; sep auto).
    eapply astar_mono in HK.
    2: { apply astar_mono; [apply V293_dispatch_output_named | apply astar_mono].
         - apply V293_inputs_reunite.
         - rewrite V293_read_pointers_array. apply V293_array_reunite. }
    2: { intros st Hz; exact Hz. }
    assert (HL : s |= V293_retained_prefix_returned next **
      ([|V293_highest_ready tasks next|] **
        ((<||aop||> ** CurTid tid) ** ((Ais stack ** Acs critical) **
          ((V293_sched_globals unmap group rows high bt bg br bh **
            V293_prefix_bindings table high target tp bp bo) ** (px ** Atrue))))))
      by (unfold V293_retained_prefix_returned, V293_storage_open, V293_retained_prefix_physical; clear Hs HP; sep auto).
    clear Hs HP HK. sep auto.
Qed.
Theorem V293_retained_OSSched_storage_prefix : forall Spec r ri sched_id old,
  GoodFrm kept -> (kept ==> V293_storage rest) ->
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries -> GoodFrm px ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_storage_inv V293_retained_prefix_cells target tp) r ri
    (V293_retained_storage_prefix_borrowed old)
    (V293_OSSched_unlocked_prefix sched_id table high target)
    V293_retained_storage_prefix_closed tid.
Proof.
  intros Spec r ri sched_id old Hkept Hforget Hlo Hhi Hr Hb Htable Hptr Hpx Hspec.
  eapply conseq_rule with (q := V293_retained_storage_prefix_returned).
  - intros s Hs; exact Hs.
  - intros s [next Hs]. unfold V293_retained_storage_prefix_returned in Hs.
    unfold V293_retained_storage_prefix_closed. exists next.
    assert (HP : s |= V293_retained_prefix_returned next **
      ([|V293_highest_ready tasks next|] **
        ((<||aop||> ** CurTid tid) ** ((Ais stack ** Acs critical) **
          ((V293_sched_globals unmap group rows high bt bg br bh **
            V293_prefix_bindings table high target tp bp bo) ** (px ** Atrue)))))) by (sep auto).
    eapply astar_mono in HP; [ | apply V293_retained_prefix_return_snapshot; assumption | intros st H; exact H].
    clear Hs. sep auto.
  - eapply V293_retained_OSSched_storage_prefix_returned; eassumption.
Qed.
(* A closed-invariant entry with an exact same-state observation. Neither the
   physical arrays nor the shared task table is duplicated by this conjunction. *)
Definition V293_retained_prefix_entry_heap hv :=
  V293_inputs_full bt bg br lo hi **
    ((PV (bh, Int.zero) @ Tint8 |-> hv) **
      (V293_array true bp 0 4 (Tptr tp) entries ** kept)).
Definition V293_retained_prefix_entry_snapshot old hv :=
  SWINV (V293_storage_inv V293_retained_prefix_cells target tp) //\\
    (V293_storage_open target tp tid tasks events now old ** V293_retained_prefix_entry_heap hv).
Definition V293_retained_storage_prefix_entry old hv :=
  <||aop||> ** ((V293_retained_prefix_entry_snapshot old hv ** CurTid tid) **
    ((Ais stack ** Acs critical) **
      ((V293_sched_globals unmap group rows high bt bg br bh **
        V293_prefix_bindings table high target tp bp bo) ** px))).

Lemma V293_retained_entry_heap_to_storage : forall hv,
  (kept ==> V293_storage rest) -> lo < 256 -> hi < 256 ->
  rule_type_val_match Tint8 hv = true ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_retained_prefix_entry_heap hv ==> V293_storage V293_retained_prefix_cells.
Proof.
  intros hv Hforget Hlo Hhi Hhv Hptr.
  assert (HH : (PV (bh, Int.zero) @ Tint8 |-> hv) ==>
    V293_storage ([((bh, 0%Z), Tint8)])).
  { intros st H. cbn [V293_storage]. apply astar_r_aemp_intro.
    unfold V293_storage_cell. exists hv. sep auto. }
  intros st H. unfold V293_retained_prefix_entry_heap in H. unfold V293_retained_prefix_cells.
    eapply astar_mono in H; [ | apply V293_inputs_to_storage; assumption | ].
    2: { apply astar_mono; [exact HH | apply astar_mono;
      [apply V293_array_to_storage; exact Hptr | exact Hforget]]. }
    apply V293_storage_append. eapply astar_mono; [intros st0 H0; exact H0 | | exact H].
    intros st0 H0. apply V293_storage_append.
    eapply astar_mono; [intros st1 H1; exact H1 | apply V293_storage_append | exact H0].

Qed.

Lemma V293_retained_prefix_entry_close : forall old hv,
  (kept ==> V293_storage rest) ->
  lo < 256 -> hi < 256 ->
  rule_type_val_match Tint8 hv = true ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_storage_open target tp tid tasks events now old ** V293_retained_prefix_entry_heap hv ==>
  V293_retained_prefix_entry_snapshot old hv.
Proof.
  intros old hv Hforget Hlo Hhi Hhv Hptr s Hs. split; [ | exact Hs].
  pose proof (V293_retained_entry_heap_to_storage hv Hforget Hlo Hhi Hhv Hptr) as HP.
  eapply astar_mono in Hs; [ | intros st H; exact H | exact HP].
  apply V293_storage_return in Hs. exact Hs.
Qed.

Lemma V293_retained_storage_prefix_lend_value : forall old hv,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  (<||aop||> **
    ((((V293_shared_flags ** ((CurTid tid ** V293_shared_fields tid tasks events now) **
      (GV target @ (Tptr tp) |-> old))) ** V293_retained_prefix_entry_heap hv) ** CurTid tid) **
      ((Ais stack ** Acs critical) **
        ((V293_sched_globals unmap group rows high bt bg br bh **
          V293_prefix_bindings table high target tp bp bo) ** px)))) ==>
    V293_retained_storage_prefix_borrowed old.
Proof.
  intros old hv Hlo Hhi Hr s Hs.
  unfold V293_retained_prefix_entry_heap in Hs.
  assert (HP : s |=
    ((V293_inputs_full bt bg br lo hi ** V293_array true bp 0 4 (Tptr tp) entries) **
      (V293_prefix_bindings table high target tp bp bo ** (GV target @ (Tptr tp) |-> old))) **
    ((V293_shared_flags ** (CurTid tid ** (CurTid tid ** V293_shared_fields tid tasks events now))) **
      ((PV (bh, Int.zero) @ Tint8 |-> hv) **
        (<||aop||> ** ((Ais stack ** Acs critical) **
          (V293_sched_globals unmap group rows high bt bg br bh ** (kept ** px))))))) by (sep auto).
  eapply astar_mono in HP.
  2: { apply astar_mono; [apply astar_mono;
      [apply V293_inputs_borrow | intros st H;
        pose proof (V293_array_borrow bp 0 4 (Tptr tp) entries st H) as HB;
        rewrite <- V293_read_pointers_array in HB; exact HB] |
      apply V293_dispatch_named_output]. }
  2: { intros st H; exact H. }
  assert (HC : CurTid tid ==> CurLINV V293_shared_li tid).
  { intros st H. unfold CurLINV. exists (nil : list logicvar).
    assert (HL : Aemp ==> LINV V293_shared_li tid nil ** Atrue).
    { intros st0 H0. pose proof (V293_switch_local_empty tid nil st0 H0) as H1. sep auto. }
    eapply astar_mono;
      [intros st0 H0; exact H0 | exact HL | apply astar_r_aemp_intro; exact H]. }
  assert (HK : s |=
    V293_shared_flags **
      (CurTid tid **
        ((V293_sched_globals unmap group rows high bt bg br bh **
          V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi)) **
          ((PV (bh, Int.zero) @ Tint8 |-> hv) **
            (V293_shared_fields tid tasks events now **
              ((V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi) **
                V293_read_pointers tp bp 0 entries) **
                ((V293_prefix_bindings table high target tp bp bo **
                  V293_read_pointers tp bp 0 entries) **
                  ((V293_prefix_output tp bo old ** CurTid tid) **
                    (<||aop||> ** ((Ais stack ** Acs critical) ** (kept ** px)))))))))))
    by (clear Hs; sep auto).
  eapply astar_mono in HK; [ | intros st H; exact H | apply astar_mono;
    [exact HC | intros st H; exact H]].
  (* Aie false is a state observation, not an owned memory cell. *)
  assert (HF : V293_shared_flags ==> Aie false ** SWINV V293_opened_inv).
  { intros st H. apply astar_l_aie_intro; [apply V293_opened_switch_close; exact H | ].
    unfold V293_shared_flags in H. sep auto. }
  eapply astar_mono in HK; [ | exact HF | intros st H; exact H].
  assert (HE : (<||aop||> **
    V293_sched_internal_resource unmap group rows high bt bg br bh lo hi V293_shared_li tid hv) ==>
    V293_sched_internal_pre unmap group rows high bt bg br bh lo hi V293_shared_li tid aop).
  { intros st H. exists hv. sep auto. }
  assert (HL : s |= (<||aop||> **
    V293_sched_internal_resource unmap group rows high bt bg br bh lo hi V293_shared_li tid hv) **
    (V293_sched_critical V293_opened_inv stack critical **
      (V293_prefix_frame table high target tp bp bo entries tasks
        (V293_shared_remainder tid events now ** V293_retained_prefix_reserve) ** V293_prefix_output tp bo old))).
  { unfold V293_sched_internal_resource, V293_sched_critical, V293_prefix_frame,
      V293_retained_prefix_reserve, V293_shared_remainder, V293_shared_fields in *.
    clear HP Hs. sep auto. }
  eapply astar_mono in HL; [ | exact HE | intros st H; exact H].
  unfold V293_retained_storage_prefix_borrowed. clear Hs HP HK. sep auto.
Qed.

Lemma V293_retained_storage_prefix_lend : forall old hv,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_retained_storage_prefix_entry old hv ==> V293_retained_storage_prefix_borrowed (Vptr old).
Proof.
  intros old hv Hlo Hhi Hr s Hs.
  apply V293_retained_storage_prefix_lend_value with (hv := hv); try assumption.
  unfold V293_retained_storage_prefix_entry in Hs.
  eapply astar_mono in Hs; [ | intros st H; exact H | apply astar_mono].
  2: { apply astar_mono; [intros st [_ H]; exact H | intros st H; exact H]. }
  2: { intros st H; exact H. }
  unfold V293_storage_open in Hs. exact Hs.
Qed.

Theorem V293_retained_OSSched_storage_closed_prefix : forall Spec r ri sched_id old hv,
  GoodFrm kept -> (kept ==> V293_storage rest) ->
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries -> GoodFrm px ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_storage_inv V293_retained_prefix_cells target tp) r ri
    (V293_retained_storage_prefix_entry old hv)
    (V293_OSSched_unlocked_prefix sched_id table high target)
    V293_retained_storage_prefix_closed tid.
Proof.
  intros Spec r ri sched_id old hv Hkept Hforget Hlo Hhi Hr Hb Ht Hp Hpx Hspec.
  eapply conseq_rule.
  - apply V293_retained_storage_prefix_lend; assumption.
  - intros st H; exact H.
  - apply V293_retained_OSSched_storage_prefix; assumption.
Qed.
End RetainedStoragePrefix.

Section StoragePrefix.
Variables unmap group rows high table target : var.
Variables bt bg br bh bp bo : block.
Variable tp : type.
Variables lo hi : nat.
Variable entries : list val.
Variable rest : list (addr * type).
Variable tid : Modules.tid.
Variable tasks : TcbMod.map.
Variable events : EcbMod.map.
Variable now : int32.
Variable aop : spec_code.
Variable stack : list hid.
Variable critical : list bool.
Variable px : asrt.
Definition V293_prefix_cells :=
  V293_input_cells bt bg br ++
  [((bh, 0%Z), Tint8)] ++ V293_array_cells bp 0 4 (Tptr tp) (length entries) ++ rest.
Definition V293_prefix_reserve :=
  V293_sched_inputs bt bg br lo hi (V293_ready_group lo hi) **
  (V293_read_pointers tp bp 0 entries ** (V293_storage rest ** px)).
(* This is an OPENED borrowing boundary. The old target and the callee's
   initial output value are not claimed reachable from initialization. *)
Definition V293_storage_prefix_borrowed old :=
  (V293_sched_internal_pre unmap group rows high bt bg br bh lo hi V293_shared_li tid aop **
    V293_sched_critical V293_opened_inv stack critical) **
  (V293_prefix_frame table high target tp bp bo entries tasks
    (V293_shared_remainder tid events now ** V293_prefix_reserve) ** V293_prefix_output tp bo old).
Definition V293_prefix_physical :=
  V293_inputs_full bt bg br lo hi **
  ((PV (bh, Int.zero) @ Tint8 |->
      (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi)))) **
    (V293_array true bp 0 4 (Tptr tp) entries ** V293_storage rest)).
Definition V293_prefix_returned next :=
  V293_storage_open target tp tid tasks events now next ** V293_prefix_physical.
Definition V293_prefix_snapshot next :=
  SWINV (V293_storage_inv V293_prefix_cells target tp) //\\
  (((CurTid tid ** V293_shared_fields tid tasks events now) **
    (GV target @ (Tptr tp) |-> (Vptr next))) ** (V293_prefix_physical ** Atrue)).
Definition V293_storage_prefix_closed :=
  EX next : Modules.tid, [|V293_highest_ready tasks next|] **
  ((<||aop||> ** ((V293_prefix_snapshot next ** CurTid tid) ** (Ais stack ** Acs critical))) **
    ((V293_sched_globals unmap group rows high bt bg br bh **
      V293_prefix_bindings table high target tp bp bo) ** (px ** Atrue))).

Lemma V293_prefix_physical_return :
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_prefix_physical ==> V293_storage V293_prefix_cells.
Proof.
  intros Hlo Hhi Hr Hptr. eapply V293_retained_prefix_physical_return with (kept := V293_storage rest); try eassumption;
    try apply V293_storage_frame_good; intros st Hst; exact Hst.
Qed.
Lemma V293_prefix_return_snapshot : forall next,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_prefix_returned next ==> V293_prefix_snapshot next.
Proof.
  intros next Hlo Hhi Hr Hptr. eapply V293_retained_prefix_return_snapshot with (kept := V293_storage rest); try eassumption;
    try apply V293_storage_frame_good; intros st Hst; exact Hst.
Qed.

Theorem V293_OSSched_storage_prefix : forall Spec r ri sched_id old,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries -> GoodFrm px ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_storage_inv V293_prefix_cells target tp) r ri
    (V293_storage_prefix_borrowed old)
    (V293_OSSched_unlocked_prefix sched_id table high target)
    V293_storage_prefix_closed tid.
Proof.
  intros Spec r ri sched_id old Hlo Hhi Hr Hb Htable Hptr Hpx Hspec. eapply V293_retained_OSSched_storage_prefix with (kept := V293_storage rest); try eassumption;
    try apply V293_storage_frame_good; intros st Hst; exact Hst.
Qed.
(* A closed-invariant entry with an exact same-state observation. Neither the
   physical arrays nor the shared task table is duplicated by this conjunction. *)
Definition V293_prefix_entry_heap hv :=
  V293_inputs_full bt bg br lo hi **
    ((PV (bh, Int.zero) @ Tint8 |-> hv) **
      (V293_array true bp 0 4 (Tptr tp) entries ** V293_storage rest)).
Definition V293_prefix_entry_snapshot old hv :=
  SWINV (V293_storage_inv V293_prefix_cells target tp) //\\
    (V293_storage_open target tp tid tasks events now old ** V293_prefix_entry_heap hv).
Definition V293_storage_prefix_entry old hv :=
  <||aop||> ** ((V293_prefix_entry_snapshot old hv ** CurTid tid) **
    ((Ais stack ** Acs critical) **
      ((V293_sched_globals unmap group rows high bt bg br bh **
        V293_prefix_bindings table high target tp bp bo) ** px))).

Lemma V293_prefix_entry_close : forall old hv,
  lo < 256 -> hi < 256 ->
  rule_type_val_match Tint8 hv = true ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_storage_open target tp tid tasks events now old ** V293_prefix_entry_heap hv ==>
  V293_prefix_entry_snapshot old hv.
Proof.
  intros old hv Hlo Hhi Hhv Hptr. eapply V293_retained_prefix_entry_close with (kept := V293_storage rest); try eassumption;
    try apply V293_storage_frame_good; intros st Hst; exact Hst.
Qed.

Lemma V293_storage_prefix_lend : forall old hv,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_storage_prefix_entry old hv ==> V293_storage_prefix_borrowed (Vptr old).
Proof.
  intros old hv Hlo Hhi Hr. eapply V293_retained_storage_prefix_lend with (kept := V293_storage rest); try eassumption;
    try apply V293_storage_frame_good; intros st Hst; exact Hst.
Qed.

Theorem V293_OSSched_storage_closed_prefix : forall Spec r ri sched_id old hv,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries -> GoodFrm px ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li (V293_storage_inv V293_prefix_cells target tp) r ri
    (V293_storage_prefix_entry old hv)
    (V293_OSSched_unlocked_prefix sched_id table high target)
    V293_storage_prefix_closed tid.
Proof.
  intros Spec r ri sched_id old hv Hlo Hhi Hr Hb Ht Hp Hpx Hspec. eapply V293_retained_OSSched_storage_closed_prefix with (kept := V293_storage rest); try eassumption;
    try apply V293_storage_frame_good; intros st Hst; exact Hst.
Qed.
End StoragePrefix.

(* Ready bitmap/table correspondence is owned by the invariant, not supplied
   as an exact snapshot across an interrupt. OSPrioCur correspondence remains
   a separate port obligation: the framework switch changes only OSTCBCur. *)
Lemma V293_array_inv_good : forall w b offset step tau vs,
  GoodInvAsrt (V293_array w b offset step tau vs).
Proof. intros w b offset step tau vs. revert offset. induction vs; intros; simpl; auto. Qed.

Section ReadyStorageInvariant.
Variables bt bg br bh bp : block.
Variable tp : type.
Variable rest : list (addr * type).
Variable target : var.
Let cells := V293_input_cells bt bg br ++ [((bh, 0%Z), Tint8)] ++
  V293_array_cells bp 0 4 (Tptr tp) 13 ++ rest.
Definition V293_ready_resources (tasks : TcbMod.map) :=
  EX lo : nat, EX hi : nat, EX entries : list val, EX hv : val,
    [|lo < 256 /\ hi < 256 /\ (exists p, V293_bitmap_ready lo hi p) /\
      V293_bitmap_tasks lo hi tasks /\ V293_priority_table entries tasks /\
      Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries /\
      rule_type_val_match Tint8 hv = true|] **
    V293_retained_prefix_entry_heap bt bg br bh bp tp lo hi entries (V293_storage rest) hv.
Definition V293_ready_core := EX current : Modules.tid, EX tasks : TcbMod.map,
  EX events : EcbMod.map, EX now : int32,
    CurTid current ** (V293_shared_fields current tasks events now **
      (V293_dispatch_cell target tp ** V293_ready_resources tasks)).

Lemma V293_ready_resources_forget : forall tasks,
  V293_ready_resources tasks ==> V293_storage cells.
Proof.
  intros tasks s (lo & hi & entries & hv & H).
  apply astar_l_apure_elim in H.
  destruct H as [[Hlo [Hhi [Hr [Hb [Ht [Hptr Hhv]]]]]] H].
  pose proof (proj1 Ht) as Hlen.
  pose proof (V293_retained_entry_heap_to_storage bt bg br bh bp tp lo hi entries rest
    (V293_storage rest) hv (fun _ H => H) Hlo Hhi Hhv Hptr s H) as HP.
  unfold V293_retained_prefix_cells in HP. rewrite Hlen in HP. exact HP.
Qed.
Lemma V293_ready_core_forget :
  V293_ready_core ==> V293_storage_core cells target tp.
Proof.
  intros s (ct & ts & es & n & Hs).
  eapply astar_mono in Hs; [ | intros st H; exact H | apply astar_mono;
    [intros st H; exact H | apply astar_mono;
      [intros st H; exact H | apply V293_ready_resources_forget]]].
  unfold V293_storage_core, V293_shared_core. sep auto.
Qed.
Lemma V293_ready_resources_frame : forall ts, GoodFrm (V293_ready_resources ts).
Proof.
  intro ts. unfold V293_ready_resources, V293_retained_prefix_entry_heap, V293_inputs_full.
  simpl. intros. repeat split; try exact I; try apply V293_array_good; apply V293_storage_frame_good.
Qed.
Lemma V293_ready_core_frame : GoodFrm V293_ready_core.
Proof.
  change (forall ct ts es n, GoodFrm (CurTid ct) /\
    (GoodFrm (V293_shared_fields ct ts es n) /\
      (GoodFrm (V293_dispatch_cell target tp) /\ GoodFrm (V293_ready_resources ts)))).
  intros ct ts es n. split.
  - unfold CurTid, Agvarmapsto, Aptrmapsto. simpl. auto.
  - split; [unfold V293_shared_fields; simpl; auto | ].
    split; [unfold V293_dispatch_cell, Agvarmapsto, Aptrmapsto; simpl; auto | ].
    apply V293_ready_resources_frame.
Qed.
Definition V293_ready_inv : Inv.
Proof.
  intro k. destruct k.
  - refine (@mkinvasrt V293_ready_core _ _).
    + change (forall ct ts es n, GoodInvAsrt (CurTid ct) /\
        (GoodInvAsrt (V293_shared_fields ct ts es n) /\
          (GoodInvAsrt (V293_dispatch_cell target tp) /\ GoodInvAsrt (V293_ready_resources ts)))).
      intros ct ts es n. split.
      * unfold CurTid, Agvarmapsto, Aptrmapsto. simpl. auto.
      * split; [unfold V293_shared_fields; simpl; auto | ].
        split; [unfold V293_dispatch_cell, Agvarmapsto, Aptrmapsto; simpl; auto | ].
        unfold V293_ready_resources, V293_retained_prefix_entry_heap, V293_inputs_full.
        simpl. intros. repeat split; try exact I; try apply V293_array_inv_good; apply V293_storage_good.
    + split.
      * intros s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
        assert (HP : precise (V293_storage_core cells target tp)).
        { unfold V293_storage_core. apply precise_star; [apply V293_shared_core_precise | ].
          apply precise_star; [apply V293_dispatch_cell_precise | apply V293_storage_precise]. }
        exact (HP s M1 M2 O1 O2 (V293_ready_core_forget _ H1)
          (V293_ready_core_forget _ H2) M O HM1 HM2 HO1 HO2).
      * unfold assertion.inv_isr_prop. repeat split; intros;
          destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op].
        all: eapply goodfrm_prop; [exact V293_ready_core_frame | exact H].
  - exact (V293_shared_inv (S k)).
Defined.
Lemma V293_ready_noisr_tail : forall n k,
  starinv_noisr V293_ready_inv (S k) n <==> Aemp.
Proof.
  induction n; intros k s; simpl starinv_noisr; [reflexivity | ]. split; intro H.
  - apply astar_l_aemp_elim in H. apply IHn in H. exact H.
  - apply astar_l_aemp_intro. apply IHn. exact H.
Qed.
Lemma V293_ready_noisr_core : forall n,
  starinv_noisr V293_ready_inv 0 n <==> V293_ready_core.
Proof.
  intros [ | n] s; [reflexivity | ]. split; intro Houter.
  - apply astar_r_aemp_elim. eapply astar_mono; [intros st H; exact H | | exact Houter].
    intros st Hs; apply V293_ready_noisr_tail in Hs; exact Hs.
  - eapply astar_mono; [intros st H; exact H | | ].
    intros st Hs; apply V293_ready_noisr_tail; exact Hs.
    apply astar_r_aemp_intro. exact Houter.
Qed.
Lemma V293_ready_switch_open :
  SWINV V293_ready_inv ==> V293_shared_flags ** V293_ready_core.
Proof.
  intros s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (HC : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold SWINV in Hs. sep auto. }
  unfold SWINV in Hs. apply sat_split in Hs.
  destruct Hs as (m1 & m2 & o1 & o2 & JM & JO & HF & k & HK).
  apply sat_split in HK. destruct HK as (m3 & m4 & o3 & o4 & JM2 & JO2 & HT & HI).
  unfold invlth_isr in HI. rewrite Nat.sub_0_r in HI.
  apply invisr_imply_noisr' in HI; [ | intros; apply HC]. apply V293_ready_noisr_core in HI.
  assert (HP : (ge, le, M, ir, aux, O, op) |=
    (isrclr ** Aie false) ** (ATopis k ** V293_ready_core)).
  { apply sat_split'. exists m1. exists m2. exists o1. exists o2.
    split; [exact JM | ]. split; [exact JO | ]. split; [exact HF | ].
    apply sat_split'. exists m3. exists m4. exists o3. exists o4.
    repeat first [assumption | split]. }
  unfold V293_shared_flags. sep auto.
Qed.
Lemma V293_ready_switch_close :
  V293_shared_flags ** V293_ready_core ==> SWINV V293_ready_inv.
Proof.
  intros s Hs. destruct s as [[[[[[ge le] M] ir] aux] O] op].
  assert (HC : forall i, ir i = false).
  { eapply (V293_shared_clear_state ge le M ir aux O op). unfold V293_shared_flags in Hs. sep auto. }
  unfold V293_shared_flags in Hs. sep normal in Hs. sep destruct Hs.
  assert (HP : (ge, le, M, ir, aux, O, op) |=
    (isrclr ** Aie false) ** (ATopis x ** V293_ready_core)) by (sep auto).
  apply sat_split in HP. destruct HP as (m1 & m2 & o1 & o2 & JM & JO & HF & HK).
  apply sat_split in HK. destruct HK as (m3 & m4 & o3 & o4 & JM2 & JO2 & HT & HI).
  apply (proj2 (V293_ready_noisr_core x _)) in HI.
  apply V293_shared_clear_noisr_close in HI; [ | exact HC].
  unfold SWINV. apply sat_split'. exists m1. exists m2. exists o1. exists o2.
  split; [exact JM | ]. split; [exact JO | ]. split; [exact HF | ].
  exists x. unfold invlth_isr. rewrite Nat.sub_0_r.
  apply sat_split'. exists m3. exists m4. exists o3. exists o4. repeat first [assumption | split].
Qed.
Definition V293_ready_full t := EX ts : TcbMod.map, EX es : EcbMod.map, EX n : int32,
  (EX ct : type, GV OSTCBCur @ (Tptr ct) |-> (Vptr t)) **
    (V293_shared_fields t ts es n ** (V293_dispatch_cell target tp ** V293_ready_resources ts)).
Lemma V293_ready_switch_full : forall t,
  SWINVt V293_ready_inv t ==> V293_shared_flags ** V293_ready_full t.
Proof.
  intros t s Hs. unfold SWINVt in Hs.
  eapply astar_mono in Hs; [ | apply V293_ready_switch_open | intros st H; exact H].
  unfold V293_ready_core in Hs. sep normal in Hs. sep destruct Hs.
  assert (HC : s |= CurTid t ** (CurTid x **
    (V293_shared_fields x x0 x1 x2 **
      (V293_shared_flags ** (V293_dispatch_cell target tp ** V293_ready_resources x0))))).
  { unfold CurTid at 1. apply astar_l_aexists_intro. exists x3. sep auto. }
  clear Hs. rename HC into Hs.
  assert (E : x = t).
  { eapply (V293_shared_current_agree x t (V293_shared_flags **
      (V293_shared_fields x x0 x1 x2 ** (V293_dispatch_cell target tp ** V293_ready_resources x0))) s).
    sep auto. } subst x.
  assert (HP : s |= (CurTid t ** CurTid t) **
    (V293_shared_flags ** (V293_shared_fields t x0 x1 x2 **
      (V293_dispatch_cell target tp ** V293_ready_resources x0)))) by (sep auto).
  eapply astar_mono in HP; [ | apply V293_current_halves_write | intros st H; exact H].
  unfold V293_ready_full. clear Hs. sep auto.
Qed.
Lemma V293_ready_switch_halves : forall t,
  V293_shared_flags ** V293_ready_full t ==> SWINVt V293_ready_inv t.
Proof.
  intros t s Hs. unfold V293_ready_full in Hs. sep normal in Hs. sep destruct Hs.
  assert (HP : s |= (GV OSTCBCur @ (Tptr x2) |-> (Vptr t)) **
    (V293_shared_flags ** (V293_shared_fields t x x0 x1 **
      (V293_dispatch_cell target tp ** V293_ready_resources x)))) by (unfold CurTid in *; sep auto).
  eapply astar_mono in HP; [ | apply GV_separate_rw | intros st H; exact H].
  unfold SWINVt. apply astar_mono with (P := V293_shared_flags ** V293_ready_core) (Q := CurTid t).
  - apply V293_ready_switch_close.
  - intros st H; exact H.
  - unfold V293_ready_core, CurTid. clear Hs. sep auto.
Qed.
Lemma V293_ready_store : forall current t ge le M M' ir aux O op b ct,
  (ge, le, M, ir, aux, O, op) |= SWINVt V293_ready_inv current ->
  get ge OSTCBCur = Some (b, Tptr ct) ->
  store (Tptr ct) M (b, 0%Z) (Vptr t) = Some M' ->
  (ge, le, M', ir, aux, set O curtid (oscurt t), op) |= SWINVt V293_ready_inv t.
Proof.
  intros current t ge le M M' ir aux O op b ct Hs GE HS.
  apply V293_ready_switch_full in Hs. unfold V293_ready_full in Hs. sep normal in Hs. sep destruct Hs.
  assert (HP : (ge, le, M, ir, aux, O, op) |= (GV OSTCBCur @ (Tptr x2) |-> (Vptr current)) **
    (V293_shared_flags ** (V293_shared_fields current x x0 x1 **
      (V293_dispatch_cell target tp ** V293_ready_resources x)))) by (sep auto).
  assert (ET : x2 = ct).
  { pose proof (@V293_star_env_l _ _ (fun ge _ => exists b, get ge OSTCBCur = Some (b, Tptr x2))
      (fun st H => V293_global_cell_type OSTCBCur (Tptr x2) true (Vptr current) st H) _ HP) as [b0 G].
    change (get ge OSTCBCur = Some (b0, Tptr x2)) in G. congruence. } subst x2.
  pose proof (V293_shared_store_global _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP GE HS) as Hstored.
  assert (HN : (ge, le, M', ir, aux, O, op) |= Aabsdata curtid (oscurt current) **
    ((GV OSTCBCur @ (Tptr ct) |-> (Vptr t)) ** (V293_shared_flags **
      ((Aabsdata abstcblsid (abstcblist x) **
        (Aabsdata absecblsid (absecblist x0) ** Aabsdata ostmid (ostm x1))) **
        (V293_dispatch_cell target tp ** V293_ready_resources x))))).
  { unfold V293_shared_fields in Hstored. clear Hs HP. sep auto. }
  apply V293_shared_replace_slot with (new := oscurt t) in HN.
  apply V293_ready_switch_halves. unfold V293_ready_full, V293_shared_fields.
  clear Hs HP Hstored. sep auto.
Qed.
Theorem V293_ready_invariant_good : GoodI V293_ready_inv V293_scheduler V293_shared_li.
Proof.
  split.
  - intros o O Of op OO Hs JO. apply V293_ready_noisr_core in Hs.
    apply V293_ready_core_forget in Hs.
    eapply (V293_shared_no_abstract_frame (o, O, op) Of OO);
      [unfold V293_storage_core in Hs; sep auto | exact JO].
  - split.
    + intros o O op t Hs. destruct o as [[[[ge le] M] ir] aux].
      assert (HP : (ge, le, M, ir, aux, O, op) |= CurTid t ** Atrue).
      { change ((ge, le, M, ir, aux, O, op) |= SWINV V293_ready_inv ** CurTid t) in Hs. sep auto. }
      destruct (V293_shared_current_read _ _ _ _ _ _ _ _ _ HP) as [b [ct [GE LD]]].
      exists b. exists ct. split; [exact GE | ]. split; [exact LD | ].
      apply V293_ready_switch_full in Hs. unfold V293_ready_full in Hs. sep normal in Hs. sep destruct Hs.
      change (get (getabst (ge, le, M, ir, aux, O, op)) curtid = Some (oscurt t)).
      eapply V293_star_abst_get_l with (p := Aabsdata curtid (oscurt t)) (q := Atrue).
      * apply V293_shared_abs_get.
      * unfold V293_shared_fields in Hs. clear HP. sep auto.
    + split.
      * intros o O op t b ct M' current Hs Hhighest GE HS. destruct o as [[[[ge le] M] ir] aux].
        assert (HT : exists ts, get O abstcblsid = Some (abstcblist ts)).
        { apply V293_ready_switch_full in Hs. unfold V293_ready_full in Hs. sep normal in Hs. sep destruct Hs.
          exists x. change (get (getabst (ge, le, M, ir, aux, O, op)) abstcblsid = Some (abstcblist x)).
          eapply V293_star_abst_get_l with (p := Aabsdata abstcblsid (abstcblist x)) (q := Atrue).
          - apply V293_shared_abs_get.
          - unfold V293_shared_fields in Hs. sep auto. }
        destruct HT as [ts HT]. exists ts. split; [exact HT | ].
        pose proof (V293_ready_store current t ge le M M' ir aux O op b ct Hs GE HS) as Hnew.
        destruct (classic (indom ts current)) as [Hm | Hm].
        -- left. split; assumption.
        -- right. split; [exact Hm | ]. intros Mx Ox MM OO HL JM JO.
           specialize (HL op). destruct HL as [lg HL]. change (Mx = emp /\ Ox = emp) in HL.
           destruct HL as [EM EO]. subst Mx Ox. apply map_join_emp' in JM. apply map_join_emp' in JO.
           subst MM OO. exact Hnew.
      * apply V293_scheduler_good.
Qed.

Definition V293_ready_snapshot := EX current : Modules.tid, EX tasks : TcbMod.map,
  EX events : EcbMod.map, EX now : int32, EX lo : nat, EX hi : nat,
  EX entries : list val, EX hv : val,
  [|lo < 256 /\ hi < 256 /\ (exists p, V293_bitmap_ready lo hi p) /\
    V293_bitmap_tasks lo hi tasks /\ V293_priority_table entries tasks /\
    Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries /\
    rule_type_val_match Tint8 hv = true|] **
  (CurTid current ** (V293_shared_fields current tasks events now **
    (V293_dispatch_cell target tp **
      V293_retained_prefix_entry_heap bt bg br bh bp tp lo hi entries (V293_storage rest) hv))).
Theorem V293_ready_core_snapshot : V293_ready_core ==> V293_ready_snapshot.
Proof.
  intros s (ct & ts & es & n & Hs). unfold V293_ready_resources in Hs.
  sep normal in Hs. sep destruct Hs.
  unfold V293_ready_snapshot. sep auto.
Qed.

(* No ready values or task map occur in the interrupt-enabled precondition. *)
Theorem V293_ready_enter_critical : forall Spec r ri tid aop critical P,
  GoodFrm P ->
  InfRules Spec V293_scheduler V293_shared_li V293_ready_inv r ri
    (<||aop||> ** OS[(fun _ : hid => false), true, nil, critical] ** ATopis INUM ** P)
    (sprim encrit)
    (<||aop||> ** OS[(fun _ : hid => false), false, nil, true::critical] **
      V293_ready_snapshot ** P) tid.
Proof.
  intros Spec r ri tid aop critical P Hframe.
  eapply conseq_rule with
    (p := <||aop||> ** OS[(fun _ : hid => false), true, nil, critical] **
      ATopis INUM ** [|INUM <= INUM|] ** P)
    (q := <||aop||> ** OS[(fun _ : hid => false), false, nil, true::critical] **
      invlth_isr V293_ready_inv 0 INUM ** P).
  - intros s Hs. sep auto; lia.
  - intros s Hs.
    assert (HC : s |= (OS[(fun _ : hid => false), false, nil, true::critical] **
      invlth_isr V293_ready_inv 0 INUM) ** (<||aop||> ** P)) by (sep auto).
    eapply astar_mono with
      (P' := OS[(fun _ : hid => false), false, nil, true::critical] ** V293_ready_snapshot)
      (Q' := <||aop||> ** P) in HC.
    2: { intros st Hpair. destruct st as [[[[[[ge le] M] ir] aux] O] op].
      assert (Hclear : forall i, ir i = false).
      { assert (HF : (ge, le, M, ir, aux, O, op) |= Aisr (fun _ : hid => false) ** Atrue)
          by (sep auto).
        apply sat_split in HF. destruct HF as (m1 & m2 & o1 & o2 & JM & JO & HF & HT).
        destruct HF as [E HE]. simpl in E. rewrite E. reflexivity. }
      apply sat_split in Hpair.
      destruct Hpair as (m1 & m2 & o1 & o2 & JM & JO & HF & Hinv).
      unfold invlth_isr in Hinv. apply invisr_imply_noisr' in Hinv; [ | intros; apply Hclear].
      apply V293_ready_noisr_core in Hinv. apply V293_ready_core_snapshot in Hinv.
      apply sat_split'. exists m1. exists m2. exists o1. exists o2.
      repeat first [assumption | split]. }
    2: { intros st H; exact H. }
    clear Hs. sep auto.
  - apply encrit1_rule; exact Hframe.
Qed.
End ReadyStorageInvariant.

(* Execute the real prefix under the SAME relational ambient invariant. *)
Lemma V293_ready_disabled_flags : forall critical,
  OS[(fun _ : hid => false), false, nil, critical] ==>
    V293_shared_flags ** (Ais nil ** Acs critical).
Proof.
  intros critical s Hs.
  assert (HR : Aisr (fun _ : hid => false) ==> isrclr).
  { intros st H. exists (fun _ : hid => false). split; [exact H | ].
    destruct H as [E HE]. split; [intros; reflexivity | exact HE]. }
  assert (HT : Ais nil ==> ATopis INUM ** Ais nil).
  { intros st H. destruct st as [[[[[[ge le] M] ir] [[ie si] cs]] O] op].
    destruct H as [E HE]. simpl in E. subst si.
    apply astar_l_atopis_intro; [split; [reflexivity | exact HE] | reflexivity]. }
  eapply astar_mono with (P' := isrclr) (Q' := Aie false ** ((ATopis INUM ** Ais nil) ** Acs critical)) in Hs.
  2: { exact HR. }
  2: { apply astar_mono; [intros st H; exact H | ].
    apply astar_mono; [exact HT | intros st H; exact H]. }
  unfold V293_shared_flags. sep auto.
Qed.

Section ReadyPrefixExecution.
Variables unmap group rows high table target : var.
Variables bt bg br bh bp bo : block.
Variable tp : type.
Variable rest : list (addr * type).
Let I := V293_ready_inv bt bg br bh bp tp rest target.
Let bindings := V293_sched_globals unmap group rows high bt bg br bh **
  V293_prefix_bindings table high target tp bp bo.
Definition V293_ready_prefix_chosen tid tasks events now next :=
  SWINV I //\\
    (((CurTid tid ** V293_shared_fields tid tasks events now) **
      (GV target @ (Tptr tp) |-> (Vptr next))) ** Atrue).
Lemma V293_ready_prefix_return : forall lo hi entries tid tasks events now next,
  lo < 256 -> hi < 256 -> (exists p, V293_bitmap_ready lo hi p) ->
  V293_bitmap_tasks lo hi tasks -> V293_priority_table entries tasks ->
  Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries ->
  V293_retained_prefix_returned target bt bg br bh bp tp lo hi entries (V293_storage rest)
    tid tasks events now next ==> V293_ready_prefix_chosen tid tasks events now next.
Proof.
  intros lo hi entries tid tasks events now next Hlo Hhi Hr Hb Ht Hp s Hs.
  unfold V293_ready_prefix_chosen. split.
  - apply V293_ready_switch_close.
    unfold V293_retained_prefix_returned, V293_storage_open, V293_retained_prefix_physical in Hs.
    unfold V293_ready_core, V293_ready_resources, V293_dispatch_cell, V293_retained_prefix_entry_heap.
    assert (Hhv : rule_type_val_match Tint8
      (V293_byteval (V293_ready_select lo hi (V293_ready_group lo hi))) = true).
    { apply V293_byte_type. pose proof (V293_ready_selection_range lo hi
        (V293_ready_group lo hi) Hlo Hhi eq_refl Hr). lia. }
    sep auto. repeat first [assumption | split].
  - unfold V293_retained_prefix_returned, V293_storage_open in Hs. sep auto.
Qed.
Definition V293_ready_prefix_open tid aop stack critical px :=
  <||aop||> **
    ((V293_ready_snapshot bt bg br bh bp tp rest target ** CurTid tid) **
      ((V293_shared_flags ** (Ais stack ** Acs critical)) ** (bindings ** px))).
Definition V293_ready_prefix_done tid aop stack critical px :=
  EX tasks : TcbMod.map, EX events : EcbMod.map, EX now : int32, EX next : Modules.tid,
    [|V293_highest_ready tasks next|] **
    ((<||aop||> ** ((V293_ready_prefix_chosen tid tasks events now next ** CurTid tid) **
      (Ais stack ** Acs critical))) ** (bindings ** (px ** Atrue))).
Theorem V293_ready_OSSched_prefix : forall Spec r ri sched_id tid aop stack critical px,
  GoodFrm px ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li I r ri
    (V293_ready_prefix_open tid aop stack critical px)
    (V293_OSSched_unlocked_prefix sched_id table high target)
    (V293_ready_prefix_done tid aop stack critical px) tid.
Proof.
  intros Spec r ri sched_id tid aop stack critical px Hpx Hspec.
  eapply conseq_rule with (p := EX tasks : TcbMod.map, EX events : EcbMod.map,
    EX now : int32, EX lo : nat, EX hi : nat, EX entries : list val, EX old : val,
    V293_retained_storage_prefix_borrowed unmap group rows high table target bt bg br bh bp bo
      tp lo hi entries (V293_storage rest) tid tasks events now aop stack critical px old **
    [|lo < 256 /\ hi < 256 /\ (exists p, V293_bitmap_ready lo hi p) /\
      V293_bitmap_tasks lo hi tasks /\ V293_priority_table entries tasks /\
      Forall (fun v => rule_type_val_match (Tptr tp) v = true) entries|]).
  - intros s Hs. unfold V293_ready_prefix_open, V293_ready_snapshot, V293_dispatch_cell in Hs.
    sep normal in Hs. sep destruct Hs. sep split in Hs.
    assert (E : x = tid).
    { eapply V293_shared_current_agree with (frame := Atrue) (s := s). sep auto. }
    subst x.
    destruct H0 as [Hlo [Hhi [Hr [Hb [Ht [Hp Hhv]]]]]].
    exists x0. exists x1. exists x2. exists x3. exists x4. exists x5. exists x7.
    apply astar_comm. apply astar_l_apure_intro.
    2: { repeat first [assumption | split]. }
    apply V293_retained_storage_prefix_lend_value with (hv := x6); try assumption.
    unfold V293_retained_prefix_entry_heap, bindings in *. sep auto.
  - intros s Hs; exact Hs.
  - apply ex_intro_rule. intro tasks. apply ex_intro_rule. intro events.
    apply ex_intro_rule. intro now. apply ex_intro_rule. intro lo.
    apply ex_intro_rule. intro hi. apply ex_intro_rule. intro entries.
    apply ex_intro_rule. intro old.
    apply pure_split_rule. intros [Hlo [Hhi [Hr [Hb [Ht Hp]]]]].
    eapply conseq_rule.
    3: { eapply V293_retained_OSSched_storage_prefix_returned with
        (RI := I) (kept := V293_storage rest) (lo := lo) (hi := hi) (entries := entries)
        (tid := tid) (tasks := tasks) (events := events) (now := now) (aop := aop)
        (stack := stack) (critical := critical) (px := px) (old := old)
        (unmap := unmap) (group := group) (rows := rows) (high := high)
        (table := table) (target := target) (bt := bt) (bg := bg) (br := br)
        (bh := bh) (bp := bp) (bo := bo) (tp := tp); try eassumption;
        apply V293_storage_frame_good. }
    + intros s Hs; exact Hs.
    + intros s [next Hs]. unfold V293_retained_storage_prefix_returned in Hs.
      assert (HP : s |= V293_retained_prefix_returned target bt bg br bh bp tp lo hi entries
        (V293_storage rest) tid tasks events now next **
        ([|V293_highest_ready tasks next|] **
          ((<||aop||> ** CurTid tid) ** ((Ais stack ** Acs critical) ** (bindings ** (px ** Atrue))))))
        by (unfold bindings; sep auto).
      eapply astar_mono in HP; [ | apply V293_ready_prefix_return; eassumption | intros st H; exact H].
      unfold V293_ready_prefix_done. clear Hs. sep auto.
Qed.
End ReadyPrefixExecution.

Lemma V293_ready_isr_clear : isrclr ==> Aisr (fun _ : hid => false).
Proof.
  intros s (r & Hr & [HC HE]).
  assert (E : r = (fun _ : hid => false)).
  { apply FunctionalExtensionality.functional_extensionality. intro i. apply HC. }
  subst r. exact Hr.
Qed.

Section ReadyCriticalRoundtrip.
Variables unmap group rows high table target : var.
Variables bt bg br bh bp bo : block.
Variable tp : type.
Variable rest : list (addr * type).
Let I := V293_ready_inv bt bg br bh bp tp rest target.
Let bindings := V293_sched_globals unmap group rows high bt bg br bh **
  V293_prefix_bindings table high target tp bp bo.
Lemma V293_ready_exit_resources : forall aop critical P,
  (<||aop||> ** ((SWINV I ** (Ais nil ** Acs (true::critical))) ** P)) ==>
  (<||aop||> ** OS[(fun _ : hid => false), false, nil, true::critical] **
    ATopis INUM ** invlth_isr I 0 INUM ** P).
Proof.
  intros aop critical P s Hs.
  assert (HT : gettopis (getis (gettaskst s)) = INUM).
  { assert (HP : s |= Ais nil ** Atrue) by (sep auto).
    apply astar_l_ais_elim in HP. destruct HP as [E _]. rewrite E. reflexivity. }
  unfold SWINV in Hs. sep normal in Hs. sep destruct Hs.
  assert (HK : gettopis (getis (gettaskst s)) = x).
  { assert (HP : s |= ATopis x ** Atrue) by (sep auto).
    exact (proj1 (astar_l_atopis_elim HP)). }
  assert (E : x = INUM) by congruence. rewrite E in Hs.
  assert (HP : s |= isrclr ** (<||aop||> ** Aie false ** Ais nil **
    Acs (true::critical) ** ATopis INUM ** invlth_isr I 0 INUM ** P)) by (sep auto).
  eapply astar_mono in HP; [ | apply V293_ready_isr_clear | intros st H; exact H].
  clear Hs. sep auto.
Qed.

Definition V293_ready_roundtrip_pre tid aop critical px :=
  <||aop||> ** OS[(fun _ : hid => false), true, nil, critical] **
    ATopis INUM ** (CurTid tid ** (bindings ** px)).
Definition V293_ready_roundtrip_post tid aop critical px :=
  <||aop||> ** OS[(fun _ : hid => false), true, nil, critical] **
    (CurTid tid ** (bindings ** (px ** Atrue))).
Theorem V293_ready_OSSched_critical_prefix : forall Spec r ri sched_id tid aop critical px,
  GoodFrm px ->
  Spec sched_id = Some
    (V293_critical_fpre unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     V293_critical_fpost unmap group rows high bt bg br bh V293_shared_li V293_opened_inv V293_switch_li_good,
     (Tvoid, nil)) ->
  InfRules Spec V293_scheduler V293_shared_li I r ri
    (V293_ready_roundtrip_pre tid aop critical px)
    (sseq (sprim encrit)
      (sseq (V293_OSSched_unlocked_prefix sched_id table high target) (sprim excrit)))
    (V293_ready_roundtrip_post tid aop critical px) tid.
Proof.
  intros Spec r ri sched_id tid aop critical px Hpx Hspec.
  assert (HF : GoodFrm (CurTid tid ** (bindings ** px))).
  { unfold CurTid, Agvarmapsto, Aptrmapsto, bindings, V293_sched_globals,
      V293_prefix_bindings. simpl. repeat split; try exact Logic.I; exact Hpx. }
  eapply seq_rule with (p' := V293_ready_prefix_open unmap group rows high table target
    bt bg br bh bp bo tp rest tid aop nil (true::critical) px).
  - eapply conseq_rule.
    3: { apply V293_ready_enter_critical with (P := CurTid tid ** (bindings ** px)); exact HF. }
    + intros s Hs; exact Hs.
    + intros s Hs.
      assert (HP : s |= OS[(fun _ : hid => false), false, nil, true::critical] **
        (<||aop||> ** V293_ready_snapshot bt bg br bh bp tp rest target **
          (CurTid tid ** (bindings ** px)))) by (sep auto).
      eapply astar_mono in HP; [ | apply V293_ready_disabled_flags | intros st H; exact H].
      unfold V293_ready_prefix_open. clear Hs. sep auto.
  - eapply seq_rule.
    + apply V293_ready_OSSched_prefix; assumption.
    + eapply conseq_rule with
        (p := <||aop||> ** OS[(fun _ : hid => false), false, nil, true::critical] **
          ATopis INUM ** invlth_isr I 0 INUM **
          (CurTid tid ** (bindings ** (px ** Atrue))))
        (q := V293_ready_roundtrip_post tid aop critical px).
      * intros s Hs. unfold V293_ready_prefix_done in Hs.
        sep normal in Hs. sep destruct Hs. sep split in Hs.
        assert (HP : s |= V293_ready_prefix_chosen target bt bg br bh bp tp rest tid x x0 x1 x2 **
          (<||aop||> ** CurTid tid ** Ais nil ** Acs (true::critical) **
            (bindings ** (px ** Atrue)))) by (sep auto).
        eapply astar_mono in HP; [ | intros st [Hinv _]; exact Hinv | intros st Hst; exact Hst].
        apply V293_ready_exit_resources. clear Hs. sep auto.
      * intros s Hs; exact Hs.
      * apply excrit1_rule.
        -- unfold CurTid, Agvarmapsto, Aptrmapsto, bindings, V293_sched_globals,
            V293_prefix_bindings. simpl. repeat split; try exact Logic.I; exact Hpx.
        -- intros s Hs. unfold CurLINV. exists (nil : list logicvar).
           pose proof (V293_switch_local_empty tid nil) as HL.
           assert (HP : s |= CurTid tid ** Aemp ** Atrue) by (sep auto).
           eapply astar_mono in HP; [ | intros st H; exact H | apply astar_mono;
             [exact HL | intros st H; exact H]]. sep auto.
Qed.
End ReadyCriticalRoundtrip.
