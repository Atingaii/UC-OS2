(* Independent literal spatial witnesses.  No completed execution trace is
   used as an entry proof; these are resource-layout tests, not API proofs. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition expected_owned_records_sound : Prop := forall tasks s,
  s |= V293_owned_task_records tasks -> V293_task_records (getmem s) tasks.
Definition expected_shared_records_sound : Prop := forall current tasks events now s,
  s |= V293_shared_task_records current tasks events now ->
  get (getabst s) abstcblsid = Some (abstcblist tasks) /\
  V293_task_records (getmem s) tasks.
Theorem OwnershipContract : expected_owned_records_sound.
Proof. exact V293_owned_task_records_sound. Qed.
Theorem SharedOwnershipContract : expected_shared_records_sound.
Proof. exact V293_shared_task_records_sound. Qed.

Fixpoint OwnershipBytesAddresses b offset (bytes : list memval) : list addr :=
  match bytes with
  | [] => []
  | _ :: rest => (b,offset) :: OwnershipBytesAddresses b (offset+1)%Z rest
  end.
Definition OwnershipCellAddresses (cell : V293_record_cell) :=
  let '(a,tp,v) := cell in OwnershipBytesAddresses (fst a) (snd a) (encode_val tp v).
Fixpoint OwnershipCellsAddresses (cells : list V293_record_cell) :=
  match cells with
  | [] => []
  | cell :: rest => OwnershipCellAddresses cell ++ OwnershipCellsAddresses rest
  end.
Definition OwnershipCellMemory (cell : V293_record_cell) : mem :=
  let '(a,tp,v) := cell in V293_encoded_memory (fst a) (snd a) true (encode_val tp v).
Fixpoint OwnershipCellsMemory (cells : list V293_record_cell) : mem :=
  match cells with
  | [] => emp
  | cell :: rest => merge (OwnershipCellMemory cell) (OwnershipCellsMemory rest)
  end.
Fixpoint OwnershipCellsSeparated (cells : list V293_record_cell) : Prop :=
  match cells with
  | [] => True
  | cell :: rest =>
      (forall a, In a (OwnershipCellAddresses cell) ->
        ~ In a (OwnershipCellsAddresses rest)) /\ OwnershipCellsSeparated rest
  end.

Lemma OwnershipBytesOutside : forall bytes b offset a,
  ~ In a (OwnershipBytesAddresses b offset bytes) ->
  get (V293_encoded_memory b offset true bytes) a = None.
Proof.
  induction bytes as [ | byte rest IH]; intros b offset a Outside; [apply map_emp_get | ].
  cbn [V293_encoded_memory]. rewrite map_merge_semp by reflexivity.
  rewrite map_get_sig' by (intro E; subst a; apply Outside; left; reflexivity).
  rewrite IH; [reflexivity | intro Member; apply Outside; right; exact Member].
Qed.
Lemma OwnershipCellsOutside : forall cells a,
  ~ In a (OwnershipCellsAddresses cells) -> get (OwnershipCellsMemory cells) a = None.
Proof.
  induction cells as [ | [[[b offset] tp] v] rest IH]; intros a Outside; [apply map_emp_get | ].
  cbn [OwnershipCellsMemory OwnershipCellMemory]. rewrite map_merge_semp by reflexivity.
  rewrite OwnershipBytesOutside.
  - rewrite IH; [reflexivity | intro Member; apply Outside; apply in_or_app; right; exact Member].
  - intro Member. apply Outside. apply in_or_app. left; exact Member.
Qed.
Lemma OwnershipCellsJoin : forall cell rest,
  (forall a, In a (OwnershipCellAddresses cell) -> ~ In a (OwnershipCellsAddresses rest)) ->
  join (OwnershipCellMemory cell) (OwnershipCellsMemory rest)
    (merge (OwnershipCellMemory cell) (OwnershipCellsMemory rest)).
Proof.
  intros [[[b offset] tp] v] rest Separated.
  apply map_join_merge. apply map_disjoint. intro a.
  destruct (in_dec addr_eq_dec a (OwnershipBytesAddresses b offset (encode_val tp v))) as [Inside | Outside].
  - right; left. apply OwnershipCellsOutside. apply Separated; exact Inside.
  - left. apply OwnershipBytesOutside; exact Outside.
Qed.
Lemma OwnershipCellsSpatial : forall cells,
  OwnershipCellsSeparated cells ->
  Forall (fun cell => let '(_,tp,v) := cell in rule_type_val_match tp v = true) cells ->
  forall ge le, V293_wstate ge le (OwnershipCellsMemory cells) |= V293_owned_record_cells cells.
Proof.
  induction cells as [ | [[[b offset] tp] v] rest IH]; intros Separated Valid ge le.
  - split; reflexivity.
  - destruct Separated as [Apart Separated]. inversion Valid; subst.
    eapply V293_wstate_star.
    + apply OwnershipCellsJoin; exact Apart.
    + unfold V293_owned_record_cell. apply astar_l_apure_intro.
      * split; [apply V293_encoded_memory_mapsto | reflexivity].
      * assumption.
    + apply IH; assumption.
Qed.

Definition OwnershipReady : tid := (60%positive,Int.zero).
Definition OwnershipWaiting : tid := (41%positive,Int.repr 8).
Definition OwnershipTasks : TcbMod.map :=
  set (sig OwnershipReady (Int.repr 4,rdy,Vnull)) OwnershipWaiting
    (Int.repr 6,wait (os_stat_sem (72%positive,Int.repr 5)) Int.one,
      Vptr (120%positive,Int.repr 7)).
Definition OwnershipEntryCells (entry : tid * abstcb.B) : list V293_record_cell :=
  let '(t,(p,st,msg)) := entry in V293_record_layout t (Z.to_nat (Int.unsigned p)) st msg 0.
Definition OwnershipAllCells := flat_map OwnershipEntryCells (TcbMod.lst OwnershipTasks).
Definition OwnershipMemory := OwnershipCellsMemory OwnershipAllCells.

Lemma OwnershipLiteralSeparated : OwnershipCellsSeparated OwnershipAllCells.
Proof. vm_compute. repeat split; intros; intuition congruence. Qed.
Lemma OwnershipLiteralValid : Forall
  (fun cell => let '(_,tp,v) := cell in rule_type_val_match tp v = true) OwnershipAllCells.
Proof. repeat constructor; vm_compute; reflexivity. Qed.

Lemma OwnershipCellsAppend : forall left right,
  V293_owned_record_cells (left ++ right) <==>
  V293_owned_record_cells left ** V293_owned_record_cells right.
Proof.
  induction left as [ | cell rest IH]; intro right.
  - intros s. simpl. split; [apply astar_l_aemp_intro | apply astar_l_aemp_elim].
  - intros s. simpl. split; intro Owned.
    + apply astar_assoc_intro. eapply astar_mono;
        [intros st H; exact H | intros st H; apply (proj1 (IH right st)); exact H | exact Owned].
    + apply astar_assoc_elim in Owned. eapply astar_mono;
        [intros st H; exact H | intros st H; apply (proj2 (IH right st)); exact H | exact Owned].
Qed.

Theorem OwnershipLiteralSpatial :
  V293_wstate emp emp OwnershipMemory |= V293_owned_task_records OwnershipTasks.
Proof.
  pose proof (OwnershipCellsSpatial _ OwnershipLiteralSeparated OwnershipLiteralValid emp emp) as Cells.
  change (V293_wstate emp emp OwnershipMemory |=
    V293_owned_record_cells (OwnershipEntryCells (OwnershipWaiting,
      (Int.repr 6,wait (os_stat_sem (72%positive,Int.repr 5)) Int.one,Vptr (120%positive,Int.repr 7))) ++
      OwnershipEntryCells (OwnershipReady,(Int.repr 4,rdy,Vnull)))) in Cells.
  apply OwnershipCellsAppend in Cells.
  unfold V293_owned_task_records. change (V293_wstate emp emp OwnershipMemory |=
    V293_owned_task_record OwnershipWaiting (Int.repr 6)
      (wait (os_stat_sem (72%positive,Int.repr 5)) Int.one) (Vptr (120%positive,Int.repr 7)) **
    (V293_owned_task_record OwnershipReady (Int.repr 4) rdy Vnull ** Aemp)).
  eapply astar_mono; [ | | exact Cells].
  - intros s H. exists 6. exists 0. apply astar_l_apure_intro; [exact H | repeat split; reflexivity || lia].
  - intros s H. apply astar_r_aemp_intro. exists 4. exists 0.
    apply astar_l_apure_intro; [exact H | repeat split; reflexivity || lia].
Qed.

Theorem OwnershipLiteralRecords : V293_task_records OwnershipMemory OwnershipTasks.
Proof. exact (OwnershipContract _ _ OwnershipLiteralSpatial). Qed.
Theorem OwnershipLiteralFields :
  load Tint8 OwnershipMemory (41%positive,58%Z) = Some (V293_byteval 6) /\
  load Tint8 OwnershipMemory (41%positive,56%Z) = Some (V293_byteval 1) /\
  load Tint8 OwnershipMemory (60%positive,48%Z) = Some (V293_byteval 0) /\
  load (Tcom_ptr 411%Z) OwnershipMemory (41%positive,36%Z) =
    Some (Vptr (72%positive,Int.repr 5)).
Proof.
  pose proof (OwnershipCellsSpatial _ OwnershipLiteralSeparated OwnershipLiteralValid emp emp) as Cells.
  repeat split; eapply V293_owned_record_cells_load with
    (cells := OwnershipAllCells) (s := V293_wstate emp emp OwnershipMemory);
    [ vm_compute; intuition congruence | exact Cells
    | vm_compute; intuition congruence | exact Cells
    | vm_compute; intuition congruence | exact Cells
    | vm_compute; intuition congruence | exact Cells ].
Qed.

Definition OwnershipPointerMemory := V293_encoded_memory 1%positive 0%Z false
  (encode_val (Tptr Tvoid) (Vptr OwnershipReady)).
Definition OwnershipSharedMemory := merge OwnershipPointerMemory OwnershipMemory.
Definition OwnershipSharedAbs :=
  V293_shared_fixture_abs OwnershipReady OwnershipTasks (emp : EcbMod.map) Int.zero.

Lemma OwnershipPointerTasksJoin :
  join OwnershipPointerMemory OwnershipMemory OwnershipSharedMemory.
Proof.
  apply map_join_merge. apply map_disjoint. intros [b i].
  destruct (Pos.eq_dec b 1%positive) as [Same | Apart].
  - subst b. right; left. apply OwnershipCellsOutside.
    intro Member. vm_compute in Member. intuition congruence.
  - left. apply V293_encoded_memory_outside. left; exact Apart.
Qed.

Lemma OwnershipPointerSpatial :
  V293_target_wstate V293_shared_fixture_ge emp OwnershipPointerMemory emp |= CurTid OwnershipReady.
Proof.
  exists Tvoid. exists 1%positive.
  eapply V293_target_wstate_star with
    (m1 := emp) (m2 := OwnershipPointerMemory) (o1 := emp) (o2 := emp).
  - apply map_join_comm; apply map_join_emp.
  - apply map_join_emp.
  - exists 1%positive. split; [apply map_get_sig | ]. repeat split; reflexivity.
  - split; [apply V293_encoded_memory_mapsto | reflexivity].
Qed.

Theorem OwnershipSharedLiteralSpatial :
  V293_target_wstate V293_shared_fixture_ge emp OwnershipSharedMemory OwnershipSharedAbs |=
  V293_shared_task_records OwnershipReady OwnershipTasks (emp : EcbMod.map) Int.zero.
Proof.
  unfold V293_shared_task_records.
  eapply V293_target_wstate_star with
    (m1 := OwnershipPointerMemory) (m2 := OwnershipMemory)
    (o1 := OwnershipSharedAbs) (o2 := emp).
  - apply OwnershipPointerTasksJoin.
  - apply map_join_emp.
  - eapply V293_target_wstate_star with
      (m1 := OwnershipPointerMemory) (m2 := emp)
      (o1 := emp) (o2 := OwnershipSharedAbs).
    + apply map_join_emp.
    + apply map_join_comm; apply map_join_emp.
    + apply OwnershipPointerSpatial.
    + apply V293_shared_fixture_fields.
  - exact (OwnershipLiteralSpatial).
Qed.

Theorem OwnershipSharedLiteralRecords :
  get OwnershipSharedAbs abstcblsid = Some (abstcblist OwnershipTasks) /\
  V293_task_records OwnershipSharedMemory OwnershipTasks.
Proof. exact (SharedOwnershipContract _ _ _ _ _ OwnershipSharedLiteralSpatial). Qed.

(* A one-byte semantic counterexample: the value really can be read, yet
   the full write resource cannot be reconstructed and a store cannot run. *)
Definition OwnershipReadOnlyCell : mem :=
  V293_encoded_memory 41%positive 58%Z false (encode_val Tint8 (V293_byteval 6)).
Theorem OwnershipReadableNotWritable :
  load Tint8 OwnershipReadOnlyCell (41%positive,58%Z) = Some (V293_byteval 6) /\
  ~ V293_wstate emp emp OwnershipReadOnlyCell |=
      V293_owned_record_cell ((41%positive,58%Z),Tint8,V293_byteval 6) /\
  ~ exists Mf, store Tint8 OwnershipReadOnlyCell (41%positive,58%Z) (V293_byteval 7) = Some Mf.
Proof.
  assert (NoStore : ~ exists Mf,
    store Tint8 OwnershipReadOnlyCell (41%positive,58%Z) (V293_byteval 7) = Some Mf).
  { intros [Mf Store].
    change (match get OwnershipReadOnlyCell (41%positive,58%Z) with
      | Some (true,_) => Some (set OwnershipReadOnlyCell (41%positive,58%Z)
          (true,Byte (Byte.repr 7)))
      | _ => None end = Some Mf) in Store.
    assert (ReadPermission : get OwnershipReadOnlyCell (41%positive,58%Z) =
      Some (false,Byte (Byte.repr 6))).
    { unfold OwnershipReadOnlyCell.
      change (get (merge (sig (41%positive,58%Z) (false,Byte (Byte.repr 6))) emp)
        (41%positive,58%Z) = Some (false,Byte (Byte.repr 6))).
      rewrite map_merge_semp by reflexivity. rewrite map_get_sig. reflexivity. }
    rewrite ReadPermission in Store. discriminate.
  }
  split.
  - eapply mapstoval_load with (perm := false).
    + vm_compute; reflexivity.
    + apply V293_encoded_memory_mapsto.
  - split; [ | exact NoStore]. intro Owned. apply NoStore.
    exact (V293_owned_record_cell_store _ _ _ (V293_byteval 7) _ Owned).

Qed.

Print Assumptions OwnershipContract.
Print Assumptions SharedOwnershipContract.
Print Assumptions OwnershipLiteralSpatial.
Print Assumptions OwnershipLiteralRecords.
Print Assumptions OwnershipLiteralFields.
Print Assumptions OwnershipSharedLiteralSpatial.
Print Assumptions OwnershipSharedLiteralRecords.
Print Assumptions OwnershipReadableNotWritable.
