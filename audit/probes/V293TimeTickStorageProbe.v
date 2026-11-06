(* Encoded entry is independent of execution. OSRunning is a byte, not a
   truthiness flag. Initial scan storage is really allocated Vundef; only the
   real head assignment makes it a typed readable pointer. *)
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TimeTickTraversalProbe.
Require Import CertiOS.audit.probes.V293TimeTickLoopProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition StorageGlobal : env :=
  set (set (set LoopGlobal 1001%Z (101%positive,Tint32))
    1002%Z (102%positive,Tint8)) 1003%Z (103%positive,Tptr V293_tcb_type).
Definition StorageCells tick run : list V293_record_cell :=
  ((101%positive,0%Z),Tint32,Vint32 tick) ::
  ((102%positive,0%Z),Tint8,V293_byteval run) ::
  ((103%positive,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head LoopTasks LoopIdle)) ::
  tl LoopCells.
Definition StorageLocal : env := set emp 901%Z (70%positive,Tptr V293_tcb_type).
Definition StorageMemory tick run := allocb (OwnershipCellsMemory (StorageCells tick run))
  70%positive 0%Z (typelen (Tptr V293_tcb_type)).
Definition StorageState enabled M : RstateOP :=
  (StorageGlobal,StorageLocal,M,(fun _ => false),(enabled,[3%nat],[false]),emp,spec_done None).

Lemma StorageFresh : forall tick run,
  fresh (OwnershipCellsMemory (StorageCells tick run)) 70%positive.
Proof.
  intros tick run l i E [v Bound]. subst l.
  assert (Outside : get (OwnershipCellsMemory (StorageCells tick run)) (70%positive,i) = None).
  { apply OwnershipCellsOutside. vm_compute. intro Member.
    repeat destruct Member as [Member|Member]; try contradiction; discriminate. }
  change (get (OwnershipCellsMemory (StorageCells tick run)) (70%positive,i) = Some v) in Bound.
  rewrite Outside in Bound. discriminate.
Qed.

Theorem StorageEntrySatisfiable : forall tick run enabled, run<256 ->
  StorageState enabled (StorageMemory tick run) |=
    V293_tick_storage_owned 101%positive tick 102%positive run 103%positive
      (V293_tick_head LoopTasks LoopIdle) 70%positive Vundef LoopTasks LoopIdle
      92%positive 93%positive 0 0 0 LoopFrame.
Proof.
  intros tick run enabled Range.
  assert (Apart : OwnershipCellsSeparated (StorageCells tick run)).
  { vm_compute. repeat split; intros a Member Rest;
      repeat destruct Member as [Member|Member]; try contradiction; subst a; intuition discriminate. }
  assert (Valid : Forall (fun cell => let '(_,tp,v) := cell in
    rule_type_val_match tp v = true) (StorageCells tick run)).
  { apply Forall_cons; [reflexivity | ]. apply Forall_cons; [apply V293_byte_type;exact Range | ].
    repeat constructor; reflexivity. }
  pose proof (OwnershipCellsSpatial _ Apart Valid StorageGlobal StorageLocal) as Spatial.
  assert (Frame : StorageState enabled (OwnershipCellsMemory (StorageCells tick run)) |=
    V293_owned_record_cells (StorageCells tick run)).
  { unfold StorageState. eapply TickCellsRebase. exact Spatial. }
  pose proof (V293_tick_scan_allocation (fun _ => None) kstop dnil StorageGlobal emp
    (OwnershipCellsMemory (StorageCells tick run)) (fun _ => false) (enabled,[3%nat],[false])
    emp (spec_done None) 901%Z 70%positive (V293_owned_record_cells (StorageCells tick run))
    (StorageFresh tick run) ltac:(intro H; destruct H; discriminate) Frame) as Allocation.
  destruct Allocation as (Alloc & Step & Raw & Read).
  unfold V293_tick_storage_owned.
  assert (Rest : forall st, st |= V293_owned_record_cells (StorageCells tick run) ->
    st |= V293_owned_record_cell ((101%positive,0%Z),Tint32,Vint32 tick) **
      (V293_owned_record_cell ((102%positive,0%Z),Tint8,V293_byteval run) **
        (V293_owned_record_cell ((103%positive,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head LoopTasks LoopIdle)) **
          (V293_owned_record_cells (V293_tick_chain_cells LoopTasks LoopIdle) **
            (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0) **
              (V293_owned_record_cell (V293_tick_idle_cell LoopIdle) ** LoopFrame)))))).
  { intros st Held. change (st |=
      V293_owned_record_cell ((101%positive,0%Z),Tint32,Vint32 tick) **
      (V293_owned_record_cell ((102%positive,0%Z),Tint8,V293_byteval run) **
        (V293_owned_record_cell ((103%positive,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head LoopTasks LoopIdle)) **
          V293_owned_record_cells (V293_tick_chain_cells LoopTasks LoopIdle ++
            (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0 ++
              (V293_tick_idle_cell LoopIdle :: LoopFrameCells)))))) in Held.
    eapply astar_mono; [intros ? H;exact H | | exact Held].
    eapply astar_mono; [intros ? H;exact H | ].
    eapply astar_mono; [intros ? H;exact H | ].
    intros ? H. apply V293_tick_cells_append in H. eapply astar_mono; [intros ? A;exact A | | exact H].
    intros ? A. apply V293_tick_cells_append in A. exact A. }
  eapply astar_mono in Raw; [ | intros ? H;exact H | exact Rest].
  clear -Raw. sep auto.
Qed.

Theorem StorageAllocatedUninitialized : forall tick run (enabled:bool), run<256 ->
  alloc 901%Z (Tptr V293_tcb_type) emp (OwnershipCellsMemory (StorageCells tick run))
    StorageLocal (StorageMemory tick run) /\
  load (Tptr V293_tcb_type) (StorageMemory tick run) (70%positive,0%Z) = Some Vundef /\
  rule_type_val_match (Tptr V293_tcb_type) Vundef = false.
Proof.
  intros tick run enabled Range. split.
  - exists 70%positive. repeat split; try reflexivity.
    + apply StorageFresh.
    + intro H. destruct H. discriminate.
  - split; [ | reflexivity].
    change (load (Tptr V293_tcb_type) (getmem (StorageState enabled (StorageMemory tick run))) (70%positive,0%Z) = Some Vundef).
    pose proof (StorageEntrySatisfiable tick run enabled Range) as Entry.
    eapply V293_record_star_load_r; [ | exact Entry].
    eapply V293_record_star_load_r. eapply V293_record_star_load_r. eapply V293_record_star_load_l.
    intros st Slot. eapply V293_tick_raw_pointer_load; [left;reflexivity | exact Slot].
Qed.

Definition StorageExecution tick run enabled Mf :=
  V293_local_steps (fun _ => None)
    (curs (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z),(kenil,kstop))
    ((StorageGlobal,StorageLocal,StorageMemory tick run),(fun _ => false),(enabled,[3%nat],[false]))
    (curs (sskip None),(kenil,kstop)) ((StorageGlobal,StorageLocal,Mf),(fun _ => false),(enabled,[3%nat],[false])).
Definition StorageExpectedCells tick run : list V293_record_cell :=
  ((101%positive,0%Z),Tint32,Vint32 (Int.add tick Int.one)) ::
  ((102%positive,0%Z),Tint8,V293_byteval run) ::
  ((103%positive,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head LoopTasks LoopIdle)) ::
  (V293_tick_chain_cells (if Nat.eqb run 1 then LoopFinalTasks else LoopTasks) LoopIdle ++
    (V293_tick_bitmap_cells 92%positive 93%positive (if Nat.eqb run 1 then 3 else 0)
      (if Nat.eqb run 1 then 4 else 0) (if Nat.eqb run 1 then 4 else 0) ++
      (V293_tick_idle_cell LoopIdle :: LoopFrameCells))).

Theorem StorageMixedExecution : forall tick run enabled, run<256 -> exists Mf,
  StorageExecution tick run enabled Mf /\
  load (Tptr V293_tcb_type) Mf (70%positive,0%Z) = Some (if Nat.eqb run 1 then Vptr LoopIdle else Vundef) /\
  (forall a tp v, In (a,tp,v) (StorageExpectedCells tick run) -> load tp Mf a = Some v) /\
  StorageState enabled Mf |= V293_tick_storage_owned 101%positive (Int.add tick Int.one)
    102%positive run 103%positive (V293_tick_head LoopTasks LoopIdle) 70%positive (if Nat.eqb run 1 then Vptr LoopIdle else Vundef)
    (if Nat.eqb run 1 then LoopFinalTasks else LoopTasks) LoopIdle 92%positive 93%positive
    (if Nat.eqb run 1 then 3 else 0) (if Nat.eqb run 1 then 4 else 0)
    (if Nat.eqb run 1 then 4 else 0) LoopFrame.
Proof.
  intros tick run enabled Range.
  assert (TasksValid : Forall V293_tick_task_valid LoopTasks).
  { unfold LoopTasks.
    repeat (apply Forall_cons; [unfold V293_tick_task_valid; vm_compute; repeat split; try discriminate; lia | ]).
    apply Forall_nil. }
  pose proof (V293_tick_uninitialized_suffix_execution LoopTasks (fun _ => None) kstop StorageGlobal
    StorageLocal (StorageMemory tick run) (fun _ => false) enabled [3%nat] [false] emp (spec_done None)
    901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z 70%positive 101%positive 102%positive 103%positive
    LoopIdle 92%positive 93%positive tick run 0 0 0 LoopFrame
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(change (4+50<=4294967295)%Z;lia) TasksValid Range ltac:(lia) ltac:(lia) ltac:(lia)
    (StorageEntrySatisfiable tick run enabled Range)) as Run.
  destruct Run as (Mf & Exec & Time & Pointer & Returned).
  assert (Expected : map V293_tick_task_after LoopTasks = LoopFinalTasks) by reflexivity.
  assert (Final : StorageState enabled Mf |= V293_tick_storage_owned 101%positive (Int.add tick Int.one)
    102%positive run 103%positive (V293_tick_head LoopTasks LoopIdle) 70%positive (if Nat.eqb run 1 then Vptr LoopIdle else Vundef)
    (if Nat.eqb run 1 then LoopFinalTasks else LoopTasks) LoopIdle 92%positive 93%positive
    (if Nat.eqb run 1 then 3 else 0) (if Nat.eqb run 1 then 4 else 0)
    (if Nat.eqb run 1 then 4 else 0) LoopFrame).
  { destruct (Nat.eqb run 1); cbn beta iota zeta in Returned |- *; rewrite ?Expected in Returned; exact Returned. }
  exists Mf. split; [exact Exec | ]. split; [exact Pointer | ]. split; [ | exact Final].
  intros a tp v Member.
  assert (Typed : forall st, st |= V293_tick_storage_owned 101%positive (Int.add tick Int.one)
    102%positive run 103%positive (V293_tick_head LoopTasks LoopIdle) 70%positive
    (if Nat.eqb run 1 then Vptr LoopIdle else Vundef)
    (if Nat.eqb run 1 then LoopFinalTasks else LoopTasks) LoopIdle 92%positive 93%positive
    (if Nat.eqb run 1 then 3 else 0) (if Nat.eqb run 1 then 4 else 0)
    (if Nat.eqb run 1 then 4 else 0) LoopFrame ->
    st |= V293_owned_record_cells (StorageExpectedCells tick run) **
      Amapsto (70%positive,0%Z) (Tptr V293_tcb_type) true
        (if Nat.eqb run 1 then Vptr LoopIdle else Vundef)).
  { intros st Held. unfold V293_tick_storage_owned in Held.
    assert (Packed : st |=
      (V293_owned_record_cell ((101%positive,0%Z),Tint32,Vint32 (Int.add tick Int.one)) **
        (V293_owned_record_cell ((102%positive,0%Z),Tint8,V293_byteval run) **
          (V293_owned_record_cell ((103%positive,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head LoopTasks LoopIdle)) **
            (V293_owned_record_cells (V293_tick_chain_cells (if Nat.eqb run 1 then LoopFinalTasks else LoopTasks) LoopIdle) **
              (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive
                (if Nat.eqb run 1 then 3 else 0) (if Nat.eqb run 1 then 4 else 0) (if Nat.eqb run 1 then 4 else 0)) **
                (V293_owned_record_cell (V293_tick_idle_cell LoopIdle) ** LoopFrame)))))) **
      Amapsto (70%positive,0%Z) (Tptr V293_tcb_type) true
        (if Nat.eqb run 1 then Vptr LoopIdle else Vundef)).
    { clear -Held. sep auto. }
    eapply astar_mono; [ | intros ? H;exact H | exact Packed].
    unfold StorageExpectedCells. cbn [V293_owned_record_cells].
    eapply astar_mono; [intros ? H;exact H | ].
    eapply astar_mono; [intros ? H;exact H | ].
    eapply astar_mono; [intros ? H;exact H | ].
    intros s H. apply V293_tick_cells_append. eapply astar_mono; [intros ? A;exact A | | exact H].
    intros s0 A. apply V293_tick_cells_append. exact A. }
  change (load tp (getmem (StorageState enabled Mf)) a = Some v).
  eapply V293_record_star_load_l; [ | apply Typed;exact Final].
  intros st Held. eapply V293_owned_record_cells_load; [exact Member | exact Held].
Qed.

Lemma StorageUint32Wrap : Int.add (Int.repr 4294967295) Int.one = Int.zero.
Proof.
  change (Int.repr 4294967296 = Int.repr 0).
  apply Int.eqm_samerepr. unfold Int.eqm,Int.eqmod. exists 1%Z. reflexivity.
Qed.

Theorem StorageRunningOneWrapped : forall enabled, exists Mf,
  StorageExecution (Int.repr 4294967295) 1 enabled Mf /\
  load Tint32 Mf (101%positive,0%Z) = Some (Vint32 Int.zero) /\
  load Tint32 Mf (82%positive,56%Z) = Some (Vint32 (Int.repr 2)) /\
  load Tint8 Mf (92%positive,0%Z) = Some (V293_byteval 3).
Proof.
  intro enabled. destruct (StorageMixedExecution (Int.repr 4294967295) 1 enabled ltac:(lia))
    as (Mf & Exec & Pointer & Fields & Returned).
  exists Mf. split; [exact Exec| ]. split.
  - rewrite <- StorageUint32Wrap. apply Fields. unfold StorageExpectedCells. left. reflexivity.
  - split; apply Fields; unfold StorageExpectedCells; vm_compute; tauto.
Qed.

Theorem StorageRunningTwoNotTrue : forall enabled, exists Mf,
  StorageExecution Int.zero 2 enabled Mf /\
  load Tint32 Mf (101%positive,0%Z) = Some (Vint32 Int.one) /\
  load Tint32 Mf (82%positive,56%Z) = Some (Vint32 (Int.repr 3)) /\
  load Tint8 Mf (92%positive,0%Z) = Some (V293_byteval 0).
Proof.
  intro enabled. destruct (StorageMixedExecution Int.zero 2 enabled ltac:(lia))
    as (Mf & Exec & Pointer & Fields & Returned).
  exists Mf. split; [exact Exec| ]. repeat split; apply Fields;
    unfold StorageExpectedCells; vm_compute; tauto.
Qed.

Theorem StorageRunningZeroStillTicks : forall enabled, exists Mf,
  StorageExecution (Int.repr 4294967295) 0 enabled Mf /\
  load Tint32 Mf (101%positive,0%Z) = Some (Vint32 Int.zero) /\
  load Tint32 Mf (82%positive,56%Z) = Some (Vint32 (Int.repr 3)) /\
  load Tint8 Mf (92%positive,0%Z) = Some (V293_byteval 0).
Proof.
  intro enabled. destruct (StorageMixedExecution (Int.repr 4294967295) 0 enabled ltac:(lia))
    as (Mf & Exec & Pointer & Fields & Returned).
  exists Mf. split; [exact Exec| ]. split.
  - rewrite <- StorageUint32Wrap. apply Fields. unfold StorageExpectedCells. left. reflexivity.
  - split; apply Fields; unfold StorageExpectedCells; vm_compute; tauto.
Qed.

Print Assumptions StorageAllocatedUninitialized.
Print Assumptions StorageEntrySatisfiable.
Print Assumptions StorageMixedExecution.
Print Assumptions StorageRunningOneWrapped.
Print Assumptions StorageRunningTwoNotTrue.
Print Assumptions StorageRunningZeroStillTicks.
