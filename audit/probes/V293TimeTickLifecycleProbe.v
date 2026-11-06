(* Lifecycle fixture: encoded entry is independent of execution. OSRunning is a byte, not a
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

Require Import CertiOS.audit.probes.V293TimeTickStorageProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.framework.proof.memory_prop.
Local Open Scope nat_scope.

Definition LifecycleLocal := V293_tick_locals 901%Z 904%Z 70%positive 71%positive.
Definition LifecycleCaller : env := set emp 777%Z (101%positive,Tint32).
Definition LifecycleBody :=
  sseq (V293_tick_body 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 2002%Z) sret.
Definition LifecycleProgram (f:fid) :=
  if Z.eq_dec f 2001%Z then
    Some (V293_tick_function 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 2002%Z)
  else None.
Definition LifecycleBase tick run := OwnershipCellsMemory (StorageCells tick run).
Definition LifecycleState enabled M : RstateOP :=
  (StorageGlobal,LifecycleLocal,M,(fun _ => false),(enabled,[3%nat],[false]),emp,spec_done None).
Definition LifecycleHookContinuation :=
  kseq (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z)
    (kseq sret (kcall 2001%Z LifecycleBody LifecycleCaller kstop)).
Definition LifecyclePrefix tick run enabled Mp :=
  V293_local_steps LifecycleProgram (curs (scall 2001%Z nil),(kenil,kstop))
    ((StorageGlobal,LifecycleCaller,LifecycleBase tick run),(fun _ => false),(enabled,[3%nat],[false]))
    (curs (scall 2002%Z nil),(kenil,LifecycleHookContinuation))
    ((StorageGlobal,LifecycleLocal,Mp),(fun _ => false),(enabled,[3%nat],[false])).
Definition LifecycleTail enabled Mp Mf :=
  V293_local_steps LifecycleProgram (curs (sskip None),(kenil,LifecycleHookContinuation))
    ((StorageGlobal,LifecycleLocal,Mp),(fun _ => false),(enabled,[3%nat],[false]))
    (curs (sskip None),(kenil,kstop))
    ((StorageGlobal,LifecycleCaller,Mf),(fun _ => false),(enabled,[3%nat],[false])).

Lemma LifecycleFreshSaved : forall tick run,
  fresh (allocb (LifecycleBase tick run) 70%positive 0%Z 4) 71%positive.
Proof.
  intros tick run l i E [v Bound]. subst l.
  assert (Outside : get (LifecycleBase tick run) (71%positive,i) = None).
  { apply OwnershipCellsOutside. vm_compute. intro Member.
    repeat destruct Member as [Member|Member]; try contradiction; discriminate. }
  change (get (allocb (LifecycleBase tick run) 70%positive 0%Z 4) (71%positive,i) = Some v) in Bound.
  rewrite V293_success_allocb_outside in Bound by (left;discriminate).
  change (get (LifecycleBase tick run) (71%positive,i) = Some v) in Bound.
  rewrite Outside in Bound. discriminate.
Qed.

Lemma LifecycleBaseOwned : forall tick run enabled, run<256 ->
  LifecycleState enabled (LifecycleBase tick run) |= V293_owned_record_cells (StorageCells tick run).
Proof.
  intros tick run enabled Range.
  assert (Apart : OwnershipCellsSeparated (StorageCells tick run)).
  { vm_compute. repeat split; intros a Member Rest;
      repeat destruct Member as [Member|Member]; try contradiction; subst a; intuition discriminate. }
  assert (Valid : Forall (fun cell => let '(_,tp,v) := cell in
    rule_type_val_match tp v = true) (StorageCells tick run)).
  { apply Forall_cons; [reflexivity | ]. apply Forall_cons; [apply V293_byte_type;exact Range | ].
    repeat constructor; reflexivity. }
  pose proof (OwnershipCellsSpatial _ Apart Valid StorageGlobal LifecycleLocal) as Spatial.
  unfold LifecycleState,LifecycleBase. eapply TickCellsRebase. exact Spatial.
Qed.

Lemma LifecycleCellsSplit : forall tick run st,
  st |= V293_owned_record_cells (StorageCells tick run) ->
  st |= V293_owned_record_cell ((101%positive,0%Z),Tint32,Vint32 tick) **
    (V293_owned_record_cell ((102%positive,0%Z),Tint8,V293_byteval run) **
      (V293_owned_record_cell ((103%positive,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head LoopTasks LoopIdle)) **
        (V293_owned_record_cells (V293_tick_chain_cells LoopTasks LoopIdle) **
          (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0) **
            (V293_owned_record_cell (V293_tick_idle_cell LoopIdle) ** LoopFrame))))).
Proof.
  intros tick run st Held. change (st |=
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
  intros ? A. apply V293_tick_cells_append in A. exact A.
Qed.

Lemma LifecycleReadExpected : forall tick run enabled Ms,
  LifecycleState enabled Ms |= V293_tick_storage_owned 101%positive (Int.add tick Int.one)
    102%positive run 103%positive (V293_tick_head LoopTasks LoopIdle) 70%positive (if Nat.eqb run 1 then Vptr LoopIdle else Vundef)
    (if Nat.eqb run 1 then LoopFinalTasks else LoopTasks) LoopIdle 92%positive 93%positive
    (if Nat.eqb run 1 then 3 else 0) (if Nat.eqb run 1 then 4 else 0)
    (if Nat.eqb run 1 then 4 else 0)
    (V293_owned_record_cell ((71%positive,0%Z),Tint32,Vint32 Int.zero) ** LoopFrame) ->
  forall a tp v, In (a,tp,v) (StorageExpectedCells tick run) -> load tp Ms a = Some v.
Proof.
  intros tick run enabled Ms Final a tp v Member.
  assert (Typed : forall st, st |= V293_tick_storage_owned 101%positive (Int.add tick Int.one)
    102%positive run 103%positive (V293_tick_head LoopTasks LoopIdle) 70%positive
    (if Nat.eqb run 1 then Vptr LoopIdle else Vundef)
    (if Nat.eqb run 1 then LoopFinalTasks else LoopTasks) LoopIdle 92%positive 93%positive
    (if Nat.eqb run 1 then 3 else 0) (if Nat.eqb run 1 then 4 else 0)
    (if Nat.eqb run 1 then 4 else 0) (V293_owned_record_cell ((71%positive,0%Z),Tint32,Vint32 Int.zero) ** LoopFrame) ->
    st |= V293_owned_record_cells (StorageExpectedCells tick run) **
      (V293_owned_record_cell ((71%positive,0%Z),Tint32,Vint32 Int.zero) ** Amapsto (70%positive,0%Z) (Tptr V293_tcb_type) true
        (if Nat.eqb run 1 then Vptr LoopIdle else Vundef))).
  { intros st Held. unfold V293_tick_storage_owned in Held.
    assert (Packed : st |=
      (V293_owned_record_cell ((101%positive,0%Z),Tint32,Vint32 (Int.add tick Int.one)) **
        (V293_owned_record_cell ((102%positive,0%Z),Tint8,V293_byteval run) **
          (V293_owned_record_cell ((103%positive,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head LoopTasks LoopIdle)) **
            (V293_owned_record_cells (V293_tick_chain_cells (if Nat.eqb run 1 then LoopFinalTasks else LoopTasks) LoopIdle) **
              (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive
                (if Nat.eqb run 1 then 3 else 0) (if Nat.eqb run 1 then 4 else 0) (if Nat.eqb run 1 then 4 else 0)) **
                (V293_owned_record_cell (V293_tick_idle_cell LoopIdle) ** LoopFrame)))))) **
      (V293_owned_record_cell ((71%positive,0%Z),Tint32,Vint32 Int.zero) ** Amapsto (70%positive,0%Z) (Tptr V293_tcb_type) true
        (if Nat.eqb run 1 then Vptr LoopIdle else Vundef))).
    { clear -Held. sep auto. }
    eapply astar_mono; [ | intros ? H;exact H | exact Packed].
    unfold StorageExpectedCells. cbn [V293_owned_record_cells].
    eapply astar_mono; [intros ? H;exact H | ].
    eapply astar_mono; [intros ? H;exact H | ].
    eapply astar_mono; [intros ? H;exact H | ].
    intros s H. apply V293_tick_cells_append. eapply astar_mono; [intros ? A;exact A | | exact H].
    intros s0 A. apply V293_tick_cells_append. exact A. }
  change (load tp (getmem (LifecycleState enabled Ms)) a = Some v).
  eapply V293_record_star_load_l; [ | apply Typed;exact Final].
  intros st Held. eapply V293_owned_record_cells_load; [exact Member | exact Held].
Qed.

(* These are TWO checkpoints with a deliberately unproved hook transition,
   not a complete call trace. They share Mp, not independent witnesses. *)
Theorem LifecycleSameMemoryCheckpoints : forall tick run enabled, run<256 -> exists Mp Ms Mf,
  LifecyclePrefix tick run enabled Mp /\
  load (Tptr V293_tcb_type) Mp (70%positive,0%Z) = Some Vundef /\
  load Tint32 Mp (71%positive,0%Z) = Some (Vint32 Int.zero) /\
  LifecycleTail enabled Mp Mf /\
  load Tint32 Mf (101%positive,0%Z) = Some (Vint32 (Int.add tick Int.one)) /\
  load (Tptr V293_tcb_type) Ms (70%positive,0%Z) = Some (if Nat.eqb run 1 then Vptr LoopIdle else Vundef) /\
  (forall a tp v, In (a,tp,v) (StorageExpectedCells tick run) -> load tp Mf a = Some v) /\
  (forall b i, b<>70%positive -> b<>71%positive -> get Mf (b,i) = get Ms (b,i)) /\
  (forall k, k<4 -> get Mf (70%positive,Z.of_nat k) = None /\ get Mf (71%positive,Z.of_nat k) = None).
Proof.
  intros tick run enabled Range.
  destruct (V293_tick_call_to_hook LifecycleProgram kstop StorageGlobal LifecycleCaller
    (LifecycleBase tick run) (fun _ => false) enabled [3%nat] [false] emp (spec_done None)
    2001%Z 901%Z 902%Z 903%Z 904%Z 1001%Z 1002%Z 1003%Z 2002%Z
    70%positive 71%positive (V293_owned_record_cells (StorageCells tick run))
    eq_refl ltac:(discriminate) (StorageFresh tick run) (LifecycleFreshSaved tick run)
    (LifecycleBaseOwned tick run enabled Range)) as (Mp & Prefix & RawScan & ZeroSaved & Owned).
  assert (Entry : LifecycleState enabled Mp |=
    V293_tick_storage_owned 101%positive tick 102%positive run 103%positive
      (V293_tick_head LoopTasks LoopIdle) 70%positive Vundef LoopTasks LoopIdle 92%positive 93%positive 0 0 0
      (V293_owned_record_cell ((71%positive,0%Z),Tint32,Vint32 Int.zero) ** LoopFrame)).
  { eapply astar_mono in Owned; [ | intros ? H;exact H | ].
    2: { eapply astar_mono; [intros ? H;exact H | apply LifecycleCellsSplit]. }
    unfold LifecycleState,V293_tick_storage_owned. clear -Owned. sep auto. }
  assert (TasksValid : Forall V293_tick_task_valid LoopTasks).
  { unfold LoopTasks.
    repeat (apply Forall_cons; [unfold V293_tick_task_valid; vm_compute; repeat split; try discriminate; lia | ]).
    apply Forall_nil. }
  destruct (V293_tick_suffix_void_lifecycle LoopTasks LifecycleProgram kstop StorageGlobal LifecycleCaller Mp
    (fun _ => false) enabled [3%nat] [false] emp (spec_done None)
    901%Z 904%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z 70%positive 71%positive
    101%positive 102%positive 103%positive LoopIdle 92%positive 93%positive tick run 0 0 0
    2001%Z LifecycleBody LoopFrame ltac:(discriminate) ltac:(discriminate)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(change (4+50<=4294967295)%Z;lia) TasksValid Range ltac:(lia) ltac:(lia) ltac:(lia) Entry)
    as (Ms & Mf & Tail & Time & Scan & Returned & Frame & Removed).
  assert (FinalTime : load Tint32 Mf (101%positive,0%Z) = Some (Vint32 (Int.add tick Int.one))).
  { etransitivity; [apply V293_load_block_frame;intro i;apply Frame;discriminate | exact Time]. }
  assert (Final : LifecycleState enabled Ms |= V293_tick_storage_owned 101%positive (Int.add tick Int.one)
    102%positive run 103%positive (V293_tick_head LoopTasks LoopIdle) 70%positive (if Nat.eqb run 1 then Vptr LoopIdle else Vundef)
    (if Nat.eqb run 1 then LoopFinalTasks else LoopTasks) LoopIdle 92%positive 93%positive
    (if Nat.eqb run 1 then 3 else 0) (if Nat.eqb run 1 then 4 else 0)
    (if Nat.eqb run 1 then 4 else 0)
    (V293_owned_record_cell ((71%positive,0%Z),Tint32,Vint32 Int.zero) ** LoopFrame)).
  { assert (Expected : map V293_tick_task_after LoopTasks = LoopFinalTasks) by reflexivity.
    destruct (Nat.eqb run 1); cbn beta iota zeta in Returned |- *; rewrite ?Expected in Returned; exact Returned. }
  assert (Fields : forall a tp v, In (a,tp,v) (StorageExpectedCells tick run) -> load tp Mf a = Some v).
  { intros [b off] tp v Member.
    assert (NotLocal : b<>70%positive /\ b<>71%positive).
    { apply in_map with (f:=fun cell : V293_record_cell => fst (fst cell)) in Member.
      unfold StorageExpectedCells in Member. destruct (Nat.eqb run 1); vm_compute in Member;
        intuition congruence. }
    etransitivity.
    - apply V293_load_block_frame. intro i. apply Frame; tauto.
    - eapply LifecycleReadExpected; [exact Final | exact Member]. }
  exists Mp. exists Ms. exists Mf.
  split; [exact Prefix | ]. split; [exact RawScan | ]. split; [exact ZeroSaved | ].
  split; [exact Tail | ]. split; [exact FinalTime | ]. split; [exact Scan | ]. split; [exact Fields | ]. split; assumption.
Qed.

Theorem LifecycleRunOneWrap : forall enabled, exists Mp Mf,
  LifecyclePrefix (Int.repr 4294967295) 1 enabled Mp /\ LifecycleTail enabled Mp Mf /\
  load Tint32 Mf (101%positive,0%Z) = Some (Vint32 Int.zero) /\
  get Mf (70%positive,0%Z) = None /\ get Mf (71%positive,0%Z) = None.
Proof.
  intro enabled. destruct (LifecycleSameMemoryCheckpoints (Int.repr 4294967295) 1 enabled ltac:(lia))
    as (Mp & Ms & Mf & Prefix & Raw & Zero & Tail & Time & Scan & Fields & Frame & Removed).
  exists Mp. exists Mf. split; [exact Prefix | ]. split; [exact Tail | ]. split.
  - rewrite StorageUint32Wrap in Time. exact Time.
  - apply (Removed 0 ltac:(lia)).
Qed.

Theorem LifecycleRunTwoNotTrue : forall enabled, exists Mp Ms Mf,
  LifecyclePrefix Int.zero 2 enabled Mp /\ LifecycleTail enabled Mp Mf /\
  load (Tptr V293_tcb_type) Ms (70%positive,0%Z) = Some Vundef /\
  load Tint32 Mf (101%positive,0%Z) = Some (Vint32 Int.one).
Proof.
  intro enabled. destruct (LifecycleSameMemoryCheckpoints Int.zero 2 enabled ltac:(lia))
    as (Mp & Ms & Mf & Prefix & Raw & Zero & Tail & Time & Scan & Fields & Frame & Removed).
  exists Mp. exists Ms. exists Mf. split; [exact Prefix | ]. split; [exact Tail | ].
  split; [exact Scan | exact Time].
Qed.

Theorem LifecycleHookNotDefined : LifecycleProgram 2002%Z = None.
Proof. reflexivity. Qed.

Print Assumptions LifecycleBaseOwned.
Print Assumptions LifecycleSameMemoryCheckpoints.
Print Assumptions LifecycleRunOneWrap.
Print Assumptions LifecycleRunTwoNotTrue.
Print Assumptions LifecycleHookNotDefined.
