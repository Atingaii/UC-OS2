(* Encoded entry is independent of execution. OSRunning is a byte, not a
   truthiness flag. Initial scan=idle; only real head assignment reaches tasks. *)
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TimeTickTraversalProbe.
Require Import CertiOS.audit.probes.V293TimeTickLoopProbe.
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
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition SuffixGlobal : env :=
  set (set (set LoopGlobal 1001%Z (101%positive,Tint32))
    1002%Z (102%positive,Tint8)) 1003%Z (103%positive,Tptr V293_tcb_type).
Definition SuffixCells tick run : list V293_record_cell :=
  ((101%positive,0%Z),Tint32,Vint32 tick) ::
  ((102%positive,0%Z),Tint8,V293_byteval run) ::
  ((103%positive,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head LoopTasks LoopIdle)) ::
  V293_tick_pointer_cell 70%positive LoopIdle :: tl LoopCells.
Definition SuffixMemory tick run := OwnershipCellsMemory (SuffixCells tick run).
Definition SuffixState enabled M : RstateOP :=
  (SuffixGlobal,TickLocal,M,(fun _ => false),(enabled,[3%nat],[false]),emp,spec_done None).

Theorem SuffixEntrySatisfiable : forall tick run enabled, run<256 ->
  SuffixState enabled (SuffixMemory tick run) |=
    V293_tick_suffix_owned 101%positive tick 102%positive run 103%positive
      (V293_tick_head LoopTasks LoopIdle) 70%positive LoopIdle LoopTasks LoopIdle
      92%positive 93%positive 0 0 0 LoopFrame.
Proof.
  intros tick run enabled Range.
  assert (Apart : OwnershipCellsSeparated (SuffixCells tick run)).
  { vm_compute. repeat split; intros a Member Rest;
      repeat destruct Member as [Member|Member]; try contradiction; subst a; intuition discriminate. }
  assert (Valid : Forall (fun cell => let '(_,tp,v) := cell in
    rule_type_val_match tp v = true) (SuffixCells tick run)).
  { apply Forall_cons; [reflexivity| ]. apply Forall_cons; [apply V293_byte_type;exact Range| ].
    repeat constructor; reflexivity. }
  pose proof (OwnershipCellsSpatial _ Apart Valid SuffixGlobal TickLocal) as Entry.
  assert (Rebased : SuffixState enabled (SuffixMemory tick run) |=
    V293_owned_record_cells (SuffixCells tick run)).
  { unfold SuffixState,SuffixMemory. eapply TickCellsRebase. exact Entry. }
  unfold V293_tick_suffix_owned,V293_tick_loop_owned.
  change (SuffixState enabled (SuffixMemory tick run) |=
    V293_owned_record_cell ((101%positive,0%Z),Tint32,Vint32 tick) **
    (V293_owned_record_cell ((102%positive,0%Z),Tint8,V293_byteval run) **
      (V293_owned_record_cell ((103%positive,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head LoopTasks LoopIdle)) **
        (V293_owned_record_cell (V293_tick_pointer_cell 70%positive LoopIdle) **
          V293_owned_record_cells (V293_tick_chain_cells LoopTasks LoopIdle ++
            (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0 ++
              (V293_tick_idle_cell LoopIdle :: LoopFrameCells))))))) in Rebased.
  eapply astar_mono; [intros st H;exact H| |exact Rebased].
  eapply astar_mono; [intros st H;exact H| ].
  eapply astar_mono; [intros st H;exact H| ].
  eapply astar_mono; [intros st H;exact H| ].
  intros st H. apply V293_tick_cells_append in H. eapply astar_mono; [intros s A;exact A| |exact H].
  intros s A. apply V293_tick_cells_append in A. exact A.
Qed.

Definition SuffixExecution tick run enabled Mf :=
  V293_local_steps (fun _ => None)
    (curs (V293_tick_post_hook 901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z),(kenil,kstop))
    ((SuffixGlobal,TickLocal,SuffixMemory tick run),(fun _ => false),(enabled,[3%nat],[false]))
    (curs (sskip None),(kenil,kstop)) ((SuffixGlobal,TickLocal,Mf),(fun _ => false),(enabled,[3%nat],[false])).
Definition SuffixExpectedCells tick run : list V293_record_cell :=
  ((101%positive,0%Z),Tint32,Vint32 (Int.add tick Int.one)) ::
  ((102%positive,0%Z),Tint8,V293_byteval run) ::
  ((103%positive,0%Z),Tptr V293_tcb_type,Vptr (V293_tick_head LoopTasks LoopIdle)) ::
  V293_tick_pointer_cell 70%positive LoopIdle ::
  (V293_tick_chain_cells (if Nat.eqb run 1 then LoopFinalTasks else LoopTasks) LoopIdle ++
    (V293_tick_bitmap_cells 92%positive 93%positive (if Nat.eqb run 1 then 3 else 0)
      (if Nat.eqb run 1 then 4 else 0) (if Nat.eqb run 1 then 4 else 0) ++
      (V293_tick_idle_cell LoopIdle :: LoopFrameCells))).

Theorem SuffixMixedExecution : forall tick run enabled, run<256 -> exists Mf,
  SuffixExecution tick run enabled Mf /\
  (forall a tp v, In (a,tp,v) (SuffixExpectedCells tick run) -> load tp Mf a = Some v) /\
  SuffixState enabled Mf |= V293_tick_suffix_owned 101%positive (Int.add tick Int.one)
    102%positive run 103%positive (V293_tick_head LoopTasks LoopIdle) 70%positive LoopIdle
    (if Nat.eqb run 1 then LoopFinalTasks else LoopTasks) LoopIdle 92%positive 93%positive
    (if Nat.eqb run 1 then 3 else 0) (if Nat.eqb run 1 then 4 else 0)
    (if Nat.eqb run 1 then 4 else 0) LoopFrame.
Proof.
  intros tick run enabled Range.
  assert (TasksValid : Forall V293_tick_task_valid LoopTasks).
  { unfold LoopTasks.
    repeat (apply Forall_cons; [unfold V293_tick_task_valid; vm_compute; repeat split; try discriminate; lia | ]).
    apply Forall_nil. }
  pose proof (V293_tick_post_hook_owned_execution LoopTasks (fun _ => None) kstop SuffixGlobal
    TickLocal (SuffixMemory tick run) (fun _ => false) enabled [3%nat] [false] emp (spec_done None)
    901%Z 902%Z 903%Z 1001%Z 1002%Z 1003%Z 70%positive 101%positive 102%positive 103%positive
    LoopIdle LoopIdle 92%positive 93%positive tick run 0 0 0 LoopFrame
    ltac:(apply map_get_sig) ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(change (4+50<=4294967295)%Z;lia) TasksValid Range ltac:(lia) ltac:(lia) ltac:(lia)
    (SuffixEntrySatisfiable tick run enabled Range)) as Run.
  destruct Run as (Mf & Exec & Time & Pointer & Returned).
  assert (Expected : map V293_tick_task_after LoopTasks = LoopFinalTasks) by reflexivity.
  assert (Final : SuffixState enabled Mf |= V293_tick_suffix_owned 101%positive (Int.add tick Int.one)
    102%positive run 103%positive (V293_tick_head LoopTasks LoopIdle) 70%positive LoopIdle
    (if Nat.eqb run 1 then LoopFinalTasks else LoopTasks) LoopIdle 92%positive 93%positive
    (if Nat.eqb run 1 then 3 else 0) (if Nat.eqb run 1 then 4 else 0)
    (if Nat.eqb run 1 then 4 else 0) LoopFrame).
  { destruct (Nat.eqb run 1); cbn beta iota zeta in Returned |- *; rewrite ?Expected in Returned; exact Returned. }
  exists Mf. split; [exact Exec| ]. split; [ | exact Final].
  assert (All : SuffixState enabled Mf |= V293_owned_record_cells (SuffixExpectedCells tick run)).
  { unfold V293_tick_suffix_owned,V293_tick_loop_owned in Final.
    unfold SuffixExpectedCells. cbn [V293_owned_record_cells].
    eapply astar_mono; [intros s H;exact H| |exact Final].
    eapply astar_mono; [intros s H;exact H| ].
    eapply astar_mono; [intros s H;exact H| ].
    eapply astar_mono; [intros s H;exact H| ].
    intros s H. apply V293_tick_cells_append. eapply astar_mono; [intros st A;exact A| |exact H].
    intros st A. apply V293_tick_cells_append. exact A. }
  intros a tp v Member. change (load tp (getmem (SuffixState enabled Mf)) a = Some v).
  eapply V293_owned_record_cells_load; [exact Member|exact All].
Qed.

Lemma SuffixUint32Wrap : Int.add (Int.repr 4294967295) Int.one = Int.zero.
Proof.
  change (Int.repr 4294967296 = Int.repr 0).
  apply Int.eqm_samerepr. unfold Int.eqm,Int.eqmod. exists 1%Z. reflexivity.
Qed.

Theorem SuffixRunningOneWrapped : forall enabled, exists Mf,
  SuffixExecution (Int.repr 4294967295) 1 enabled Mf /\
  load Tint32 Mf (101%positive,0%Z) = Some (Vint32 Int.zero) /\
  load Tint32 Mf (82%positive,56%Z) = Some (Vint32 (Int.repr 2)) /\
  load Tint8 Mf (92%positive,0%Z) = Some (V293_byteval 3).
Proof.
  intro enabled. destruct (SuffixMixedExecution (Int.repr 4294967295) 1 enabled ltac:(lia))
    as (Mf & Exec & Fields & Returned).
  exists Mf. split; [exact Exec| ]. split.
  - rewrite <- SuffixUint32Wrap. apply Fields. unfold SuffixExpectedCells. left. reflexivity.
  - split; apply Fields; unfold SuffixExpectedCells; vm_compute; tauto.
Qed.

Theorem SuffixRunningTwoNotTrue : forall enabled, exists Mf,
  SuffixExecution Int.zero 2 enabled Mf /\
  load Tint32 Mf (101%positive,0%Z) = Some (Vint32 Int.one) /\
  load Tint32 Mf (82%positive,56%Z) = Some (Vint32 (Int.repr 3)) /\
  load Tint8 Mf (92%positive,0%Z) = Some (V293_byteval 0).
Proof.
  intro enabled. destruct (SuffixMixedExecution Int.zero 2 enabled ltac:(lia))
    as (Mf & Exec & Fields & Returned).
  exists Mf. split; [exact Exec| ]. repeat split; apply Fields;
    unfold SuffixExpectedCells; vm_compute; tauto.
Qed.

Theorem SuffixRunningZeroStillTicks : forall enabled, exists Mf,
  SuffixExecution (Int.repr 4294967295) 0 enabled Mf /\
  load Tint32 Mf (101%positive,0%Z) = Some (Vint32 Int.zero) /\
  load Tint32 Mf (82%positive,56%Z) = Some (Vint32 (Int.repr 3)) /\
  load Tint8 Mf (92%positive,0%Z) = Some (V293_byteval 0).
Proof.
  intro enabled. destruct (SuffixMixedExecution (Int.repr 4294967295) 0 enabled ltac:(lia))
    as (Mf & Exec & Fields & Returned).
  exists Mf. split; [exact Exec| ]. split.
  - rewrite <- SuffixUint32Wrap. apply Fields. unfold SuffixExpectedCells. left. reflexivity.
  - split; apply Fields; unfold SuffixExpectedCells; vm_compute; tauto.
Qed.

Print Assumptions SuffixEntrySatisfiable.
Print Assumptions SuffixMixedExecution.
Print Assumptions SuffixRunningOneWrapped.
Print Assumptions SuffixRunningTwoNotTrue.
Print Assumptions SuffixRunningZeroStillTicks.
