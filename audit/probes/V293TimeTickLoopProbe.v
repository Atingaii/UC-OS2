(* Independent encoded finite chain, with no idle Dly/Next bytes. This is
   a spatial witness, not a reachable initialized/global-invariant state. *)
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TimeTickTraversalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition LoopTasks : list V293_tick_task :=
  [Build_V293_tick_task 81%positive 8%Z 0%Z 0 7 0 0 0;
   Build_V293_tick_task 82%positive 12%Z 3%Z 0 7 0 1 1;
   Build_V293_tick_task 83%positive 8%Z 1%Z 1 7 0 2 2;
   Build_V293_tick_task 84%positive 12%Z 1%Z 9 7 1 1 9;
   Build_V293_tick_task 85%positive 8%Z 1%Z 0 7 1 2 10;
   Build_V293_tick_task 86%positive 12%Z 1%Z 8 7 1 3 11].
Definition LoopFinalTasks : list V293_tick_task :=
  [Build_V293_tick_task 81%positive 8%Z 0%Z 0 7 0 0 0;
   Build_V293_tick_task 82%positive 12%Z 2%Z 0 7 0 1 1;
   Build_V293_tick_task 83%positive 8%Z 0%Z 0 1 0 2 2;
   Build_V293_tick_task 84%positive 12%Z 0%Z 8 1 1 1 9;
   Build_V293_tick_task 85%positive 8%Z 0%Z 0 0 1 2 10;
   Build_V293_tick_task 86%positive 12%Z 0%Z 8 0 1 3 11].
Definition LoopIdle : addrval := (87%positive,Int.repr 4).
Definition LoopGlobal : env := set (sig 902%Z (93%positive,Tarray Tint8 2)) 903%Z (92%positive,Tint8).
Definition LoopFrameCells : list V293_record_cell :=
  [((90%positive,0%Z),Tint32,Vint32 (Int.repr 99));
   ((81%positive,40%Z),Tptr Tvoid,Vptr (94%positive,Int.repr 4))].
Definition LoopFrame := V293_owned_record_cells LoopFrameCells.
Definition LoopCells : list V293_record_cell :=
  V293_tick_pointer_cell 70%positive (V293_tick_head LoopTasks LoopIdle) ::
    (V293_tick_chain_cells LoopTasks LoopIdle ++
      (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0 ++
        (V293_tick_idle_cell LoopIdle :: LoopFrameCells))).
Definition LoopMemory := OwnershipCellsMemory LoopCells.
Definition LoopState enabled M : RstateOP :=
  (LoopGlobal,TickLocal,M,(fun _ => false),(enabled,(3%nat :: nil),(false :: nil)),emp,spec_done None).

Theorem LoopEntrySatisfiable : forall enabled,
  LoopState enabled LoopMemory |= V293_tick_loop_owned 70%positive
    (V293_tick_head LoopTasks LoopIdle) LoopTasks LoopIdle 92%positive 93%positive 0 0 0 LoopFrame.
Proof.
  intro enabled.
  assert (Apart : OwnershipCellsSeparated LoopCells).
  { vm_compute. repeat split; intros a Member Rest;
      repeat destruct Member as [Member|Member]; try contradiction; subst a; intuition discriminate. }
  assert (Valid : Forall (fun cell => let '(_,tp,v) := cell in
    rule_type_val_match tp v = true) LoopCells).
  { repeat constructor; reflexivity. }
  pose proof (OwnershipCellsSpatial _ Apart Valid LoopGlobal TickLocal) as Entry.
  assert (Rebased : LoopState enabled LoopMemory |= V293_owned_record_cells LoopCells).
  { unfold LoopState,LoopMemory. eapply TickCellsRebase. exact Entry. }
  unfold V293_tick_loop_owned. change (LoopState enabled LoopMemory |=
    V293_owned_record_cell (V293_tick_pointer_cell 70%positive (V293_tick_head LoopTasks LoopIdle)) **
    V293_owned_record_cells (V293_tick_chain_cells LoopTasks LoopIdle ++
      (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0 ++
        (V293_tick_idle_cell LoopIdle :: LoopFrameCells)))) in Rebased.
  eapply astar_mono; [ | | exact Rebased].
  - intros st H; exact H.
  - intros st H. apply V293_tick_cells_append in H. eapply astar_mono; [ | | exact H].
    + intros st0 H0; exact H0.
    + intros st0 H0. apply V293_tick_cells_append in H0. exact H0.
Qed.

Lemma LoopLoadBytesMissing : forall M b off n,
  get M (b,off) = None -> loadbytes M (b,off) (S n) = None.
Proof.
  intros M b off n Missing.
  change (match get M (b,off), loadbytes M (b,(off+1)%Z) n with
    | Some (_,u), Some bs => Some (u::bs) | _,_ => None end = None).
  rewrite Missing. reflexivity.
Qed.

Theorem LoopIdleHasNoIterationFields :
  load Tint32 LoopMemory (87%positive,48%Z) = None /\
  load (Tcom_ptr 410%Z) LoopMemory (87%positive,24%Z) = None.
Proof.
  assert (MissingDly : get LoopMemory (87%positive,48%Z) = None).
  { unfold LoopMemory. apply OwnershipCellsOutside. vm_compute. intro Member; intuition discriminate. }
  assert (MissingNext : get LoopMemory (87%positive,24%Z) = None).
  { unfold LoopMemory. apply OwnershipCellsOutside. vm_compute. intro Member; intuition discriminate. }
  split.
  - change (match loadbytes LoopMemory (87%positive,48%Z) 4 with
      | Some bs => Some (decode_val Tint32 bs) | None => None end = None).
    exact (f_equal (fun bytes => match bytes with
      | Some bs => Some (decode_val Tint32 bs) | None => None end)
      (LoopLoadBytesMissing LoopMemory 87%positive 48%Z 3 MissingDly)).
  - change (match loadbytes LoopMemory (87%positive,24%Z) 4 with
      | Some bs => Some (decode_val (Tcom_ptr 410%Z) bs) | None => None end = None).
    exact (f_equal (fun bytes => match bytes with
      | Some bs => Some (decode_val (Tcom_ptr 410%Z) bs) | None => None end)
      (LoopLoadBytesMissing LoopMemory 87%positive 24%Z 3 MissingNext)).
Qed.

Definition LoopExecution P ks enabled Mf :=
  V293_local_steps P
    (curs (swhile (V293_tick_guard 901%Z) (V293_tick_iteration 901%Z 902%Z 903%Z)),(kenil,ks))
    ((LoopGlobal,TickLocal,LoopMemory),(fun _ => false),(enabled,(3%nat :: nil),(false :: nil)))
    (curs (sskip None),(kenil,ks))
    ((LoopGlobal,TickLocal,Mf),(fun _ => false),(enabled,(3%nat :: nil),(false :: nil))).
Definition LoopExpectedCells := V293_tick_pointer_cell 70%positive LoopIdle ::
  (V293_tick_chain_cells LoopFinalTasks LoopIdle ++
    (V293_tick_bitmap_cells 92%positive 93%positive 3 4 4 ++ [V293_tick_idle_cell LoopIdle])).

Theorem LoopMixedExecution : forall P ks enabled, exists Mf,
  LoopExecution P ks enabled Mf /\
  load (Tptr V293_tcb_type) Mf (70%positive,0%Z) = Some (Vptr LoopIdle) /\
  (forall a tp v, In (a,tp,v) LoopExpectedCells -> load tp Mf a = Some v) /\
  (forall a tp v, In (a,tp,v) LoopFrameCells -> load tp Mf a = Some v) /\
  LoopState enabled Mf |= V293_tick_loop_owned 70%positive LoopIdle LoopFinalTasks LoopIdle
    92%positive 93%positive 3 4 4 LoopFrame.
Proof.
  intros P ks enabled.
  assert (TasksValid : Forall V293_tick_task_valid LoopTasks).
  { unfold LoopTasks.
    repeat (apply Forall_cons; [unfold V293_tick_task_valid; vm_compute; repeat split; try discriminate; lia | ]).
    apply Forall_nil. }
  pose proof (V293_tick_while_owned_execution LoopTasks P ks LoopGlobal TickLocal LoopMemory
    (fun _ => false) enabled (3%nat :: nil) (false :: nil) emp (spec_done None)
    901%Z 902%Z 903%Z 70%positive LoopIdle 92%positive 93%positive 0 0 0 LoopFrame
    ltac:(apply map_get_sig) ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(change (4+50<=4294967295)%Z;lia) TasksValid ltac:(lia) ltac:(lia) ltac:(lia)
    (LoopEntrySatisfiable enabled)) as Run.
  destruct Run as (Mf & Exec & Pointer & Returned).
  assert (Expected : map V293_tick_task_after LoopTasks = LoopFinalTasks) by reflexivity.
  change (LoopState enabled Mf |= V293_tick_loop_owned 70%positive LoopIdle
    (map V293_tick_task_after LoopTasks) LoopIdle 92%positive 93%positive 3 4 4 LoopFrame) in Returned.
  rewrite Expected in Returned.
  exists Mf. split; [exact Exec | ]. split; [exact Pointer | ]. split.
  - intros a tp v Member. change (load tp (getmem (LoopState enabled Mf)) a = Some v).
    eapply V293_tick_loop_fields_load; [exact Member | exact Returned].
  - split; [ | exact Returned]. intros a tp v Member.
    change (load tp (getmem (LoopState enabled Mf)) a = Some v).
    unfold V293_tick_loop_owned in Returned.
    eapply V293_record_star_load_r; [ | exact Returned]. eapply V293_record_star_load_r.
    eapply V293_record_star_load_r. eapply V293_record_star_load_r.
    unfold LoopFrame. apply V293_owned_record_cells_load. exact Member.
Qed.

Print Assumptions LoopEntrySatisfiable.
Print Assumptions LoopIdleHasNoIterationFields.
Print Assumptions LoopMixedExecution.
