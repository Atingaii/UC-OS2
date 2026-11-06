(* Nonempty literal resources built BEFORE execution.  One waiting task,
   no idle task: this witnesses the bridge, not initialized kernel reachability. *)
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TimeTickTraversalProbe.
Require Import CertiOS.audit.probes.V293TimeTickExpiryProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition BridgeTask : tid := (81%positive,Int.repr 8).
Definition BridgeReason := os_stat_sem (84%positive,Int.repr 4).
Definition BridgeTasks d : TcbMod.map :=
  sig BridgeTask (Int.repr 10,wait BridgeReason (Int.repr d),Vnull).
Definition BridgeEntries := repeat Vnull 10 ++ [Vptr BridgeTask;Vnull;Vnull].
Definition BridgeNode d := V293_tick_wait_node 81%positive 8%Z d BridgeReason 7 10.
Definition BridgeAbs d := V293_shared_fixture_abs BridgeTask (BridgeTasks d)
  (emp : EcbMod.map) (Int.repr 37).
Definition BridgeGlobal : env := set (sig 902%Z (93%positive,Tarray Tint8 2)) 903%Z (92%positive,Tint8).
Definition BridgeFrameCells : list V293_record_cell :=
  [((90%positive,0%Z),Tint32,Vint32 (Int.repr 99))].
Definition BridgeCells d :=
  [V293_tick_pointer_cell 70%positive BridgeTask] ++
  (V293_tick_task_cells (BridgeNode d) TickNext ++
  (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0 ++
  (V293_tick_record_extra 81%positive 8%Z 10 BridgeReason Vnull ++ BridgeFrameCells))).
Definition BridgeMemory d := OwnershipCellsMemory (BridgeCells d).
Definition BridgeState d M := V293_target_wstate BridgeGlobal TickLocal M (BridgeAbs d).
Definition BridgeNewTasks d := set (BridgeTasks d) BridgeTask
  (Int.repr 10,V293_tick_wait_status BridgeReason d,Vnull).

Lemma BridgeTable : forall d, V293_priority_table BridgeEntries (BridgeTasks d).
Proof.
  intro d. split; [reflexivity | ]. intros t p st msg Lookup.
  unfold BridgeTasks in Lookup. destruct (TcbMod.eq_dec BridgeTask t) as [Same|Apart].
  - subst t. rewrite map_get_sig in Lookup. inversion Lookup; subst p st msg.
    exists 10. repeat split; reflexivity || lia.
  - rewrite map_get_sig' in Lookup by exact Apart. discriminate.
Qed.

Lemma BridgeBitmap : forall d, V293_bitmap_tasks 0 0 (BridgeTasks d).
Proof.
  intros d p P. split.
  - intros [[_ Bit]|[_ [_ Bit]]]; rewrite Nat.testbit_0_l in Bit; discriminate.
  - intros [t [msg Lookup]]. unfold BridgeTasks in Lookup.
    destruct (TcbMod.eq_dec BridgeTask t) as [Same|Apart].
    + subst t. rewrite map_get_sig in Lookup. discriminate.
    + rewrite map_get_sig' in Lookup by exact Apart. discriminate.
Qed.

Theorem BridgeEntry : forall d, BridgeState d (BridgeMemory d) |=
  V293_owned_record_cell (V293_tick_pointer_cell 70%positive BridgeTask) **
  (V293_owned_record_cells (V293_tick_task_cells (BridgeNode d) TickNext) **
  (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0) **
  (V293_owned_record_cells (V293_tick_record_extra 81%positive 8%Z 10 BridgeReason Vnull) **
  (V293_owned_task_records (del (BridgeTasks d) BridgeTask) **
  (V293_shared_fields BridgeTask (BridgeTasks d) (emp : EcbMod.map) (Int.repr 37) **
    V293_owned_record_cells BridgeFrameCells))))).
Proof.
  intro d.
  assert (Apart:OwnershipCellsSeparated (BridgeCells d)).
  { vm_compute. repeat split; intros; intuition congruence. }
  assert (Valid:Forall (fun cell => let '(_,tp,v) := cell in rule_type_val_match tp v=true) (BridgeCells d)).
  { repeat constructor; reflexivity. }
  pose proof (OwnershipCellsSpatial _ Apart Valid BridgeGlobal TickLocal) as Cells.
  assert (Physical : V293_target_wstate BridgeGlobal TickLocal (BridgeMemory d) emp |=
    V293_owned_record_cell (V293_tick_pointer_cell 70%positive BridgeTask) **
    (V293_owned_record_cells (V293_tick_task_cells (BridgeNode d) TickNext) **
    (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0) **
    (V293_owned_record_cells (V293_tick_record_extra 81%positive 8%Z 10 BridgeReason Vnull) **
      V293_owned_record_cells BridgeFrameCells)))).
  { change (V293_target_wstate BridgeGlobal TickLocal (BridgeMemory d) emp |=
      V293_owned_record_cell (V293_tick_pointer_cell 70%positive BridgeTask) **
      V293_owned_record_cells (V293_tick_task_cells (BridgeNode d) TickNext ++
      (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0 ++
      (V293_tick_record_extra 81%positive 8%Z 10 BridgeReason Vnull ++ BridgeFrameCells)))) in Cells.
    eapply astar_mono; [intros s H;exact H | | exact Cells].
    intros s H. apply OwnershipCellsAppend in H.
    eapply astar_mono; [intros st H';exact H' | | exact H].
    intros st H'. apply OwnershipCellsAppend in H'.
    eapply astar_mono; [intros st' H'';exact H'' | | exact H'].
    intros st' H''. apply OwnershipCellsAppend in H''. exact H''. }
  assert (Joint : BridgeState d (BridgeMemory d) |=
    (V293_owned_record_cell (V293_tick_pointer_cell 70%positive BridgeTask) **
    (V293_owned_record_cells (V293_tick_task_cells (BridgeNode d) TickNext) **
    (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0) **
    (V293_owned_record_cells (V293_tick_record_extra 81%positive 8%Z 10 BridgeReason Vnull) **
      V293_owned_record_cells BridgeFrameCells)))) **
    V293_shared_fields BridgeTask (BridgeTasks d) (emp : EcbMod.map) (Int.repr 37)).
  { eapply V293_target_wstate_star with (m1:=BridgeMemory d) (m2:=emp)
      (o1:=emp) (o2:=BridgeAbs d).
    - apply map_join_emp.
    - apply map_join_comm; apply map_join_emp.
    - exact Physical.
    - exact (V293_shared_fixture_fields BridgeTask (BridgeTasks d) (emp : EcbMod.map) (Int.repr 37)). }
  assert (Deleted:del (BridgeTasks d) BridgeTask=(emp : TcbMod.map)).
  { apply TcbMod.extensionality. intro t.
    change (get (del (BridgeTasks d) BridgeTask) t = get (emp : TcbMod.map) t).
    rewrite map_del_sem,map_emp_get.
    match goal with |- context [if ?decision then _ else _] => destruct decision as [Same|Other] end; [reflexivity | ].
    unfold BridgeTasks. apply map_get_sig'; exact Other. }
  rewrite Deleted. change (BridgeState d (BridgeMemory d) |=
    V293_owned_record_cell (V293_tick_pointer_cell 70%positive BridgeTask) **
    (V293_owned_record_cells (V293_tick_task_cells (BridgeNode d) TickNext) **
    (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0) **
    (V293_owned_record_cells (V293_tick_record_extra 81%positive 8%Z 10 BridgeReason Vnull) **
    (Aemp ** (V293_shared_fields BridgeTask (BridgeTasks d) (emp : EcbMod.map) (Int.repr 37) **
      V293_owned_record_cells BridgeFrameCells)))))).
  clear -Joint. sep auto.
Qed.

Definition BridgeExecution P ks d Mf :=
  V293_local_steps P (curs (V293_tick_iteration 901%Z 902%Z 903%Z),(kenil,ks))
    ((BridgeGlobal,TickLocal,BridgeMemory d),(fun _ => false),(false,nil,nil))
    (curs (sskip None),(kenil,ks)) ((BridgeGlobal,TickLocal,Mf),(fun _ => false),(false,nil,nil)).

Theorem BridgeLiteral : forall P ks sd d,
  (0<=d<=Int.max_unsigned)%Z -> exists Mf,
  BridgeExecution P ks d Mf /\
  spec_step sd (spec_prim nil (V293_tick_wait_step BridgeTask)) (BridgeAbs d) (END None)
    (set (BridgeAbs d) abstcblsid (abstcblist (BridgeNewTasks d))) /\
  V293_task_records Mf (BridgeNewTasks d) /\
  V293_priority_table BridgeEntries (BridgeNewTasks d) /\
  V293_bitmap_tasks (fst (V293_tick_wait_rows 0 0 d 10))
    (snd (V293_tick_wait_rows 0 0 d 10)) (BridgeNewTasks d) /\
  load Tint8 Mf (92%positive,0%Z)=Some (V293_byteval
    (V293_ready_group (fst (V293_tick_wait_rows 0 0 d 10)) (snd (V293_tick_wait_rows 0 0 d 10)))) /\
  load Tint8 Mf (93%positive,1%Z)=Some (V293_byteval (snd (V293_tick_wait_rows 0 0 d 10))) /\
  load Tint32 Mf (90%positive,0%Z)=Some (Vint32 (Int.repr 99)).
Proof.
  intros P ks sd d D.
  destruct (V293_tick_wait_iteration_refines P ks BridgeGlobal TickLocal (BridgeMemory d)
    (fun _ => false) false nil nil (BridgeAbs d) (spec_done None) sd 901%Z 902%Z 903%Z
    70%positive 81%positive 8%Z TickNext d BridgeReason 7 10 92%positive 93%positive 0 0
    Vnull BridgeTask (BridgeTasks d) (emp : EcbMod.map) (Int.repr 37) BridgeEntries
    (V293_owned_record_cells BridgeFrameCells)
    ltac:(apply map_get_sig) ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(change (0<=8 /\ 8+54<=4294967295)%Z;lia) D
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (BridgeTable d) (BridgeBitmap d) ltac:(apply map_get_sig) (BridgeEntry d))
    as (Mf & Step & Exec & Records & Table & Bitmap & Returned).
  exists Mf. split; [exact Exec | ]. split; [exact Step | ]. split; [exact Records | ].
  split; [exact Table | ]. split; [exact Bitmap | ].
  assert (Bits : V293_target_wstate BridgeGlobal TickLocal Mf
      (set (BridgeAbs d) abstcblsid (abstcblist (BridgeNewTasks d))) |=
    V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive
      (V293_ready_group (fst (V293_tick_wait_rows 0 0 d 10)) (snd (V293_tick_wait_rows 0 0 d 10)))
      (fst (V293_tick_wait_rows 0 0 d 10)) (snd (V293_tick_wait_rows 0 0 d 10))) ** Atrue)
    by (clear -Returned;sep auto).
  split.
  - change (load Tint8 (getmem (V293_target_wstate BridgeGlobal TickLocal Mf
      (set (BridgeAbs d) abstcblsid (abstcblist (BridgeNewTasks d))))) (92%positive,0%Z)=
      Some (V293_byteval (V293_ready_group (fst (V293_tick_wait_rows 0 0 d 10)) (snd (V293_tick_wait_rows 0 0 d 10))))).
    eapply V293_record_star_load_l; [ | exact Bits].
    apply V293_owned_record_cells_load. left; reflexivity.
  - split.
    + change (load Tint8 (getmem (V293_target_wstate BridgeGlobal TickLocal Mf
        (set (BridgeAbs d) abstcblsid (abstcblist (BridgeNewTasks d))))) (93%positive,1%Z)=
        Some (V293_byteval (snd (V293_tick_wait_rows 0 0 d 10)))).
      eapply V293_record_star_load_l; [ | exact Bits].
      apply V293_owned_record_cells_load. right;right;left;reflexivity.
    + assert (Frame : V293_target_wstate BridgeGlobal TickLocal Mf
          (set (BridgeAbs d) abstcblsid (abstcblist (BridgeNewTasks d))) |=
          V293_owned_record_cells BridgeFrameCells ** Atrue) by (clear -Returned;sep auto).
      change (load Tint32 (getmem (V293_target_wstate BridgeGlobal TickLocal Mf
        (set (BridgeAbs d) abstcblsid (abstcblist (BridgeNewTasks d))))) (90%positive,0%Z)=Some (Vint32 (Int.repr 99))).
      eapply V293_record_star_load_l; [ | exact Frame].
      apply V293_owned_record_cells_load. left; reflexivity.
Qed.

(* Both delay relations below inspect the SAME actual execution result. *)
Theorem BridgeCountdownControl : forall P ks, exists Mf,
  BridgeExecution P ks 3%Z Mf /\
  V293_task_records Mf (BridgeNewTasks 3%Z) /\
  ~ V293_task_records Mf (BridgeTasks 3%Z).
Proof.
  intros P ks. destruct (BridgeLiteral P ks V293_scheduler 3%Z ltac:(change (0<=3<=4294967295)%Z;lia))
    as (Mf & Exec & Step & Records & Rest).
  exists Mf. split; [exact Exec | ]. split; [exact Records | ]. intro Old.
  pose proof (Records BridgeTask (Int.repr 10) (wait BridgeReason (Int.repr 2)) Vnull
    ltac:(apply map_get_set)) as NewRecord.
  pose proof (Old BridgeTask (Int.repr 10) (wait BridgeReason (Int.repr 3)) Vnull
    ltac:(apply map_get_sig)) as OldRecord.
  destruct NewRecord as (p & Range & Priority & Fields & pend & Payload & Event).
  destruct OldRecord as (p' & Range' & Priority' & Fields' & pend' & Payload' & Event').
  unfold V293_wait_payload in Payload,Payload'.
  destruct Payload as (Stat & Delay & Tail). destruct Payload' as (Stat' & Delay' & Tail').
  change (load Tint32 Mf (81%positive,52%Z)=Some (Vint32 (Int.repr 2))) in Delay.
  change (load Tint32 Mf (81%positive,52%Z)=Some (Vint32 (Int.repr 3))) in Delay'.
  rewrite Delay in Delay'. discriminate.
Qed.

(* Change only ONE side of the bitmap/task relation at a time. *)
Theorem BridgeExpiryControls : forall P ks, exists Mf,
  BridgeExecution P ks 1%Z Mf /\
  V293_task_records Mf (BridgeNewTasks 1%Z) /\
  V293_bitmap_tasks 0 4 (BridgeNewTasks 1%Z) /\
  load Tint8 Mf (92%positive,0%Z)=Some (V293_byteval 2) /\
  load Tint8 Mf (93%positive,1%Z)=Some (V293_byteval 4) /\
  ~ V293_bitmap_tasks 0 0 (BridgeNewTasks 1%Z) /\
  ~ V293_bitmap_tasks 0 4 (BridgeTasks 1%Z).
Proof.
  intros P ks. destruct (BridgeLiteral P ks V293_scheduler 1%Z ltac:(change (0<=1<=4294967295)%Z;lia))
    as (Mf & Exec & Step & Records & Table & Bitmap & Group & Row & Canary).
  exists Mf. split; [exact Exec | ]. split; [exact Records | ]. split; [exact Bitmap | ]. split; [exact Group | ]. split; [exact Row | ]. split.
  - intro MissingBit. assert (Ready:V293_bitmap_ready 0 0 10).
    { apply (proj2 (MissingBit 10 ltac:(lia))). exists BridgeTask. exists Vnull. apply map_get_set. }
    destruct Ready as [[_ Bad]|[_ [_ Bad]]]; discriminate.
  - intro MissingTask. assert (Ready:V293_bitmap_ready 0 4 10) by (right;repeat split;reflexivity || lia).
    pose proof (proj1 (MissingTask 10 ltac:(lia)) Ready) as Ghost.
    apply (proj2 (BridgeBitmap 1%Z 10 ltac:(lia))) in Ghost.
    destruct Ghost as [[_ Bad]|[_ [_ Bad]]]; discriminate.
Qed.

(* Actual original raw execution remains suspended after a pending timeout.
   It is deliberately NOT fed to the unsuspended abstract bridge. *)
Theorem BridgeSuspensionBoundary : forall P ks, exists Mf,
  ExpiryExecution P ks false 9 Mf /\
  load Tint8 Mf (81%positive,56%Z)=Some (V293_byteval 8) /\
  load Tint8 Mf (81%positive,57%Z)=Some (V293_byteval 1) /\
  load Tint8 Mf (92%positive,0%Z)=Some (V293_byteval 1) /\
  load Tint8 Mf (93%positive,1%Z)=Some (V293_byteval 128) /\
  (forall reason, V293_tick_reason_stat reason<>9).
Proof.
  intros P ks. destruct (ExpiryLiteralExecution P ks false 9 ltac:(lia))
    as (Mf & Exec & Delay & Stat & Pend & Group & Row & Tail).
  exists Mf. split; [exact Exec | ]. split; [exact Stat | ]. split; [exact Pend | ].
  split; [exact Group | ]. split; [exact Row | ]. intros reason;destruct reason;discriminate.
Qed.

Theorem BridgeOtherSlots : forall d id,
  id<>abstcblsid -> get (set (BridgeAbs d) abstcblsid (abstcblist (BridgeNewTasks d))) id =
    get (BridgeAbs d) id.
Proof. intros;apply map_get_set';congruence. Qed.
