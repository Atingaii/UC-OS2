(* Two disjoint records in ONE physical block. This is a resource/iteration
   fixture, not a reachable initialized kernel or a second iteration. *)
Require Import CertiOS.audit.probes.V293TimeTickTaskBridgeProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickRecordReassembly.
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
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.


Definition ReassemblyOther : tid := (81%positive,Int.repr 128).
Definition ReassemblyOtherValue : abstcb.B := (Int.repr 4,wait os_stat_time (Int.repr 5),Vnull).
Definition ReassemblyTasks d := set (BridgeTasks d) ReassemblyOther ReassemblyOtherValue.
Definition ReassemblyEntries := repeat Vnull 4 ++ [Vptr ReassemblyOther] ++
  repeat Vnull 5 ++ [Vptr BridgeTask;Vnull;Vnull].
Definition ReassemblyOtherCells :=
  V293_record_layout ReassemblyOther 4 (wait os_stat_time (Int.repr 5)) Vnull 0.
Definition ReassemblyCells d :=
  [V293_tick_pointer_cell 70%positive BridgeTask] ++
  (V293_tick_task_cells (BridgeNode d) ReassemblyOther ++
  (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0 ++
  (V293_tick_record_extra 81%positive 8%Z 10 BridgeReason Vnull ++
  (ReassemblyOtherCells ++ BridgeFrameCells)))).
Definition ReassemblyMemory d := OwnershipCellsMemory (ReassemblyCells d).
Definition ReassemblyAbs d := V293_shared_fixture_abs BridgeTask (ReassemblyTasks d)
  (emp : EcbMod.map) (Int.repr 37).
Definition ReassemblyNewTasks d := set (ReassemblyTasks d) BridgeTask
  (Int.repr 10,V293_tick_wait_status BridgeReason d,Vnull).

Lemma ReassemblyDeleted : forall d,
  del (ReassemblyTasks d) BridgeTask = sig ReassemblyOther ReassemblyOtherValue.
Proof.
  intro d. apply TcbMod.extensionality. intro t.
  change (get (del (ReassemblyTasks d) BridgeTask) t =
    get (sig ReassemblyOther ReassemblyOtherValue) t).
  rewrite map_del_sem.
  match goal with |- context [if ?decision then _ else _] => destruct decision as [Same|Apart] end.
  - subst t. rewrite map_get_sig' by (vm_compute; congruence). reflexivity.
  - unfold ReassemblyTasks. destruct (TcbMod.eq_dec t ReassemblyOther) as [Other|Away].
    + subst t. rewrite map_get_set,map_get_sig. reflexivity.
    + rewrite map_get_set' by congruence. unfold BridgeTasks.
      rewrite !map_get_sig' by congruence. reflexivity.
Qed.

Lemma ReassemblyRelations : forall d,
  V293_priority_table ReassemblyEntries (ReassemblyTasks d) /\
  V293_bitmap_tasks 0 0 (ReassemblyTasks d).
Proof.
  intro d. split.
  - split; [reflexivity | ]. intros t p st msg Lookup.
    unfold ReassemblyTasks in Lookup.
    destruct (TcbMod.eq_dec t ReassemblyOther) as [Same|Apart].
    + subst t. rewrite map_get_set in Lookup. inversion Lookup; subst p st msg.
      exists 4. repeat split; reflexivity || lia.
    + rewrite map_get_set' in Lookup by congruence.
      unfold BridgeTasks in Lookup.
      destruct (TcbMod.eq_dec BridgeTask t) as [Same|Away].
      * subst t. rewrite map_get_sig in Lookup. inversion Lookup; subst p st msg.
        exists 10. repeat split; reflexivity || lia.
      * rewrite map_get_sig' in Lookup by exact Away. discriminate.
  - intros p P. split.
    + intros [[_ Bit]|[_ [_ Bit]]]; rewrite Nat.testbit_0_l in Bit; discriminate.
    + intros [t [msg Lookup]]. unfold ReassemblyTasks in Lookup.
      destruct (TcbMod.eq_dec t ReassemblyOther) as [Same|Apart].
      * subst t. rewrite map_get_set in Lookup. discriminate.
      * rewrite map_get_set' in Lookup by congruence.
        apply (proj2 (BridgeBitmap d p P)). exists t. exists msg. exact Lookup.
Qed.

Theorem ReassemblyEntry : forall d,
  V293_target_wstate BridgeGlobal TickLocal (ReassemblyMemory d) (ReassemblyAbs d) |=
    V293_owned_record_cell (V293_tick_pointer_cell 70%positive BridgeTask) **
    (V293_owned_record_cells (V293_tick_task_cells (BridgeNode d) ReassemblyOther) **
    (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0) **
    (V293_owned_record_cells (V293_tick_record_extra 81%positive 8%Z 10 BridgeReason Vnull) **
    (V293_owned_task_records (del (ReassemblyTasks d) BridgeTask) **
    (V293_shared_fields BridgeTask (ReassemblyTasks d) (emp : EcbMod.map) (Int.repr 37) **
      V293_owned_record_cells BridgeFrameCells))))).
Proof.
  intro d.
  assert (Apart:OwnershipCellsSeparated (ReassemblyCells d)).
  { vm_compute. repeat split; intros; intuition congruence. }
  assert (Valid:Forall (fun cell => let '(_,tp,v) := cell in rule_type_val_match tp v=true) (ReassemblyCells d)).
  { repeat constructor; reflexivity. }
  pose proof (OwnershipCellsSpatial _ Apart Valid BridgeGlobal TickLocal) as Cells.
  assert (Physical : V293_target_wstate BridgeGlobal TickLocal (ReassemblyMemory d) emp |=
    V293_owned_record_cell (V293_tick_pointer_cell 70%positive BridgeTask) **
    (V293_owned_record_cells (V293_tick_task_cells (BridgeNode d) ReassemblyOther) **
    (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0) **
    (V293_owned_record_cells (V293_tick_record_extra 81%positive 8%Z 10 BridgeReason Vnull) **
    (V293_owned_record_cells ReassemblyOtherCells ** V293_owned_record_cells BridgeFrameCells))))).
  { change (V293_target_wstate BridgeGlobal TickLocal (ReassemblyMemory d) emp |=
      V293_owned_record_cell (V293_tick_pointer_cell 70%positive BridgeTask) **
      V293_owned_record_cells (V293_tick_task_cells (BridgeNode d) ReassemblyOther ++
      (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0 ++
      (V293_tick_record_extra 81%positive 8%Z 10 BridgeReason Vnull ++
      (ReassemblyOtherCells ++ BridgeFrameCells))))) in Cells.
    eapply astar_mono; [intros s H; exact H | | exact Cells].
    intros s H. apply OwnershipCellsAppend in H.
    eapply astar_mono; [intros s' H'; exact H' | | exact H].
    intros s' H'. apply OwnershipCellsAppend in H'.
    eapply astar_mono; [intros s'' H''; exact H'' | | exact H'].
    intros s'' H''. apply OwnershipCellsAppend in H''.
    eapply astar_mono; [intros s0 H0; exact H0 | | exact H''].
    intros s0 H0. apply OwnershipCellsAppend in H0. exact H0. }
  assert (Joint : V293_target_wstate BridgeGlobal TickLocal (ReassemblyMemory d) (ReassemblyAbs d) |=
    (V293_owned_record_cell (V293_tick_pointer_cell 70%positive BridgeTask) **
    (V293_owned_record_cells (V293_tick_task_cells (BridgeNode d) ReassemblyOther) **
    (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0) **
    (V293_owned_record_cells (V293_tick_record_extra 81%positive 8%Z 10 BridgeReason Vnull) **
    (V293_owned_task_records (del (ReassemblyTasks d) BridgeTask) **
      V293_owned_record_cells BridgeFrameCells))))) **
    V293_shared_fields BridgeTask (ReassemblyTasks d) (emp : EcbMod.map) (Int.repr 37)).
  { eapply V293_target_wstate_star with (m1:=ReassemblyMemory d) (m2:=emp)
      (o1:=emp) (o2:=ReassemblyAbs d).
    - apply map_join_emp.
    - apply map_join_comm; apply map_join_emp.
    - rewrite ReassemblyDeleted.
      change (V293_target_wstate BridgeGlobal TickLocal (ReassemblyMemory d) emp |=
        V293_owned_record_cell (V293_tick_pointer_cell 70%positive BridgeTask) **
        (V293_owned_record_cells (V293_tick_task_cells (BridgeNode d) ReassemblyOther) **
        (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0) **
        (V293_owned_record_cells (V293_tick_record_extra 81%positive 8%Z 10 BridgeReason Vnull) **
        ((V293_owned_task_record ReassemblyOther (Int.repr 4) (wait os_stat_time (Int.repr 5)) Vnull ** Aemp) **
          V293_owned_record_cells BridgeFrameCells))))).
      assert (Reordered : V293_target_wstate BridgeGlobal TickLocal (ReassemblyMemory d) emp |=
        V293_owned_record_cells ReassemblyOtherCells **
        (V293_owned_record_cell (V293_tick_pointer_cell 70%positive BridgeTask) **
        (V293_owned_record_cells (V293_tick_task_cells (BridgeNode d) ReassemblyOther) **
        (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0) **
        (V293_owned_record_cells (V293_tick_record_extra 81%positive 8%Z 10 BridgeReason Vnull) **
          V293_owned_record_cells BridgeFrameCells))))) by (clear -Physical; sep auto).
      assert (WithRecord : V293_target_wstate BridgeGlobal TickLocal (ReassemblyMemory d) emp |=
        V293_owned_task_record ReassemblyOther (Int.repr 4) (wait os_stat_time (Int.repr 5)) Vnull **
        (V293_owned_record_cell (V293_tick_pointer_cell 70%positive BridgeTask) **
        (V293_owned_record_cells (V293_tick_task_cells (BridgeNode d) ReassemblyOther) **
        (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 0 0 0) **
        (V293_owned_record_cells (V293_tick_record_extra 81%positive 8%Z 10 BridgeReason Vnull) **
          V293_owned_record_cells BridgeFrameCells))))).
      { eapply astar_mono; [ | | exact Reordered]; [ | intros;assumption].
        intros s H. unfold V293_owned_task_record. exists 4. exists 0.
        apply astar_l_apure_intro; [exact H | repeat split; reflexivity || lia]. }
      clear -WithRecord. sep auto.
    - exact (V293_shared_fixture_fields BridgeTask (ReassemblyTasks d) (emp : EcbMod.map) (Int.repr 37)). }
  clear -Joint. sep auto.
Qed.

Definition ReassemblyExecution P ks d Mf :=
  V293_local_steps P (curs (V293_tick_iteration 901%Z 902%Z 903%Z),(kenil,ks))
    ((BridgeGlobal,TickLocal,ReassemblyMemory d),(fun _ => false),(false,nil,nil))
    (curs (sskip None),(kenil,ks)) ((BridgeGlobal,TickLocal,Mf),(fun _ => false),(false,nil,nil)).
Definition ReassemblyResult d Mf :=
  V293_target_wstate BridgeGlobal TickLocal Mf
    (set (ReassemblyAbs d) abstcblsid (abstcblist (ReassemblyNewTasks d))) |=
  V293_owned_task_records (ReassemblyNewTasks d) **
    ((V293_owned_record_cell (V293_tick_pointer_cell 70%positive ReassemblyOther) **
    (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive
      (V293_ready_group (fst (V293_tick_wait_rows 0 0 d 10)) (snd (V293_tick_wait_rows 0 0 d 10)))
      (fst (V293_tick_wait_rows 0 0 d 10)) (snd (V293_tick_wait_rows 0 0 d 10))) **
    (V293_shared_fields BridgeTask (ReassemblyNewTasks d) (emp : EcbMod.map) (Int.repr 37) **
      V293_owned_record_cells BridgeFrameCells))) ** Atrue).

Theorem ReassemblyLiteral : forall P ks sd d,
  (0<=d<=Int.max_unsigned)%Z -> exists Mf,
  ReassemblyExecution P ks d Mf /\
  spec_step sd (spec_prim nil (V293_tick_wait_step BridgeTask)) (ReassemblyAbs d) (END None)
    (set (ReassemblyAbs d) abstcblsid (abstcblist (ReassemblyNewTasks d))) /\
  V293_task_records Mf (ReassemblyNewTasks d) /\
  V293_priority_table ReassemblyEntries (ReassemblyNewTasks d) /\
  V293_bitmap_tasks (fst (V293_tick_wait_rows 0 0 d 10))
    (snd (V293_tick_wait_rows 0 0 d 10)) (ReassemblyNewTasks d) /\
  ReassemblyResult d Mf.
Proof.
  intros P ks sd d D.
  destruct (ReassemblyRelations d) as [Table Bitmap].
  destruct (V293_tick_wait_iteration_owned_records P ks BridgeGlobal TickLocal (ReassemblyMemory d)
    (fun _ => false) false nil nil (ReassemblyAbs d) (spec_done None) sd 901%Z 902%Z 903%Z
    70%positive 81%positive 8%Z ReassemblyOther d BridgeReason 7 10 92%positive 93%positive 0 0
    Vnull BridgeTask (ReassemblyTasks d) (emp : EcbMod.map) (Int.repr 37) ReassemblyEntries
    (V293_owned_record_cells BridgeFrameCells)
    ltac:(apply map_get_sig) ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(change (0<=8 /\ 8+54<=4294967295)%Z;lia) D
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Table Bitmap
    ltac:(unfold ReassemblyTasks;rewrite map_get_set' by (vm_compute;congruence);apply map_get_sig)
    (ReassemblyEntry d)) as (Mf & Step & Exec & Records & Table' & Bitmap' & Returned).
  exists Mf. split; [exact Exec | ]. split; [exact Step | ]. split; [exact Records | ].
  split; [exact Table' | ]. split; [exact Bitmap' | ]. exact Returned.
Qed.

Lemma ReassemblyOtherDelay : forall d Mf,
  V293_task_records Mf (ReassemblyNewTasks d) ->
  load Tint32 Mf (81%positive,172%Z)=Some (Vint32 (Int.repr 5)).
Proof.
  intros d Mf Records.
  assert (Other : get (ReassemblyNewTasks d) ReassemblyOther = Some ReassemblyOtherValue).
  { unfold ReassemblyNewTasks,ReassemblyTasks.
    rewrite map_get_set' by (vm_compute;congruence). apply map_get_set. }
  pose proof (Records ReassemblyOther (Int.repr 4) (wait os_stat_time (Int.repr 5)) Vnull Other)
    as (p & Range & Priority & Fields & Stat & Delay & Message).
  exact Delay.
Qed.

(* Remove exactly one other-task delay byte AFTER obtaining the real Mf.
   The erased heap is a relation ablation, not another C execution. *)
Theorem ReassemblyMissingByteControl : forall P ks, exists Mf,
  ReassemblyExecution P ks 1%Z Mf /\ ReassemblyResult 1%Z Mf /\
  load Tint32 Mf (81%positive,172%Z)=Some (Vint32 (Int.repr 5)) /\
  ~ (V293_target_wstate BridgeGlobal TickLocal (del Mf (81%positive,172%Z))
      (set (ReassemblyAbs 1%Z) abstcblsid (abstcblist (ReassemblyNewTasks 1%Z))) |=
      V293_owned_task_records (ReassemblyNewTasks 1%Z) ** Atrue).
Proof.
  intros P ks.
  destruct (ReassemblyLiteral P ks V293_scheduler 1%Z ltac:(change (0<=1<=4294967295)%Z;lia))
    as (Mf & Exec & Step & Records & Table & Bitmap & Returned).
  exists Mf. split; [exact Exec | ]. split; [exact Returned | ].
  split; [apply (ReassemblyOtherDelay _ _ Records) | ]. intro Missing.
  assert (Bad : V293_task_records (del Mf (81%positive,172%Z)) (ReassemblyNewTasks 1%Z)).
  { apply sat_split in Missing.
    destruct Missing as (m1 & m2 & o1 & o2 & JM & JO & Owned & Rest).
    pose proof (V293_owned_task_records_sound _ _ Owned) as All.
    intros t p st msg Lookup. eapply V293_task_record_sub; [exists m2;exact JM | ].
    apply All. exact Lookup. }
  pose proof (ReassemblyOtherDelay _ _ Bad) as Delay.
  assert (Absent : load Tint32 (del Mf (81%positive,172%Z)) (81%positive,172%Z)=None).
  { unfold load,loadm. cbn [typelen loadbytes].
    rewrite map_del_sem.
    match goal with |- context [if ?decision then _ else _] =>
      destruct decision as [Same|Apart] end; [reflexivity | contradiction]. }
  rewrite Absent in Delay. discriminate.
Qed.

Theorem ReassemblyFrameAndPointer : forall P ks, exists Mf,
  ReassemblyExecution P ks 3%Z Mf /\ ReassemblyResult 3%Z Mf /\
  load (Tptr V293_tcb_type) Mf (70%positive,0%Z)=Some (Vptr ReassemblyOther) /\
  load Tint32 Mf (90%positive,0%Z)=Some (Vint32 (Int.repr 99)) /\
  load Tint32 Mf (81%positive,172%Z)=Some (Vint32 (Int.repr 5)).
Proof.
  intros P ks.
  destruct (ReassemblyLiteral P ks V293_scheduler 3%Z ltac:(change (0<=3<=4294967295)%Z;lia))
    as (Mf & Exec & Step & Records & Table & Bitmap & Returned).
  exists Mf. split; [exact Exec | ]. split; [exact Returned | ].
  unfold ReassemblyResult in Returned.
  split.
  - assert (Pointer : V293_target_wstate BridgeGlobal TickLocal Mf
      (set (ReassemblyAbs 3%Z) abstcblsid (abstcblist (ReassemblyNewTasks 3%Z))) |=
      V293_owned_record_cell (V293_tick_pointer_cell 70%positive ReassemblyOther) ** Atrue)
      by (clear -Returned;sep auto).
    change (load (Tptr V293_tcb_type) (getmem (V293_target_wstate BridgeGlobal TickLocal Mf
      (set (ReassemblyAbs 3%Z) abstcblsid (abstcblist (ReassemblyNewTasks 3%Z))))) (70%positive,0%Z)=Some (Vptr ReassemblyOther)).
    eapply V293_record_star_load_l; [apply V293_owned_record_cell_load | exact Pointer].
  - split.
    + assert (Frame : V293_target_wstate BridgeGlobal TickLocal Mf
        (set (ReassemblyAbs 3%Z) abstcblsid (abstcblist (ReassemblyNewTasks 3%Z))) |=
        V293_owned_record_cells BridgeFrameCells ** Atrue) by (clear -Returned;sep auto).
      change (load Tint32 (getmem (V293_target_wstate BridgeGlobal TickLocal Mf
        (set (ReassemblyAbs 3%Z) abstcblsid (abstcblist (ReassemblyNewTasks 3%Z))))) (90%positive,0%Z)=Some (Vint32 (Int.repr 99))).
      eapply V293_record_star_load_l; [ | exact Frame].
      apply V293_owned_record_cells_load. left;reflexivity.
    + apply (ReassemblyOtherDelay _ _ Records).
Qed.

(* An overlapping Atrue projection is not a second writable resource.
   Updating one alleged copy would otherwise contradict the framed copy. *)
Theorem ReassemblyNoDuplicateByte : forall ge le M ir aux O op,
  ~ ((ge,le,M,ir,aux,O,op) |=
      V293_owned_record_cell ((81%positive,178%Z),Tint8,V293_byteval 4) **
      (V293_owned_record_cell ((81%positive,178%Z),Tint8,V293_byteval 4) ** Atrue)).
Proof.
  intros ge le M ir aux O op Duplicate.
  destruct (V293_owned_record_cell_update (81%positive,178%Z) Tint8 (V293_byteval 4) (V293_byteval 5) _
    _ _ _ _ _ _ _ eq_refl Duplicate) as (Mf & Store & Returned).
  assert (New : load Tint8 Mf (81%positive,178%Z)=Some (V293_byteval 5)).
  { change (load Tint8 (getmem (ge,le,Mf,ir,aux,O,op)) (81%positive,178%Z)=Some (V293_byteval 5)).
    eapply V293_record_star_load_l; [apply V293_owned_record_cell_load | exact Returned]. }
  assert (Old : load Tint8 Mf (81%positive,178%Z)=Some (V293_byteval 4)).
  { assert (Frame : (ge,le,Mf,ir,aux,O,op) |=
      V293_owned_record_cell ((81%positive,178%Z),Tint8,V293_byteval 4) ** Atrue)
      by (clear -Returned;sep auto).
    change (load Tint8 (getmem (ge,le,Mf,ir,aux,O,op)) (81%positive,178%Z)=Some (V293_byteval 4)).
    eapply V293_record_star_load_l; [apply V293_owned_record_cell_load | exact Frame]. }
  rewrite New in Old. discriminate.
Qed.

(* The pointed-to task is NOT the first entry in canonical task-map order.
   Its writable record is focused while the rest, pointer and frame survive. *)
Theorem ReassemblyFocusNext : forall d Mf,
  ReassemblyResult d Mf ->
  V293_target_wstate BridgeGlobal TickLocal Mf
    (set (ReassemblyAbs d) abstcblsid (abstcblist (ReassemblyNewTasks d))) |=
  V293_owned_task_record ReassemblyOther (Int.repr 4) (wait os_stat_time (Int.repr 5)) Vnull **
  (V293_owned_task_records (del (ReassemblyNewTasks d) ReassemblyOther) **
  ((V293_owned_record_cell (V293_tick_pointer_cell 70%positive ReassemblyOther) **
    (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive
      (V293_ready_group (fst (V293_tick_wait_rows 0 0 d 10)) (snd (V293_tick_wait_rows 0 0 d 10)))
      (fst (V293_tick_wait_rows 0 0 d 10)) (snd (V293_tick_wait_rows 0 0 d 10))) **
    (V293_shared_fields BridgeTask (ReassemblyNewTasks d) (emp : EcbMod.map) (Int.repr 37) **
      V293_owned_record_cells BridgeFrameCells))) ** Atrue)).
Proof.
  intros d Mf Result. eapply V293_owned_task_records_focus; [ | exact Result].
  change (get (ReassemblyNewTasks d) ReassemblyOther=Some ReassemblyOtherValue).
  unfold ReassemblyNewTasks,ReassemblyTasks.
  rewrite map_get_set' by (vm_compute;congruence). apply map_get_set.
Qed.
