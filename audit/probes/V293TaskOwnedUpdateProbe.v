(* Independent statements and a literal entry built from actual spatial cells.
   No completed trace or assumed successor memory is used as entry evidence. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition expected_cell_update : Prop :=
  forall a tp old replacement R ge le M ir aux O op,
  rule_type_val_match tp replacement = true ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cell (a,tp,old) ** R ->
  exists Mf, store tp M a replacement = Some Mf /\
    (ge,le,Mf,ir,aux,O,op) |= V293_owned_record_cell (a,tp,replacement) ** R.
Theorem OwnedCellUpdateContract : expected_cell_update.
Proof. exact V293_owned_record_cell_update. Qed.

Definition expected_task_update : Prop :=
  forall t priority status message new R ge le M ir aux O op,
  new < 13 ->
  (ge,le,M,ir,aux,O,op) |= V293_owned_task_record t priority status message ** R ->
  V293_tcb_update_writable M (fst t) (Int.unsigned (snd t)) /\
  (ge,le,V293_tcb_update_memory M (fst t) (Int.unsigned (snd t)) new,ir,aux,O,op) |=
    V293_owned_task_record t (Int.repr (Z.of_nat new)) status message ** R.
Theorem OwnedTaskUpdateContract : expected_task_update.
Proof. exact V293_owned_task_record_update. Qed.

Definition UpdateTarget : tid := (41%positive,Int.repr 8).
Definition UpdateStatus := wait (os_stat_sem (72%positive,Int.repr 5)) Int.one.
Definition UpdateMessage := Vptr (120%positive,Int.repr 7).
Definition UpdateLocalsCells : list V293_record_cell :=
  [ ((201%positive,0%Z),Tptr V293_tcb_type,Vptr UpdateTarget);
    ((202%positive,0%Z),Tint8,V293_byteval 6);
    ((203%positive,0%Z),Tint8,V293_byteval 0);
    ((204%positive,0%Z),Tint8,V293_byteval 6);
    ((205%positive,0%Z),Tint8,V293_byteval 1);
    ((206%positive,0%Z),Tint8,V293_byteval 64) ].
Definition UpdateFrameCells := UpdateLocalsCells ++
  V293_record_layout (60%positive,Int.zero) 4 rdy Vnull 0.
Definition UpdateCells := V293_record_layout UpdateTarget 8 UpdateStatus UpdateMessage 0 ++ UpdateFrameCells.
Definition UpdateMemory := OwnershipCellsMemory UpdateCells.
Definition UpdateFinalMemory := V293_tcb_update_memory UpdateMemory 41%positive 8%Z 6.
Definition UpdateFrame := V293_owned_record_cells UpdateFrameCells.
Definition UpdateLE : env :=
  set (set (set (set (set (set emp 100%Z (201%positive,Tptr V293_tcb_type))
    101%Z (202%positive,Tint8)) 102%Z (203%positive,Tint8))
    103%Z (204%positive,Tint8)) 104%Z (205%positive,Tint8)) 105%Z (206%positive,Tint8).

Lemma UpdateSeparated : OwnershipCellsSeparated UpdateCells.
Proof. vm_compute. repeat split; intros; intuition congruence. Qed.
Lemma UpdateValid : Forall
  (fun cell => let '(_,tp,v) := cell in rule_type_val_match tp v = true) UpdateCells.
Proof. repeat constructor; vm_compute; reflexivity. Qed.
Lemma UpdateCellsSpatial :
  V293_wstate emp UpdateLE UpdateMemory |= V293_owned_record_cells UpdateCells.
Proof. exact (OwnershipCellsSpatial _ UpdateSeparated UpdateValid emp UpdateLE). Qed.

Theorem UpdateEntrySpatial : V293_wstate emp UpdateLE UpdateMemory |=
  V293_owned_task_record UpdateTarget (Int.repr 8) UpdateStatus UpdateMessage ** UpdateFrame.
Proof.
  pose proof UpdateCellsSpatial as Cells.
  unfold UpdateCells in Cells. apply OwnershipCellsAppend in Cells.
  eapply astar_mono; [ | intros s H; exact H | exact Cells].
  intros s H. exists 8. exists 0. apply astar_l_apure_intro.
  - exact H.
  - repeat split; reflexivity || lia.
Qed.

Lemma UpdateEntryLoad : forall a tp v,
  In (a,tp,v) UpdateCells -> load tp UpdateMemory a = Some v.
Proof.
  intros. eapply V293_owned_record_cells_load with
    (s := V293_wstate emp UpdateLE UpdateMemory); [exact H | exact UpdateCellsSpatial].
Qed.
Lemma UpdateEntryPointer : load (Tptr V293_tcb_type) UpdateMemory (201%positive,0%Z) =
  Some (Vptr (41%positive,Int.repr 8)).
Proof. apply UpdateEntryLoad. vm_compute. intuition congruence. Qed.
Lemma UpdateEntryLocals : V293_rekey_locals emp UpdateLE UpdateMemory 41%positive 41%positive
  (V293_tcb_update_bindings 101%Z 102%Z 103%Z 104%Z 105%Z 6).
Proof.
  intros x value Member.
  cbn [V293_tcb_update_bindings V293_prio_row V293_prio_bit] in Member.
  destruct Member as [E | [E | [E | [E | [E | E]]]]]; [ | | | | | contradiction];
    inversion E; subst x value.
  - exists 202%positive. split; [vm_compute; reflexivity | ].
    split; [discriminate | ]. split; [discriminate | ].
    apply UpdateEntryLoad. vm_compute. intuition congruence.
  - exists 203%positive. split; [vm_compute; reflexivity | ].
    split; [discriminate | ]. split; [discriminate | ].
    apply UpdateEntryLoad. vm_compute. intuition congruence.
  - exists 204%positive. split; [vm_compute; reflexivity | ].
    split; [discriminate | ]. split; [discriminate | ].
    apply UpdateEntryLoad. vm_compute. intuition congruence.
  - exists 205%positive. split; [vm_compute; reflexivity | ].
    split; [discriminate | ]. split; [discriminate | ].
    apply UpdateEntryLoad. vm_compute. intuition congruence.
  - exists 206%positive. split; [vm_compute; reflexivity | ].
    split; [discriminate | ]. split; [discriminate | ].
    apply UpdateEntryLoad. vm_compute. intuition congruence.
Qed.

(* Literal AST field sequence: priority, row, bit, row mask, bit mask. *)
Definition UpdateFiveAssignments :=
  sseq (sassign (efield (ederef (evar 100%Z)) 16%Z) (evar 101%Z))
  (sseq (sassign (efield (ederef (evar 100%Z)) 18%Z) (evar 102%Z))
  (sseq (sassign (efield (ederef (evar 100%Z)) 17%Z) (evar 103%Z))
  (sseq (sassign (efield (ederef (evar 100%Z)) 20%Z) (evar 104%Z))
        (sassign (efield (ederef (evar 100%Z)) 19%Z) (evar 105%Z))))).

Theorem UpdateLiteralExecution : forall P ks,
  cstepstar P (curs UpdateFiveAssignments,(kenil,ks)) (emp,UpdateLE,UpdateMemory)
    (curs (sskip None),(kenil,ks)) (emp,UpdateLE,UpdateFinalMemory) /\
  V293_wstate emp UpdateLE UpdateFinalMemory |=
    V293_owned_task_record UpdateTarget (Int.repr 6) UpdateStatus UpdateMessage ** UpdateFrame.
Proof.
  intros P ks.
  pose proof (V293_task_prio_tcb_owned_execution P ks emp UpdateLE UpdateMemory
    (fun _ => false) (false,nil,nil) emp (spec_done None)
    100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 201%positive 41%positive 8%Z
    (Int.repr 8) UpdateStatus UpdateMessage 6 UpdateFrame
    ltac:(lia) ltac:(lia) ltac:(unfold Int.max_unsigned, Int.modulus, Int.wordsize; simpl; lia)
    eq_refl ltac:(discriminate) UpdateEntryPointer UpdateEntryLocals UpdateEntrySpatial) as Result.
  destruct Result as [[Execution Rest] Owned]. split; [exact Execution | exact Owned].
Qed.

Lemma UpdateOwnedPriorityLoad : forall t priority status message s,
  s |= V293_owned_task_record t priority status message ->
  load Tint8 (getmem s) (fst t,(Int.unsigned (snd t)+50)%Z) = Some (Vint32 priority).
Proof.
  intros t priority status message s [p [pend Owned]].
  apply astar_l_apure_elim in Owned. destruct Owned as [[Range [Priority Pend]] Cells].
  subst priority. eapply V293_owned_record_cells_load with
    (cells := V293_record_layout t p status message pend); [left; reflexivity | exact Cells].
Qed.

Theorem UpdateFinalSpatial : V293_wstate emp UpdateLE UpdateFinalMemory |=
  V293_owned_task_record UpdateTarget (Int.repr 6) UpdateStatus UpdateMessage ** UpdateFrame.
Proof. exact (proj2 (UpdateLiteralExecution (fun _ => None) kstop)). Qed.

Theorem UpdateFinalPriority : load Tint8 UpdateFinalMemory (41%positive,58%Z) =
  Some (V293_byteval 6).
Proof.
  eapply V293_record_star_load_l with
    (s := V293_wstate emp UpdateLE UpdateFinalMemory); [ | exact UpdateFinalSpatial].
  intros s Owned. exact (UpdateOwnedPriorityLoad _ _ _ _ _ Owned).
Qed.

Theorem UpdateFinalFrameLoads :
  load Tint8 UpdateFinalMemory (202%positive,0%Z) = Some (V293_byteval 6) /\
  load Tint8 UpdateFinalMemory (60%positive,50%Z) = Some (V293_byteval 4).
Proof.
  split; eapply V293_record_star_load_r with
    (s := V293_wstate emp UpdateLE UpdateFinalMemory); [ | exact UpdateFinalSpatial | | exact UpdateFinalSpatial];
    intros s Frame; eapply V293_owned_record_cells_load; [ | exact Frame | | exact Frame];
    vm_compute; intuition congruence.
Qed.

Theorem UpdateRejectsStaleOwnership :
  ~ V293_wstate emp UpdateLE UpdateFinalMemory |=
    V293_owned_task_record UpdateTarget (Int.repr 8) UpdateStatus UpdateMessage ** UpdateFrame.
Proof.
  intro Stale.
  assert (Old : load Tint8 UpdateFinalMemory (41%positive,58%Z) = Some (V293_byteval 8)).
  { eapply V293_record_star_load_l with
    (s := V293_wstate emp UpdateLE UpdateFinalMemory); [ | exact Stale].
    intros s Owned. exact (UpdateOwnedPriorityLoad _ _ _ _ _ Owned). }
  rewrite UpdateFinalPriority in Old. vm_compute in Old. discriminate.
Qed.

Print Assumptions OwnedCellUpdateContract.
Print Assumptions OwnedTaskUpdateContract.
Print Assumptions UpdateEntrySpatial.
Print Assumptions UpdateLiteralExecution.
Print Assumptions UpdateFinalPriority.
Print Assumptions UpdateFinalFrameLoads.
Print Assumptions UpdateRejectsStaleOwnership.
