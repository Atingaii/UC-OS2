(* Encoded spatial entry, independently of execution. Not initialization
   reachability, a complete TCB, or an ISR/whole-kernel theorem. *)
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TimeTickTraversalProbe.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

(* Stat=SEM, StatPend=OK, ready group/row=8 and a disjoint sentinel.
   These bytes have no permissions shared with the two write destinations. *)
Definition CountdownFrameCells : list V293_record_cell :=
  [((81%positive,56%Z),Tint8,Vint32 Int.one);
   ((81%positive,57%Z),Tint8,Vint32 Int.zero);
   ((92%positive,0%Z),Tint8,Vint32 (Int.repr 8));
   ((93%positive,0%Z),Tint8,Vint32 (Int.repr 8));
   ((90%positive,0%Z),Tint32,Vint32 (Int.repr 99))].
Definition CountdownFrame : asrt := V293_owned_record_cells CountdownFrameCells.
Definition CountdownCells d : list V293_record_cell :=
  ((70%positive,0%Z),Tptr V293_tcb_type,Vptr (81%positive,Int.repr 8)) ::
  ((81%positive,52%Z),Tint32,Vint32 (Int.repr d)) ::
  ((81%positive,28%Z),Tcom_ptr 410%Z,Vptr TickNext) :: CountdownFrameCells.
Definition CountdownMemory d : mem := OwnershipCellsMemory (CountdownCells d).

Theorem CountdownEntrySatisfiable : forall enabled d,
  TickState enabled (CountdownMemory d) |=
    V293_owned_record_cell ((70%positive,0%Z),Tptr V293_tcb_type,Vptr (81%positive,Int.repr 8)) **
    (V293_tick_countdown_node 81%positive 8%Z d TickNext ** CountdownFrame).
Proof.
  intros enabled d.
  assert (Apart : OwnershipCellsSeparated (CountdownCells d)).
  { vm_compute. repeat split; intros; intuition congruence. }
  assert (Valid : Forall (fun cell => let '(_,tp,v) := cell in
    rule_type_val_match tp v = true) (CountdownCells d)).
  { repeat constructor; reflexivity. }
  pose proof (OwnershipCellsSpatial _ Apart Valid emp TickLocal) as Entry.
  assert (Rebased : TickState enabled (CountdownMemory d) |=
      V293_owned_record_cells (CountdownCells d)).
  { unfold TickState,CountdownMemory. eapply TickCellsRebase. exact Entry. }
  change (TickState enabled (CountdownMemory d) |=
    V293_owned_record_cell ((70%positive,0%Z),Tptr V293_tcb_type,Vptr (81%positive,Int.repr 8)) **
    (V293_owned_record_cell ((81%positive,52%Z),Tint32,Vint32 (Int.repr d)) **
      (V293_owned_record_cell ((81%positive,28%Z),Tcom_ptr 410%Z,Vptr TickNext) ** CountdownFrame))) in Rebased.
  eapply astar_mono; [ | | exact Rebased].
  - intros s H; exact H.
  - intros s H. apply astar_assoc_intro. exact H.
Qed.

Definition CountdownExecution P ks enabled d Mf : Prop :=
  V293_local_steps P (curs (V293_tick_iteration 901%Z 902%Z 903%Z),(kenil,ks))
    ((emp,TickLocal,CountdownMemory d),(fun _ => false),(enabled,(3%nat :: nil),(false :: nil)))
    (curs (sskip None),(kenil,ks))
    ((emp,TickLocal,Mf),(fun _ => false),(enabled,(3%nat :: nil),(false :: nil))).

Theorem CountdownLiteralExecution : forall P ks enabled d,
  (2 <= d <= Int.max_unsigned)%Z ->
  exists Mf,
  CountdownExecution P ks enabled d Mf /\
  load Tint32 Mf (81%positive,52%Z) = Some (Vint32 (Int.repr (d-1))) /\
  load (Tptr V293_tcb_type) Mf (70%positive,0%Z) = Some (Vptr TickNext) /\
  (forall a tp v, In (a,tp,v) CountdownFrameCells -> load tp Mf a = Some v) /\
  TickState enabled Mf |=
    V293_owned_record_cell ((70%positive,0%Z),Tptr V293_tcb_type,Vptr TickNext) **
    (V293_tick_countdown_node 81%positive 8%Z (d-1)%Z TickNext ** CountdownFrame).
Proof.
  intros P ks enabled d Range.
  destruct (V293_tick_countdown_iteration_owned_execution P ks emp TickLocal (CountdownMemory d)
    (fun _ => false) enabled (3%nat :: nil) (false :: nil) emp (spec_done None) 901%Z 902%Z 903%Z
    70%positive 81%positive 8%Z d TickNext CountdownFrame
    ltac:(apply map_get_sig) ltac:(lia) ltac:(change (8+44<=4294967295)%Z;lia)
    Range (CountdownEntrySatisfiable enabled d)) as (M1 & Mf & S1 & S2 & Exec & Dly & Read & Returned & Outside).
  exists Mf. split; [exact Exec | ]. split; [exact Dly | ]. split; [exact Read | ].
  split; [ | exact Returned]. intros a tp v Member.
  change (load tp (getmem (TickState enabled Mf)) a = Some v).
  eapply V293_record_star_load_r; [ | exact Returned].
  eapply V293_record_star_load_r. unfold CountdownFrame.
  eapply V293_owned_record_cells_load. exact Member.
Qed.

(* Actual executions at both endpoints, not just a computed subtraction. *)
Theorem CountdownLiteralEndpoints : forall P ks enabled,
  exists Mlow Mhigh,
  CountdownExecution P ks enabled 2%Z Mlow /\
  load Tint32 Mlow (81%positive,52%Z) = Some (Vint32 Int.one) /\
  CountdownExecution P ks enabled 4294967295%Z Mhigh /\
  load Tint32 Mhigh (81%positive,52%Z) = Some (Vint32 (Int.repr 4294967294)).
Proof.
  intros P ks enabled.
  destruct (CountdownLiteralExecution P ks enabled 2%Z
    ltac:(change (2<=2<=4294967295)%Z;lia)) as (Mlow & Low & LowRead & RestLow).
  destruct (CountdownLiteralExecution P ks enabled 4294967295%Z
    ltac:(change (2<=4294967295<=4294967295)%Z;lia)) as (Mhigh & High & HighRead & RestHigh).
  exists Mlow. exists Mhigh. split; [exact Low | ]. split; [exact LowRead | ].
  split; [exact High | exact HighRead].
Qed.

Theorem CountdownOneReachesExpiry :
  Int.sub Int.one Int.one = Int.zero /\
  Int.eq (Int.sub Int.one Int.one) Int.zero = true.
Proof. vm_compute. split; reflexivity. Qed.

Print Assumptions CountdownEntrySatisfiable.
Print Assumptions CountdownLiteralExecution.
Print Assumptions CountdownLiteralEndpoints.
Print Assumptions CountdownOneReachesExpiry.
