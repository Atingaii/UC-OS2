(* Independent encoded spatial witnesses, BEFORE execution, for all byte Stat
   inputs. This is not an initialized or globally consistent kernel state. *)
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TimeTickTraversalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickExpiry.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
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

Definition ExpiryGlobal : env := set (sig 902%Z (93%positive,Tarray Tint8 2)) 903%Z (92%positive,Tint8).
Definition ExpiryFrameCells : list V293_record_cell :=
  [((90%positive,0%Z),Tint32,Vint32 (Int.repr 99));
   ((93%positive,0%Z),Tint8,V293_byteval 85);
   ((81%positive,36%Z),Tcom_ptr 411%Z,Vptr (84%positive,Int.repr 4));
   ((81%positive,40%Z),Tptr Tvoid,Vptr (85%positive,Int.repr 4))].
Definition ExpiryFrame := V293_owned_record_cells ExpiryFrameCells.
Definition ExpiryCells s := V293_tick_expiry_cells 70%positive 81%positive 8%Z
  (81%positive,Int.repr 8) Int.one TickNext s 7 1 2 92%positive 1 93%positive 128.
Definition ExpiryMemory s := OwnershipCellsMemory (ExpiryCells s ++ ExpiryFrameCells).
Definition ExpiryState enabled M : RstateOP :=
  (ExpiryGlobal,TickLocal,M,(fun _ => false),(enabled,(3%nat :: nil),(false :: nil)),emp,spec_done None).

Local Lemma ExpirySplitCells : forall cells frame state,
  state |= V293_owned_record_cells (cells ++ frame) ->
  state |= V293_owned_record_cells cells ** V293_owned_record_cells frame.
Proof.
  induction cells as [ | cell rest IH]; intros frame state Held.
  - cbn [app V293_owned_record_cells] in *. apply astar_l_aemp_intro. exact Held.
  - cbn [app V293_owned_record_cells] in *. apply astar_assoc_intro.
    eapply astar_mono; [ | | exact Held].
    + intros st H; exact H.
    + intros st H; apply IH; exact H.
Qed.

Theorem ExpiryEntrySatisfiable : forall enabled s,
  s < 256 -> ExpiryState enabled (ExpiryMemory s) |=
    V293_owned_record_cells (ExpiryCells s) ** ExpiryFrame.
Proof.
  intros enabled s S.
  assert (Apart : OwnershipCellsSeparated (ExpiryCells s ++ ExpiryFrameCells)).
  { vm_compute. repeat split; intros; intuition congruence. }
  assert (Valid : Forall (fun cell => let '(_,tp,v) := cell in
    rule_type_val_match tp v = true) (ExpiryCells s ++ ExpiryFrameCells)).
  { repeat constructor; try reflexivity. exact (V293_byte_type s S). }
  pose proof (OwnershipCellsSpatial _ Apart Valid ExpiryGlobal TickLocal) as Entry.
  assert (Rebased : ExpiryState enabled (ExpiryMemory s) |=
    V293_owned_record_cells (ExpiryCells s ++ ExpiryFrameCells)).
  { unfold ExpiryState,ExpiryMemory. eapply TickCellsRebase. exact Entry. }
  apply ExpirySplitCells. exact Rebased.
Qed.

Definition ExpiryExecution P ks enabled s Mf : Prop :=
  V293_local_steps P (curs (V293_tick_iteration 901%Z 902%Z 903%Z),(kenil,ks))
    ((ExpiryGlobal,TickLocal,ExpiryMemory s),(fun _ => false),(enabled,(3%nat :: nil),(false :: nil)))
    (curs (sskip None),(kenil,ks))
    ((ExpiryGlobal,TickLocal,Mf),(fun _ => false),(enabled,(3%nat :: nil),(false :: nil))).

Theorem ExpiryLiteralExecution : forall P ks enabled s,
  s < 256 -> exists Mf,
  ExpiryExecution P ks enabled s Mf /\
  load Tint32 Mf (81%positive,52%Z) = Some (Vint32 Int.zero) /\
  load Tint8 Mf (81%positive,56%Z) = Some (V293_byteval (V293_tick_expired_stat s)) /\
  load Tint8 Mf (81%positive,57%Z) = Some (V293_byteval (V293_tick_expired_pend s)) /\
  load Tint8 Mf (92%positive,0%Z) = Some (V293_byteval (V293_tick_expired_group s 1 1)) /\
  load Tint8 Mf (93%positive,1%Z) = Some (V293_byteval (V293_tick_expired_row s 128 2)) /\
  load (Tptr V293_tcb_type) Mf (70%positive,0%Z) = Some (Vptr TickNext) /\
  (forall a tp v, In (a,tp,v) ExpiryFrameCells -> load tp Mf a = Some v) /\
  ExpiryState enabled Mf |= V293_owned_record_cells
    (V293_tick_expiry_cells 70%positive 81%positive 8%Z TickNext Int.zero TickNext
      (V293_tick_expired_stat s) (V293_tick_expired_pend s) 1 2 92%positive
      (V293_tick_expired_group s 1 1) 93%positive (V293_tick_expired_row s 128 2)) ** ExpiryFrame.
Proof.
  intros P ks enabled s S.
  destruct (V293_tick_expiry_iteration_owned_execution P ks ExpiryGlobal TickLocal (ExpiryMemory s)
    (fun _ => false) enabled (3%nat :: nil) (false :: nil) emp (spec_done None) 901%Z 902%Z 903%Z
    70%positive 81%positive 8%Z TickNext s 7 1 2 92%positive 1 93%positive 128 ExpiryFrame
    ltac:(apply map_get_sig) ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(lia) ltac:(change (8+54<=4294967295)%Z;lia)
    S ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (ExpiryEntrySatisfiable enabled s S)) as (Mf & Exec & Dly & Stat & Pend & Group & Row & Pointer & Returned).
  exists Mf. split; [exact Exec | ]. split; [exact Dly | ]. split; [exact Stat | ].
  split; [exact Pend | ]. split; [exact Group | ]. split; [exact Row | ]. split; [exact Pointer | ].
  split; [ | exact Returned]. intros a tp v Member.
  change (load tp (getmem (ExpiryState enabled Mf)) a = Some v).
  eapply V293_record_star_load_r; [ | exact Returned].
  unfold ExpiryFrame. apply V293_owned_record_cells_load. exact Member.
Qed.

(* Each row below obtains an ACTUAL execution from the independently built
   entry, not only evaluation of the three output functions. *)
Theorem ExpiryFourBranches : forall P ks enabled s finalstat finalpend finalgroup finalrow,
  In (s,finalstat,finalpend,finalgroup,finalrow)
    [(0,0,0,3,132);(1,0,1,3,132);(8,8,0,1,128);(9,8,1,1,128)] ->
  exists Mf,
  ExpiryExecution P ks enabled s Mf /\
  load Tint32 Mf (81%positive,52%Z) = Some (Vint32 Int.zero) /\
  load Tint8 Mf (81%positive,56%Z) = Some (V293_byteval finalstat) /\
  load Tint8 Mf (81%positive,57%Z) = Some (V293_byteval finalpend) /\
  load Tint8 Mf (92%positive,0%Z) = Some (V293_byteval finalgroup) /\
  load Tint8 Mf (93%positive,1%Z) = Some (V293_byteval finalrow).
Proof.
  intros P ks enabled s finalstat finalpend finalgroup finalrow Member.
  assert (Expected : s < 256 /\
    V293_tick_expired_stat s = finalstat /\ V293_tick_expired_pend s = finalpend /\
    V293_tick_expired_group s 1 1 = finalgroup /\ V293_tick_expired_row s 128 2 = finalrow).
  { simpl in Member. destruct Member as [E | [E | [E | [E | E]]]]; try contradiction;
      inversion E; subst; repeat split; try reflexivity; lia. }
  destruct Expected as (S & Estat & Epend & Egroup & Erow).
  destruct (ExpiryLiteralExecution P ks enabled s S)
    as (Mf & Exec & Dly & Stat & Pend & Group & Row & Rest).
  rewrite Estat in Stat. rewrite Epend in Pend. rewrite Egroup in Group. rewrite Erow in Row.
  exists Mf. split; [exact Exec | ]. split; [exact Dly | ].
  split; [exact Stat | ]. split; [exact Pend | ]. split; [exact Group | exact Row].
Qed.

Theorem ExpiryMaskAndUpperBits : forall P ks enabled,
  forall s, In s [2;4;16;32;64;128;255] -> exists Mf,
  ExpiryExecution P ks enabled s Mf /\
  load Tint8 Mf (81%positive,56%Z) = Some (V293_byteval (V293_tick_expired_stat s)) /\
  load Tint8 Mf (81%positive,57%Z) = Some (V293_byteval (V293_tick_expired_pend s)).
Proof.
  intros P ks enabled s Member.
  assert (S : s < 256) by (simpl in Member; intuition lia).
  destruct (ExpiryLiteralExecution P ks enabled s S) as (Mf & Exec & Dly & Stat & Pend & Rest).
  exists Mf. split; [exact Exec | ]. split; assumption.
Qed.

Print Assumptions ExpiryEntrySatisfiable.
Print Assumptions ExpiryLiteralExecution.
Print Assumptions ExpiryFourBranches.
Print Assumptions ExpiryMaskAndUpperBits.
