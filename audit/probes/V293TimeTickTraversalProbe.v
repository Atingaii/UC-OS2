(* Literal spatial entry built from encoded bytes BEFORE any execution.
   Not an initialized/reachable kernel state or a whole tick function proof. *)
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.code.V293OSTimeTick.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTraversal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition TickNext : addrval := (82%positive,Int.repr 12).
Definition TickCells : list V293_record_cell :=
  [((70%positive,0%Z),Tptr V293_tcb_type,Vptr (81%positive,Int.repr 8));
   ((81%positive,52%Z),Tint32,Vint32 Int.zero);
   ((81%positive,28%Z),Tcom_ptr 410%Z,Vptr TickNext);
   ((90%positive,0%Z),Tint32,Vint32 (Int.repr 99))].
Definition TickMemory : mem := OwnershipCellsMemory TickCells.
Definition TickLocal : env := sig 901%Z (70%positive,Tptr V293_tcb_type).
Definition TickFrame : asrt := V293_owned_record_cells
  (((90%positive,0%Z),Tint32,Vint32 (Int.repr 99)) :: nil).
Definition TickState enabled M : RstateOP :=
  (emp,TickLocal,M,(fun _ => false),(enabled,(3%nat :: nil),(false :: nil)),emp,spec_done None).

(* Pure byte ownership is independent of the interrupt/control components.
   This helper is only for constructing fixtures, not the traversal proof. *)
Lemma TickCellsRebase : forall cells ge le M ir aux O op,
  (ge,le,M,ir,aux,O,op) |= V293_owned_record_cells cells ->
  forall ir' aux', (ge,le,M,ir',aux',O,op) |= V293_owned_record_cells cells.
Proof.
  induction cells as [ | [[a tp] v] rest IH]; intros ge le M ir aux O op Held ir' aux'.
  - exact Held.
  - apply sat_split in Held. destruct Held as (mh & mt & oh & ot & JM & JO & Head & Tail).
    apply sat_split'. exists mh. exists mt. exists oh. exists ot.
    split; [exact JM | ]. split; [exact JO | ]. split; [ | eapply IH; exact Tail].
    unfold V293_owned_record_cell in *. apply astar_l_apure_elim in Head.
    destruct Head as [Valid Owned]. apply astar_l_apure_intro; [exact Owned | exact Valid].
Qed.

Theorem TickEntrySatisfiable : forall enabled,
  TickState enabled TickMemory |=
    V293_owned_record_cell ((70%positive,0%Z),Tptr V293_tcb_type,Vptr (81%positive,Int.repr 8)) **
    (V293_tick_zero_node 81%positive 8%Z TickNext ** TickFrame).
Proof.
  intro enabled.
  assert (Apart : OwnershipCellsSeparated TickCells).
  { vm_compute. repeat split; intros; intuition congruence. }
  assert (Valid : Forall (fun cell => let '(_,tp,v) := cell in
    rule_type_val_match tp v = true) TickCells).
  { repeat constructor; reflexivity. }
  pose proof (OwnershipCellsSpatial _ Apart Valid emp TickLocal) as Entry.
  assert (Rebased : TickState enabled TickMemory |= V293_owned_record_cells TickCells).
  { unfold TickState,TickMemory. eapply TickCellsRebase. exact Entry. }
  change (TickState enabled TickMemory |=
    V293_owned_record_cell ((70%positive,0%Z),Tptr V293_tcb_type,Vptr (81%positive,Int.repr 8)) **
    (V293_owned_record_cell ((81%positive,52%Z),Tint32,Vint32 Int.zero) **
      (V293_owned_record_cell ((81%positive,28%Z),Tcom_ptr 410%Z,Vptr TickNext) ** TickFrame))) in Rebased.
  eapply astar_mono; [ | | exact Rebased].
  - intros s H; exact H.
  - intros s H. apply astar_assoc_intro. exact H.
Qed.

(* Both IE values and nonempty ISR/critical stacks; a genuinely distinct Next
   address at nonzero offset. Frame value is read in the SAME final Mf. *)
Theorem TickLiteralTraversal : forall P ks enabled,
  exists Mf,
  V293_local_steps P (curs (V293_tick_iteration 901%Z 902%Z 903%Z),(kenil,ks))
    ((emp,TickLocal,TickMemory),(fun _ => false),(enabled,(3%nat :: nil),(false :: nil)))
    (curs (sskip None),(kenil,ks))
    ((emp,TickLocal,Mf),(fun _ => false),(enabled,(3%nat :: nil),(false :: nil))) /\
  load (Tptr V293_tcb_type) Mf (70%positive,0%Z) = Some (Vptr TickNext) /\
  load Tint32 Mf (90%positive,0%Z) = Some (Vint32 (Int.repr 99)) /\
  TickState enabled Mf |=
    V293_owned_record_cell ((70%positive,0%Z),Tptr V293_tcb_type,Vptr TickNext) **
    (V293_tick_zero_node 81%positive 8%Z TickNext ** TickFrame).
Proof.
  intros P ks enabled.
  destruct (V293_tick_zero_iteration_owned_execution P ks emp TickLocal TickMemory
    (fun _ => false) enabled (3%nat :: nil) (false :: nil) emp (spec_done None) 901%Z 902%Z 903%Z
    70%positive 81%positive 8%Z TickNext TickFrame
    ltac:(apply map_get_sig) ltac:(lia) ltac:(change (8+44<=4294967295)%Z;lia)
    (TickEntrySatisfiable enabled)) as (Mf & Store & Exec & Read & Returned & Outside).
  exists Mf. split; [exact Exec | ]. split; [exact Read | ]. split; [ | exact Returned].
  change (load Tint32 (getmem (TickState enabled Mf)) (90%positive,0%Z) = Some (Vint32 (Int.repr 99))).
  eapply V293_record_star_load_r; [ | exact Returned].
  eapply V293_record_star_load_r. unfold TickFrame.
  eapply V293_owned_record_cells_load. left. reflexivity.
Qed.

Theorem TickDistinctSuccessor : TickNext <> (81%positive,Int.repr 8).
Proof. discriminate. Qed.

Print Assumptions TickEntrySatisfiable.
Print Assumptions TickLiteralTraversal.
Print Assumptions TickDistinctSuccessor.
