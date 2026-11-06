(* Four records share ONE block, with disjoint encoded bytes. The entry is
   built before execution; this is not initialized-kernel reachability. *)
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickWhileRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickTaskBridge.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLoop.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TimeTickTraversalProbe.
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

Definition WhileHead : tid := (81%positive,Int.repr 8).
Definition WhileSecond : tid := (81%positive,Int.repr 128).
Definition WhileReady : tid := (81%positive,Int.repr 248).
Definition WhileIdle : tid := (81%positive,Int.repr 368).
Definition WhileReason := os_stat_sem (84%positive,Int.repr 4).
Definition WhileBindings : list (V293_tick_task * (taskstatus * val)) :=
  [(V293_tick_wait_node 81%positive 8%Z 1%Z WhileReason 7 10,
     (wait WhileReason (Int.repr 1),Vnull));
   (V293_tick_wait_node 81%positive 128%Z 3%Z os_stat_time 7 2,
     (wait os_stat_time (Int.repr 3),Vnull));
   (V293_tick_wait_node 81%positive 248%Z 0%Z os_stat_time 7 4,(rdy,Vnull))].
Definition WhileOldTasks := V293_tick_record_map false WhileBindings WhileIdle Vnull.
Definition WhileNewTasks := V293_tick_record_map true WhileBindings WhileIdle Vnull.
Definition WhileFrameCells : list V293_record_cell :=
  [((90%positive,0%Z),Tint32,Vint32 (Int.repr 99))].
Definition WhileGlobal : env := set (sig 902%Z (93%positive,Tarray Tint8 2)) 903%Z (92%positive,Tint8).
Definition WhileCells :=
  V293_tick_pointer_cell 70%positive WhileHead ::
  (V293_tick_chain_cells (map fst WhileBindings) WhileIdle ++
  (V293_tick_bitmap_cells 92%positive 93%positive 3 16 16 ++
  (V293_tick_idle_cell WhileIdle ::
  (concat (map V293_tick_binding_extra WhileBindings) ++
  (V293_tick_idle_extra WhileIdle Vnull ++ WhileFrameCells))))).
Definition WhileMemory := OwnershipCellsMemory WhileCells.
Definition WhileState M : RstateOP :=
  (WhileGlobal,TickLocal,M,(fun _ => false),(false,nil,nil),emp,spec_done None).

Lemma WhileBindingsValid : Forall V293_tick_binding_valid WhileBindings.
Proof.
  unfold WhileBindings.
  repeat (apply Forall_cons; [unfold V293_tick_binding_valid,V293_tick_task_valid;
    vm_compute;repeat split;try discriminate;lia | ]).
  apply Forall_nil.
Qed.
Lemma WhileKeysUnique : NoDup (V293_tick_record_keys WhileBindings WhileIdle).
Proof.
  vm_compute. repeat constructor; simpl; intuition congruence.
Qed.

Theorem WhileEntry : WhileState WhileMemory |=
  V293_tick_loop_owned 70%positive WhileHead (map fst WhileBindings) WhileIdle
    92%positive 93%positive 3 16 16
    (V293_owned_record_cells (concat (map V293_tick_binding_extra WhileBindings)) **
      (V293_owned_record_cells (V293_tick_idle_extra WhileIdle Vnull) **
        V293_owned_record_cells WhileFrameCells)).
Proof.
  assert (Apart : OwnershipCellsSeparated WhileCells).
  { vm_compute. repeat split; intros; intuition congruence. }
  assert (Valid : Forall (fun cell => let '(_,tp,v) := cell in
    rule_type_val_match tp v=true) WhileCells).
  { repeat constructor;reflexivity. }
  pose proof (OwnershipCellsSpatial _ Apart Valid WhileGlobal TickLocal) as Encoded.
  assert (Rebased : WhileState WhileMemory |= V293_owned_record_cells WhileCells).
  { unfold WhileState,WhileMemory. eapply TickCellsRebase. exact Encoded. }
  unfold V293_tick_loop_owned.
  change (WhileState WhileMemory |=
    V293_owned_record_cell (V293_tick_pointer_cell 70%positive WhileHead) **
    V293_owned_record_cells
      (V293_tick_chain_cells (map fst WhileBindings) WhileIdle ++
      (V293_tick_bitmap_cells 92%positive 93%positive 3 16 16 ++
      (V293_tick_idle_cell WhileIdle ::
      (concat (map V293_tick_binding_extra WhileBindings) ++
      (V293_tick_idle_extra WhileIdle Vnull ++ WhileFrameCells)))))) in Rebased.
  eapply astar_mono; [intros st H;exact H | | exact Rebased].
  intros st H. apply V293_tick_cells_append in H.
  eapply astar_mono; [intros st0 H0;exact H0 | | exact H].
  intros st0 H0. apply V293_tick_cells_append in H0.
  eapply astar_mono; [intros st1 H1;exact H1 | | exact H0].
  intros st1 H1. cbn [V293_owned_record_cells] in H1 |- *.
  eapply astar_mono; [intros st2 H2;exact H2 | | exact H1].
  intros st2 H2. apply V293_tick_cells_append in H2.
  eapply astar_mono; [intros st3 H3;exact H3 | | exact H2].
  intros st3 H3. apply V293_tick_cells_append in H3. exact H3.
Qed.

Definition WhileExecution P ks Mf := V293_local_steps P
  (curs (swhile (V293_tick_guard 901%Z) (V293_tick_iteration 901%Z 902%Z 903%Z)),(kenil,ks))
  ((WhileGlobal,TickLocal,WhileMemory),(fun _ => false),(false,nil,nil))
  (curs (sskip None),(kenil,ks)) ((WhileGlobal,TickLocal,Mf),(fun _ => false),(false,nil,nil)).
Definition WhileResult Mf := WhileState Mf |= V293_owned_task_records WhileNewTasks **
  ((V293_owned_record_cell (V293_tick_pointer_cell 70%positive WhileIdle) **
    (V293_owned_record_cells (V293_tick_bitmap_cells 92%positive 93%positive 3 16 20) **
      V293_owned_record_cells WhileFrameCells)) ** Atrue).

Theorem WhileLiteral : forall P ks, exists Mf,
  WhileExecution P ks Mf /\
  load (Tptr V293_tcb_type) Mf (70%positive,0%Z)=Some (Vptr WhileIdle) /\
  V293_task_records Mf WhileNewTasks /\ WhileResult Mf.
Proof.
  intros P ks.
  exact (V293_tick_while_owned_records WhileBindings WhileIdle Vnull P ks
    WhileGlobal TickLocal WhileMemory (fun _ => false) false nil nil emp (spec_done None)
    901%Z 902%Z 903%Z 70%positive 92%positive 93%positive 3 16 16
    (V293_owned_record_cells WhileFrameCells)
    ltac:(apply map_get_sig) ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(vm_compute;reflexivity) ltac:(vm_compute;reflexivity)
    ltac:(change (368+50<=4294967295)%Z;lia) WhileBindingsValid WhileKeysUnique
    ltac:(lia) ltac:(lia) ltac:(lia) WhileEntry).
Qed.

Lemma WhileSecondDelay : forall Mf,
  V293_task_records Mf WhileNewTasks ->
  load Tint32 Mf (81%positive,172%Z)=Some (Vint32 (Int.repr 2)).
Proof.
  intros Mf Records.
  assert (Lookup : get WhileNewTasks WhileSecond=Some (Int.repr 2,wait os_stat_time (Int.repr 2),Vnull)).
  { unfold WhileNewTasks. cbn [WhileBindings V293_tick_record_map].
    rewrite map_get_set' by (vm_compute;congruence). apply map_get_set. }
  pose proof (Records _ _ _ _ Lookup) as (p & Range & Priority & Fields & Stat & Delay & Msg).
  exact Delay.
Qed.

Definition WhileOmitSecond := set WhileNewTasks WhileSecond
  (Int.repr 2,wait os_stat_time (Int.repr 3),Vnull).
(* One abstract record is stale, but the same complete-while Mf is used.
   No heap erasure and no rejected entry can manufacture this failure. *)
Theorem WhileOmitSecondControl : forall P ks, exists Mf,
  WhileExecution P ks Mf /\ WhileResult Mf /\
  load Tint32 Mf (81%positive,172%Z)=Some (Vint32 (Int.repr 2)) /\
  ~ V293_task_records Mf WhileOmitSecond.
Proof.
  intros P ks. destruct (WhileLiteral P ks) as (Mf & Exec & Pointer & Records & Result).
  exists Mf. split; [exact Exec | ]. split; [exact Result | ].
  pose proof (WhileSecondDelay _ Records) as Delay.
  split; [exact Delay | ]. intro Stale.
  pose proof (Stale WhileSecond (Int.repr 2) (wait os_stat_time (Int.repr 3)) Vnull
    ltac:(apply map_get_set)) as (p & Range & Priority & Fields & Stat & Bad & Msg).
  change (load Tint32 Mf (81%positive,172%Z)=Some (Vint32 (Int.repr 3))) in Bad.
  rewrite Delay in Bad. discriminate.
Qed.

Theorem WhileReadyIdleAndFrame : forall P ks, exists Mf,
  WhileExecution P ks Mf /\ WhileResult Mf /\
  load (Tptr V293_tcb_type) Mf (70%positive,0%Z)=Some (Vptr WhileIdle) /\
  V293_task_record Mf WhileHead (Int.repr 10) rdy Vnull /\
  V293_task_record Mf WhileReady (Int.repr 4) rdy Vnull /\
  V293_task_record Mf WhileIdle (Int.repr 12) rdy Vnull /\
  load Tint32 Mf (90%positive,0%Z)=Some (Vint32 (Int.repr 99)).
Proof.
  intros P ks. destruct (WhileLiteral P ks) as (Mf & Exec & Pointer & Records & Result).
  exists Mf. split; [exact Exec | ]. split; [exact Result | ]. split; [exact Pointer | ].
  split.
  - apply Records. unfold WhileNewTasks. apply map_get_set.
  - split.
    + apply Records. unfold WhileNewTasks. cbn [V293_tick_record_map WhileBindings].
      rewrite !map_get_set' by (vm_compute;congruence). apply map_get_set.
    + split.
      * apply Records. unfold WhileNewTasks. cbn [V293_tick_record_map WhileBindings].
        rewrite !map_get_set' by (vm_compute;congruence). apply map_get_sig.
      * assert (Frame : WhileState Mf |= V293_owned_record_cells WhileFrameCells ** Atrue)
          by (unfold WhileResult in Result;clear -Result;sep auto).
        change (load Tint32 (getmem (WhileState Mf)) (90%positive,0%Z)=Some (Vint32 (Int.repr 99))).
        eapply V293_record_star_load_l; [ | exact Frame].
        apply V293_owned_record_cells_load. left;reflexivity.
Qed.

(* Independently disallow the tempting but invalid full idle record frame:
   writing one alleged priority copy must not preserve another old copy. *)
Theorem WhileNoDuplicateIdlePriority : forall ge le M ir aux O op,
  ~ ((ge,le,M,ir,aux,O,op) |=
    V293_owned_record_cell (V293_tick_idle_cell WhileIdle) **
    (V293_owned_record_cell (V293_tick_idle_cell WhileIdle) ** Atrue)).
Proof.
  intros ge le M ir aux O op Duplicate.
  destruct (V293_owned_record_cell_update (81%positive,418%Z) Tint8 (V293_byteval 12) (V293_byteval 11) _
    _ _ _ _ _ _ _ eq_refl Duplicate) as (Mf & Store & Returned).
  assert (New : load Tint8 Mf (81%positive,418%Z)=Some (V293_byteval 11)).
  { change (load Tint8 (getmem (ge,le,Mf,ir,aux,O,op)) (81%positive,418%Z)=Some (V293_byteval 11)).
    eapply V293_record_star_load_l; [apply V293_owned_record_cell_load | exact Returned]. }
  assert (Old : load Tint8 Mf (81%positive,418%Z)=Some (V293_byteval 12)).
  { assert (Frame : (ge,le,Mf,ir,aux,O,op) |=
      V293_owned_record_cell (V293_tick_idle_cell WhileIdle) ** Atrue) by (clear -Returned;sep auto).
    change (load Tint8 (getmem (ge,le,Mf,ir,aux,O,op)) (81%positive,418%Z)=Some (V293_byteval 12)).
    eapply V293_record_star_load_l; [apply V293_owned_record_cell_load | exact Frame]. }
  rewrite New in Old. discriminate.
Qed.

Theorem WhileInitialData :
  get WhileOldTasks WhileSecond=Some (Int.repr 2,wait os_stat_time (Int.repr 3),Vnull) /\
  load Tint32 WhileMemory (81%positive,52%Z)=Some (Vint32 (Int.repr 1)) /\
  load Tint32 WhileMemory (81%positive,172%Z)=Some (Vint32 (Int.repr 3)) /\
  load Tint32 WhileMemory (81%positive,292%Z)=Some (Vint32 Int.zero) /\
  load Tint8 WhileMemory (81%positive,418%Z)=Some (V293_byteval 12).
Proof.
  split.
  - unfold WhileOldTasks. cbn [WhileBindings V293_tick_record_map].
    rewrite map_get_set' by (vm_compute;congruence). apply map_get_set.
  - assert (Reads : forall a tp v,
      In (a,tp,v) (V293_tick_pointer_cell 70%positive WhileHead ::
        (V293_tick_chain_cells (map fst WhileBindings) WhileIdle ++
          (V293_tick_bitmap_cells 92%positive 93%positive 3 16 16 ++
            [V293_tick_idle_cell WhileIdle]))) -> load tp WhileMemory a=Some v).
    { intros a tp v Member. change (load tp (getmem (WhileState WhileMemory)) a=Some v).
      eapply V293_tick_loop_fields_load; [exact Member | exact WhileEntry]. }
    repeat split; apply Reads; vm_compute; intuition congruence.
Qed.
