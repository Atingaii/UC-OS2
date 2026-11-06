(* Real initializer field stores extend the spatial records of every task.
   This is not publication, a ghost-map step, full TCB ownership, or OSInit.
   Byte separation suffices: old and new records may share a memory block. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_task_list_insert_record : forall entries t priority status message R,
  TcbMod.get' entries t=None ->
  V293_owned_task_record t priority status message **
    (V293_owned_task_list entries ** R) ==>
  V293_owned_task_list (TcbMod.set' t (priority,status,message) entries) ** R.
Proof.
  induction entries as [ | [head [[hp hs] hm]] tail IH];
    intros t priority status message R Fresh s Owned.
  - cbn [TcbMod.set' V293_owned_task_list] in *. clear -Owned. sep auto.
  - cbn [TcbMod.set']. destruct (tidspec.blt t head) eqn:Before.
    + cbn [V293_owned_task_list] in *. clear -Owned. sep auto.
    + cbn [TcbMod.get'] in Fresh. destruct (tidspec.beq t head) eqn:Same;
        [discriminate | ].
      cbn [V293_owned_task_list] in Owned |- *.
      assert (Reordered : s |= V293_owned_task_record t priority status message **
        (V293_owned_task_list tail ** (V293_owned_task_record head hp hs hm ** R))).
      { clear -Owned. sep auto. }
      apply (IH t priority status message _ Fresh) in Reordered.
      clear -Reordered. sep auto.
Qed.

Theorem V293_task_records_insert : forall tasks t priority status message R,
  get tasks t=None ->
  V293_owned_task_record t priority status message **
    (V293_owned_task_records tasks ** R) ==>
  V293_owned_task_records (set tasks t (priority,status,message)) ** R.
Proof.
  intros tasks t priority status message R Fresh.
  unfold V293_owned_task_records. apply V293_task_list_insert_record. exact Fresh.
Qed.

Lemma V293_raw_cells_move_frame : forall cells A B,
  V293_rdy_raw_cells cells (A ** B) ==> A ** V293_rdy_raw_cells cells B.
Proof.
  induction cells as [ | [[a tp] v] cells IH];intros A B s Owned;
    cbn [V293_rdy_raw_cells] in *;[exact Owned | ].
  assert (Moved : s |= Amapsto a tp true v ** (A ** V293_rdy_raw_cells cells B)).
  { eapply astar_mono;[intros st HS;exact HS | apply IH | exact Owned]. }
  clear -Moved. sep auto.
Qed.

Theorem V293_OS_TCBInit_fields_extend_records : forall tasks P ks ge le M ir aux O op R
  ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo bt base
  p top bottom identity size ext options old,
  p<13 -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
  get tasks (bt,Int.repr base)=None ->
  V293_tcb_init_env le ptcb prio ptos pbos id stk_size pext opt bc bp bs bb bi bz be bo ->
  V293_tcb_init_values_valid top bottom identity size ext options ->
  (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
    (V293_tcb_init_old_fields bt base old ++
     V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options)
    (V293_owned_task_records tasks ** R) ->
  exists Mf,
    cstepstar P (curs (V293_TCBInit_fields ptcb prio ptos pbos id stk_size pext opt),(kenil,ks))
      (ge,le,M) (curs (sskip None),(kenil,ks)) (ge,le,Mf) /\
    (ge,le,Mf,ir,aux,O,op) |=
      V293_owned_task_records
        (set tasks (bt,Int.repr base) (Int.repr (Z.of_nat p),rdy,Vnull)) **
      V293_rdy_raw_cells
        (V293_tcb_init_record_remainder bt base top bottom identity size ext options)
        (V293_rdy_raw_cells
          (V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options) R).
Proof.
  intros tasks P ks ge le M ir aux O op R ptcb prio ptos pbos id stk_size pext opt
    bc bp bs bb bi bz be bo bt base p top bottom identity size ext options old
    Range Base Bound Fresh Env Valid Owned.
  destruct (V293_OS_TCBInit_fields_execution P ks ge le M ir aux O op
    (V293_owned_task_records tasks ** R) ptcb prio ptos pbos id stk_size pext opt
    bc bp bs bb bi bz be bo bt base p top bottom identity size ext options old
    Range Base Bound Env Valid Owned) as (Mf&Exec&Final).
  exists Mf. split;[exact Exec | ].
  apply V293_raw_cells_move_frame in Final. rewrite V293_raw_cells_append in Final.
  assert (Record : (ge,le,Mf,ir,aux,O,op) |= V293_owned_task_records tasks **
    (V293_owned_task_record (bt,Int.repr base) (Int.repr (Z.of_nat p)) rdy Vnull **
      V293_rdy_raw_cells (V293_tcb_init_record_remainder bt base top bottom identity size ext options)
        (V293_rdy_raw_cells
          (V293_tcb_init_input_cells bc bp bs bb bi bz be bo bt base p top bottom identity size ext options) R))).
  { eapply astar_mono;[intros st HS;exact HS | | exact Final].
    apply V293_initialized_ready_record;try assumption;lia. }
  apply (V293_task_records_insert tasks (bt,Int.repr base)
    (Int.repr (Z.of_nat p)) rdy Vnull _ Fresh).
  clear -Record. sep auto.
Qed.
Print Assumptions V293_task_records_insert.
Print Assumptions V293_OS_TCBInit_fields_extend_records.
