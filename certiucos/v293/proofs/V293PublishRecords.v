(* Real publication writes borrow three fields from the new ready record,
   then return them; all existing records remain spatially owned. The abstract
   task slot O is unchanged. This is not a full TCB call or OSInit theorem. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_task_list_extract_fresh : forall entries t priority status message R,
 TcbMod.get' entries t=None ->
 V293_owned_task_list (TcbMod.set' t (priority,status,message) entries) ** R ==>
 V293_owned_task_record t priority status message ** (V293_owned_task_list entries ** R).
Proof.
 induction entries as [ | [head [[hp hs] hm]] tail IH];
 intros t priority status message R Fresh s Owned.
 - cbn [TcbMod.set' V293_owned_task_list] in *. clear -Owned. sep auto.
 - cbn [TcbMod.set'] in Owned. destruct (tidspec.blt t head) eqn:Before.
   + cbn [V293_owned_task_list] in *. clear -Owned. sep auto.
   + cbn [TcbMod.get'] in Fresh. destruct (tidspec.beq t head) eqn:Same;[discriminate | ].
     cbn [V293_owned_task_list] in Owned |- *.
     assert (Reordered : s |= V293_owned_task_list (TcbMod.set' t (priority,status,message) tail) **
        (V293_owned_task_record head hp hs hm ** R)) by (clear -Owned;sep auto).
     apply (IH t priority status message _ Fresh) in Reordered.
     clear -Reordered. sep auto.
Qed.
Lemma V293_task_records_extract_fresh : forall tasks t priority status message R,
 get tasks t=None ->
 V293_owned_task_records (set tasks t (priority,status,message)) ** R ==>
 V293_owned_task_record t priority status message ** (V293_owned_task_records tasks ** R).
Proof. intros tasks t priority status message R Fresh. unfold V293_owned_task_records. apply V293_task_list_extract_fresh. exact Fresh. Qed.

Lemma V293_record_cells_to_raw : forall cells,
 V293_owned_record_cells cells ==> V293_rdy_raw_cells cells Aemp.
Proof.
 induction cells as [ | [[a tp] v] tail IH];intros s Owned;cbn [V293_owned_record_cells V293_rdy_raw_cells] in *.
 - exact Owned.
 - eapply astar_mono;[ |exact IH |exact Owned]. intros st HS.
   unfold V293_owned_record_cell in HS. apply astar_l_apure_elim in HS. exact (proj2 HS).
Qed.
Lemma V293_ready_record_to_raw : forall bt base p,
 p<13 -> (0<=base<=Int.max_unsigned)%Z ->
 V293_owned_task_record (bt,Int.repr base) (Int.repr(Z.of_nat p)) rdy Vnull ==>
 V293_rdy_raw_cells (V293_record_layout (bt,Int.repr base) p rdy Vnull 0) Aemp.
Proof.
 intros bt base p Range Bound s [q [pend Owned]].
 apply astar_l_apure_elim in Owned. destruct Owned as [[Qr [Priority Pr]] Cells].
 assert (q=p) by (eapply V293_priority_repr_injective;[exact Qr |exact Range |symmetry;exact Priority]).
 subst q. apply V293_record_cells_to_raw. exact Cells.
Qed.
Lemma V293_raw_to_ready_record : forall bt base p,
 p<13 -> V293_rdy_raw_cells (V293_record_layout (bt,Int.repr base) p rdy Vnull 0) Aemp ==>
 V293_owned_task_record (bt,Int.repr base) (Int.repr(Z.of_nat p)) rdy Vnull.
Proof.
 intros bt base p Range s Raw.
 assert (Types : Forall (fun cell => let '(_,tp,v):=cell in rule_type_val_match tp v=true)
   (V293_record_layout (bt,Int.repr base) p rdy Vnull 0)).
 { destruct (V293_tcb_init_byte_valid p Range) as (Vp&Vy&Vx&Vby&Vbx).
   unfold V293_record_layout. repeat constructor;first [assumption |reflexivity]. }
 apply (V293_raw_record_ownership _ _ Types) in Raw.
 assert (Cells : s |= V293_owned_record_cells (V293_record_layout (bt,Int.repr base) p rdy Vnull 0))
 by (clear -Raw;sep auto).
 exists p. exists 0. apply astar_l_apure_intro;[exact Cells |repeat split;try reflexivity;lia].
Qed.

(* Publication's three read-only TCB fields are deliberately absent here. *)
Definition V293_pub_link_cells bc bt base bh bg br bn bo obase (present : bool) p next prev head g r n back
 : list V293_record_cell :=
 [((bc,0%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base));
  ((bt,(base+20)%Z),Tcom_ptr 410%Z,next);
  ((bt,(base+24)%Z),Tcom_ptr 410%Z,prev);
  ((bh,0%Z),Tptr V293_tcb_type,head);
  ((bg,0%Z),Tint8,V293_byteval g);
  ((br,Z.of_nat(V293_prio_row p)),Tint8,V293_byteval r);
  ((bn,0%Z),Tint8,V293_byteval n)]++
 if present then [((bo,(obase+24)%Z),Tcom_ptr 410%Z,back)] else nil.
Definition V293_pub_record_rest bt base p : list V293_record_cell :=
 [((bt,(base+50)%Z),Tint8,V293_byteval p);
  ((bt,(base+51)%Z),Tint8,V293_byteval(V293_prio_bit p));
  ((bt,(base+32)%Z),Tptr Tvoid,Vnull);
  ((bt,(base+48)%Z),Tint8,V293_byteval 0)].

Theorem V293_OS_TCBInit_publication_preserves_records : forall tasks P ks ge le M ir aux O op R enabled si ci
 ptcb head group rows counter bc bt base bh bg br bn bo obase present p g r n oldnext oldprev oldback,
 get tasks (bt,Int.repr base)=None -> p<13 ->
 V293_pub_env ge le ptcb head group rows counter bc bh bg br bn ->
 (0<=base)%Z -> (base+54<=Int.max_unsigned)%Z ->
 (0<=obase)%Z -> (obase+24<=Int.max_unsigned)%Z -> g<256 -> r<256 -> n<255 ->
 (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_pub_link_cells bc bt base bh bg br bn bo obase present p oldnext oldprev
   (V293_pub_old_head present bo obase) g r n oldback)
 (V293_owned_task_records (set tasks (bt,Int.repr base) (Int.repr(Z.of_nat p),rdy,Vnull)) ** R) ->
 exists Mf,
 V293_local_steps P (curs(V293_TCB_publish ptcb head group rows counter),(kenil,ks))
  ((ge,le,M),ir,(enabled,si,ci))
  (curs(srete(econst32 Int.zero)),(kenil,ks)) ((ge,le,Mf),ir,(enabled,si,ci)) /\
 (ge,le,Mf,ir,aux,O,op) |=
 V293_owned_task_records (set tasks (bt,Int.repr base) (Int.repr(Z.of_nat p),rdy,Vnull)) **
 V293_rdy_raw_cells (V293_pub_link_cells bc bt base bh bg br bn bo obase present p
   (V293_pub_old_head present bo obase) Vnull (Vptr(bt,Int.repr base))
   (Nat.setbit g (V293_prio_row p)) (Nat.setbit r (V293_prio_bit p)) (S n) (Vptr(bt,Int.repr base))) R.
Proof.
 intros tasks P ks ge le M ir aux O op R enabled si ci ptcb head group rows counter
 bc bt base bh bg br bn bo obase present p g r n oldnext oldprev oldback
 Fresh Range Env Base Bound OldBase OldBound G Row Count Owned.
 pose proof (V293_prio_coordinates p Range) as [Y X].
 assert (New : (ge,le,M,ir,aux,O,op) |=
 V293_owned_task_record (bt,Int.repr base) (Int.repr(Z.of_nat p)) rdy Vnull **
 V293_rdy_raw_cells (V293_pub_link_cells bc bt base bh bg br bn bo obase present p oldnext oldprev
   (V293_pub_old_head present bo obase) g r n oldback) (V293_owned_task_records tasks ** R)).
 { apply V293_raw_cells_move_frame.
   eapply V293_raw_cells_mono;[apply V293_task_records_extract_fresh;exact Fresh |exact Owned]. }
 assert (Raw : (ge,le,M,ir,aux,O,op) |=
 V293_rdy_raw_cells (V293_record_layout (bt,Int.repr base) p rdy Vnull 0) Aemp **
 V293_rdy_raw_cells (V293_pub_link_cells bc bt base bh bg br bn bo obase present p oldnext oldprev
   (V293_pub_old_head present bo obase) g r n oldback) (V293_owned_task_records tasks ** R)).
 { eapply astar_mono;[apply V293_ready_record_to_raw;try assumption;lia |intros st HS;exact HS |exact New]. }
 assert (Entry : (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells
 (V293_pub_cells bc bt base bh bg br bn bo obase present (V293_prio_row p) (V293_prio_bit p)
 oldnext oldprev (V293_pub_old_head present bo obase) g r n oldback)
 (V293_rdy_raw_cells (V293_pub_record_rest bt base p) (V293_owned_task_records tasks ** R))).
 { unfold V293_pub_cells,V293_pub_link_cells,V293_pub_record_rest,V293_record_layout in *.
   cbn [fst snd] in Raw. rewrite Int.unsigned_repr in Raw by lia.
   cbn [V293_rdy_raw_cells app] in Raw |- *. destruct present; cbn [V293_rdy_raw_cells] in Raw |- *; clear -Raw; sep auto. }
 destruct (V293_OS_TCBInit_publication_execution P ks ge le M ir aux O op _ enabled si ci
 ptcb head group rows counter bc bt base bh bg br bn bo obase present
 (V293_prio_row p) (V293_prio_bit p) g r n oldnext oldprev oldback
 Env Base Bound OldBase OldBound Y X G Row Count Entry) as (Mf&Exec&Final).
 exists Mf. split;[exact Exec | ].
 assert (Back : (ge,le,Mf,ir,aux,O,op) |=
 V293_rdy_raw_cells (V293_record_layout (bt,Int.repr base) p rdy Vnull 0) Aemp **
 (V293_owned_task_records tasks **
 V293_rdy_raw_cells (V293_pub_link_cells bc bt base bh bg br bn bo obase present p
  (V293_pub_old_head present bo obase) Vnull (Vptr(bt,Int.repr base))
  (Nat.setbit g (V293_prio_row p)) (Nat.setbit r (V293_prio_bit p)) (S n) (Vptr(bt,Int.repr base))) R)).
 { unfold V293_pub_cells,V293_pub_link_cells,V293_pub_record_rest,V293_record_layout in *.
   cbn [fst snd]. rewrite Int.unsigned_repr by lia.
   cbn [V293_rdy_raw_cells app] in Final |- *. destruct present; cbn [V293_rdy_raw_cells] in Final |- *; clear -Final; sep auto. }
 apply (V293_task_records_insert tasks (bt,Int.repr base) (Int.repr(Z.of_nat p)) rdy Vnull _ Fresh).
 eapply astar_mono;[apply V293_raw_to_ready_record;exact Range |intros st HS;exact HS |exact Back].
Qed.
Print Assumptions V293_OS_TCBInit_publication_preserves_records.
