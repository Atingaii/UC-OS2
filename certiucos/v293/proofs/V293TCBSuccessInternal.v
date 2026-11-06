(* Nonempty OS_TCBInit: keep the exact declaration domain OUTSIDE the
   GoodFunAsrt CPU-port resource. No implementation is invented for either Hook. *)
Require Import CertiOS.tactics.hoareforward.init_spec.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBLinkedHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublishHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_tcb_internal_no_shadow_globals : forall le x,
 eq_dom_env le (getlenvdom V293_tcb_internal_declarations) ->
 (91<=x<=96)%Z -> get le x=None.
Proof.
 intros le x Domain Range. destruct (get le x) as [[b tp] | ] eqn:E;[ |reflexivity].
 exfalso. pose proof(proj2(Domain x tp)(ex_intro _ b E)) as Bad.
 cbn [V293_tcb_internal_declarations V293_TCBInit_parameters V293_TCBInit_locals
 revlcons getlenvdom] in Bad.
 repeat destruct Bad as [Bad|Bad];try contradiction;inversion Bad;lia.
Qed.
Lemma V293_tcb_internal_domain_frame : GoodFrm V293_tcb_internal_domain.
Proof. exact I. Qed.
Lemma V293_tcb_success_body_good : forall hi hc,
 GoodStmt'(V293_TCBInit_function_body hi hc).
Proof. intros. vm_compute. repeat split. Qed.

Definition V293_tcb_success_arguments p top bottom identity size ext options :=
 [V293_byteval p;top;bottom;identity;size;ext;options].
Definition V293_tcb_success_local_bindings bu bc bp bs bb bi bz be bo :=
 (Alvarenv 107%Z (Tint16) (bo,0%Z) ** (Alvarenv 106%Z (Tptr Tvoid) (be,0%Z) ** (Alvarenv 105%Z (Tint32) (bz,0%Z) ** (Alvarenv 104%Z (Tint16) (bi,0%Z) ** (Alvarenv 103%Z (Tptr Tint32) (bb,0%Z) ** (Alvarenv 102%Z (Tptr Tint32) (bs,0%Z) ** (Alvarenv 101%Z (Tint8) (bp,0%Z) ** (Alvarenv 108%Z (Tptr V293_tcb_type) (bc,0%Z) ** (Alvarenv 109%Z (Tint32) (bu,0%Z) ** Aemp))))))))).
Definition V293_tcb_success_local_cells bu bc bp bs bb bi bz be bo p top bottom identity size ext options pc cpu : list V293_record_cell :=
 [((bo,0%Z),(Tint16),(options));
 ((be,0%Z),(Tptr Tvoid),(ext));
 ((bz,0%Z),(Tint32),(size));
 ((bi,0%Z),(Tint16),(identity));
 ((bb,0%Z),(Tptr Tint32),(bottom));
 ((bs,0%Z),(Tptr Tint32),(top));
 ((bp,0%Z),(Tint8),(V293_byteval p));
 ((bc,0%Z),(Tptr V293_tcb_type),(pc));
 ((bu,0%Z),(Tint32),(cpu))].

Lemma V293_tcb_success_internal_unpack : forall p top bottom identity size ext options Q,
 V293_tcb_internal_pre_cells (V293_byteval p) top bottom identity size ext options ** Q ==>
 EX pc : val, EX cpu : val, EX bo : block, EX be : block, EX bz : block, EX bi : block, EX bb : block, EX bs : block, EX bp : block, EX bc : block, EX bu : block,
 V293_rdy_raw_cells
 (V293_tcb_success_local_cells bu bc bp bs bb bi bz be bo p top bottom identity size ext options pc cpu)
 (V293_tcb_success_local_bindings bu bc bp bs bb bi bz be bo ** Q).
Proof.
 intros. unfold V293_tcb_internal_pre_cells,V293_tcb_internal_locals,
 V293_tcb_success_local_cells,V293_tcb_success_local_bindings,
 Alvarmapsto,Alvarenv',Aptrmapsto in *.
 cbn [V293_rdy_raw_cells] in *. sep auto.
Qed.

Lemma V293_tcb_success_internal_pack : forall bu bc bp bs bb bi bz be bo p top bottom identity size ext options pc cpu,
 V293_rdy_raw_cells
 (V293_tcb_success_local_cells bu bc bp bs bb bi bz be bo p top bottom identity size ext options pc cpu)
 (V293_tcb_success_local_bindings bu bc bp bs bb bi bz be bo) ==>
 V293_tcb_internal_post_cells.
Proof.
 intros bu bc bp bs bb bi bz be bo p top bottom identity size ext options pc cpu s H.
 unfold V293_tcb_success_local_cells,V293_tcb_success_local_bindings in H.
 cbn [V293_rdy_raw_cells] in H.
 assert (Grouped : s |= ((Alvarenv 107%Z (Tint16) (bo,0%Z) ** Amapsto (bo,0%Z) (Tint16) true (options)) ** ((Alvarenv 106%Z (Tptr Tvoid) (be,0%Z) ** Amapsto (be,0%Z) (Tptr Tvoid) true (ext)) ** ((Alvarenv 105%Z (Tint32) (bz,0%Z) ** Amapsto (bz,0%Z) (Tint32) true (size)) ** ((Alvarenv 104%Z (Tint16) (bi,0%Z) ** Amapsto (bi,0%Z) (Tint16) true (identity)) ** ((Alvarenv 103%Z (Tptr Tint32) (bb,0%Z) ** Amapsto (bb,0%Z) (Tptr Tint32) true (bottom)) ** ((Alvarenv 102%Z (Tptr Tint32) (bs,0%Z) ** Amapsto (bs,0%Z) (Tptr Tint32) true (top)) ** ((Alvarenv 101%Z (Tint8) (bp,0%Z) ** Amapsto (bp,0%Z) (Tint8) true (V293_byteval p)) ** ((Alvarenv 108%Z (Tptr V293_tcb_type) (bc,0%Z) ** Amapsto (bc,0%Z) (Tptr V293_tcb_type) true (pc)) ** ((Alvarenv 109%Z (Tint32) (bu,0%Z) ** Amapsto (bu,0%Z) (Tint32) true (cpu)) ** Aemp)))))))))).
 { clear -H. sep auto. }
 unfold V293_tcb_internal_post_cells,V293_tcb_internal_locals.
 eapply astar_mono;[apply V293_tcb_internal_local_return| |exact Grouped].
 apply astar_mono;[apply V293_tcb_internal_local_return| ].
 apply astar_mono;[apply V293_tcb_internal_local_return| ].
 apply astar_mono;[apply V293_tcb_internal_local_return| ].
 apply astar_mono;[apply V293_tcb_internal_local_return| ].
 apply astar_mono;[apply V293_tcb_internal_local_return| ].
 apply astar_mono;[apply V293_tcb_internal_local_return| ].
 apply astar_mono;[apply V293_tcb_internal_local_return| ].
 apply astar_mono;[apply V293_tcb_internal_local_return| ].
 intros st HS;exact HS.
Qed.

Definition V293_tcb_success_global_bindings table bg bh bgrp br bn :=
 Agvarenv 91%Z (Tptr V293_tcb_type) (bg,0%Z) **
 (Agvarenv 92%Z (Tarray (Tptr V293_tcb_type) 13) (table,0%Z) **
 (Agvarenv 93%Z (Tptr V293_tcb_type) (bh,0%Z) **
 (Agvarenv 94%Z Tint8 (bgrp,0%Z) **
 (Agvarenv 95%Z (Tarray Tint8 2) (br,0%Z) **
 (Agvarenv 96%Z Tint8 (bn,0%Z) ** Aemp))))).

Lemma V293_tcb_internal_empty_star : forall A B s,
 s |= Aemp -> s |= A -> s |= B -> s |= A ** B.
Proof. intros A B s Emp HA HB. destruct_s s. simpl in *. join auto. Qed.

Lemma V293_tcb_success_bindings_from_domain : forall table bg bu bc bp bs bb bi bz be bo bh bgrp br bn,
 (V293_tcb_success_local_bindings bu bc bp bs bb bi bz be bo **
 V293_tcb_success_global_bindings table bg bh bgrp br bn) ** V293_tcb_internal_domain ==>
 V293_hook_bindings table bg bu bc bp bs bb bi bz be bo bh bgrp br bn ** V293_tcb_internal_domain.
Proof.
 intros table bg bu bc bp bs bb bi bz be bo bh bgrp br bn s H.
 unfold V293_tcb_internal_domain in *.
 apply astar_comm in H. apply astar_l_adomlenv_elim in H. destruct H as [Domain H].
 apply astar_comm. apply astar_l_adomlenv_intro;[ |exact Domain].
 assert(N : forall x, (91<=x<=96)%Z -> ~ indom (getlenv s) x).
 { intros x Range [v E]. rewrite(V293_tcb_internal_no_shadow_globals _ x Domain Range) in E. discriminate. }
 unfold V293_tcb_success_local_bindings,V293_tcb_success_global_bindings in H.
 unfold V293_hook_bindings,V293_tcb_success_bindings,V293_tcb_success_extra,
 V293_tcb_fields_bindings,V293_tcb_table_binding,V293_pub_bindings.
 sep auto.
 repeat (apply V293_tcb_internal_empty_star;[exact H| | ]).
 all: repeat match goal with |- _ |= _ //\\ _ => split end.
 all: first [apply alvarenv_intro;[exact H|assumption] |
        apply agvarenv_intro;[exact H|assumption] |
        apply anotinlenv_intro;[exact H|apply N;lia]].
Qed.

(* Caller-visible byte resources; neither list contains any local address. *)
Definition V293_tcb_success_pre_owned table slot bg bt base old next
 bh bgrp br bn oldblock oldbase present p oldprev g row n oldback :=
 ((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,slot)::
 (V293_tcb_init_old_fields bt base old ++
 V293_tcb_prefix_links bg bt base (Vptr(bt,Int.repr base)) next ++
 V293_link_extra bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback).
Definition V293_tcb_success_post_owned table bg bt base p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present g row n : list V293_record_cell :=
 tl(V293_pub_cells 1%positive bt base bh bgrp br bn oldblock oldbase present
  (V293_prio_row p)(V293_prio_bit p)(V293_pub_old_head present oldblock oldbase)
  Vnull (Vptr(bt,Int.repr base)) (Nat.setbit g (V293_prio_row p))
  (Nat.setbit row (V293_prio_bit p))(S n)(Vptr(bt,Int.repr base))) ++
 [((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base));
  ((bt,(base+0)%Z),Tptr Tint32,top);
  ((bt,(base+50)%Z),Tint8,V293_byteval p);
  ((bt,(base+48)%Z),Tint8,Vint32 Int.zero);
  ((bt,(base+49)%Z),Tint8,Vint32 Int.zero);
  ((bt,(base+44)%Z),Tint32,Vint32 Int.zero);
  ((bt,(base+4)%Z),Tptr Tvoid,ext);
  ((bt,(base+12)%Z),Tint32,size);
  ((bt,(base+8)%Z),Tptr Tint32,bottom);
  ((bt,(base+16)%Z),Tint16,options);
  ((bt,(base+18)%Z),Tint16,identity);
  ((bt,(base+55)%Z),Tint8,Vint32 Int.zero);
  ((bt,(base+51)%Z),Tint8,V293_byteval(V293_prio_bit p));
  ((bt,(base+28)%Z),Tcom_ptr 411%Z,Vnull);
  ((bt,(base+36)%Z),Tcom_ptr 412%Z,Vnull);
  ((bt,(base+32)%Z),Tptr Tvoid,Vnull);
  ((bg,0%Z),Tptr V293_tcb_type,next)].
Definition V293_tcb_success_external table bg bh bgrp br bn cells R aop isr is cs :=
 V293_hook_resource cells (V293_tcb_success_global_bindings table bg bh bgrp br bn ** R) aop isr is cs.
Lemma V293_tcb_success_external_good : forall table bg bh bgrp br bn cells R aop isr is cs,
 GoodFunAsrt R -> GoodFunAsrt(V293_tcb_success_external table bg bh bgrp br bn cells R aop isr is cs).
Proof.
 intros. apply V293_hook_resource_good.
 cbn [V293_tcb_success_global_bindings GoodFunAsrt]. tauto.
Qed.

Lemma V293_tcb_success_entry_layout : forall table slot bg bu bc bp bs bb bi bz be bo bt base old
 p top bottom identity size ext options pc cpu next bh bgrp br bn oldblock oldbase present oldprev g row n oldback,
 Permutation
 (V293_tcb_success_local_cells bu bc bp bs bb bi bz be bo p top bottom identity size ext options pc cpu ++
 V293_tcb_success_pre_owned table slot bg bt base old next bh bgrp br bn oldblock oldbase present p oldprev g row n oldback)
 ((((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,slot)::
 V293_tcb_success_cells bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_old_fields bt base old) pc cpu (Vptr(bt,Int.repr base)) next) ++
 V293_link_extra bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback).
Proof.
 intros. destruct present;unfold V293_tcb_success_local_cells,V293_tcb_success_pre_owned,
 V293_tcb_success_cells,V293_tcb_init_old_fields,V293_tcb_prefix_inputs,V293_tcb_init_input_cells,
 V293_tcb_prefix_links,V293_link_extra;cbn [app tl];V293_link_permute.
Qed.
Lemma V293_tcb_success_exit_layout : forall table bg bu bc bp bs bb bi bz be bo bt base p
 top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n,
 Permutation
 (V293_pub_cells bc bt base bh bgrp br bn oldblock oldbase present (V293_prio_row p)(V293_prio_bit p)
  (V293_pub_old_head present oldblock oldbase) Vnull (Vptr(bt,Int.repr base))
  (Nat.setbit g (V293_prio_row p))(Nat.setbit row (V293_prio_bit p))(S n)(Vptr(bt,Int.repr base)) ++
 V293_link_residual table bg bu bp bs bb bi bz be bo bt base p top bottom identity size ext options next)
 (V293_tcb_success_post_owned table bg bt base p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present g row n ++
 V293_tcb_success_local_cells bu bc bp bs bb bi bz be bo p top bottom identity size ext options
 (Vptr(bt,Int.repr base))(Vint32 Int.zero)).
Proof.
 intros. destruct present;unfold V293_tcb_success_post_owned,V293_tcb_success_local_cells,
 V293_pub_cells,V293_link_residual;cbn [app tl];V293_link_permute.
Qed.

Lemma V293_tcb_success_flatten : forall xs ys A B D R aop isr is cs,
 V293_rdy_raw_cells xs (A ** (V293_hook_resource ys (B ** R) aop isr is cs ** D)) ==>
 <||aop||> ** V293_rdy_raw_cells (xs++ys) (OS[isr,false,is,cs] ** (((A ** B) ** D) ** R)).
Proof.
 intros xs ys A B D R aop isr is cs s H. unfold V293_hook_resource in H.
 assert(K:s |= V293_rdy_raw_cells xs
 (V293_rdy_raw_cells ys (<||aop||> ** (OS[isr,false,is,cs] ** (((A ** B) ** D) ** R))))).
 { eapply V293_raw_cells_mono;[ |exact H]. intros st HS.
   assert(K1:st |= (A ** (<||aop||> ** D)) ** V293_rdy_raw_cells ys (OS[isr,false,is,cs] ** (B ** R))).
   { clear -HS. sep auto. }
   apply V293_raw_cells_unmove_frame in K1.
   eapply V293_raw_cells_mono;[ |exact K1]. intros st1 H1. clear -H1. sep auto. }
 rewrite <- V293_raw_cells_append in K. apply V293_raw_cells_move_frame in K.
 clear -K. sep auto.
Qed.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.

Lemma V293_tcb_success_internal_entry : forall table slot bg bu bc bp bs bb bi bz be bo bt base old
 p top bottom identity size ext options pc cpu next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs,
 V293_rdy_raw_cells
 (V293_tcb_success_local_cells bu bc bp bs bb bi bz be bo p top bottom identity size ext options pc cpu)
 (V293_tcb_success_local_bindings bu bc bp bs bb bi bz be bo **
 (V293_tcb_success_external table bg bh bgrp br bn
 (V293_tcb_success_pre_owned table slot bg bt base old next bh bgrp br bn oldblock oldbase present p oldprev g row n oldback)
 R aop isr is cs ** V293_tcb_internal_domain)) ==>
 V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_old_fields bt base old) pc cpu (Vptr(bt,Int.repr base)) next
 (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs **
 V293_tcb_internal_domain.
Proof.
 intros table slot bg bu bc bp bs bb bi bz be bo bt base old p top bottom identity size ext options pc cpu next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs s H.
 unfold V293_tcb_success_external in H. apply V293_tcb_success_flatten in H.
 eapply astar_mono in H;[ |intros st HS;exact HS| ].
 2: { eapply V293_raw_cells_mono. apply astar_mono;[intros st HS;exact HS| ].
      apply astar_mono;[apply V293_tcb_success_bindings_from_domain|intros st HS;exact HS]. }
 eapply astar_mono in H;[ |intros st HS;exact HS| ].
 2: { apply V293_link_cells_permutation. apply V293_tcb_success_entry_layout. }
 unfold V293_tcb_table_state,V293_link_frame,V293_hook_bindings.
 assert(K:s |= <||aop||> ** V293_rdy_raw_cells
 ((((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,slot)::
 V293_tcb_success_cells bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_old_fields bt base old) pc cpu (Vptr(bt,Int.repr base)) next) ++
 V293_link_extra bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback)
 (V293_tcb_internal_domain ** (OS[isr,false,is,cs] **
 ((V293_tcb_success_bindings bg bu bc bp bs bb bi bz be bo ** V293_tcb_table_binding table) **
 (V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z bc bh bgrp br bn ** R))))).
 { eapply astar_mono;[intros st HS;exact HS| |exact H].
   apply V293_raw_cells_mono. intros st HS. unfold V293_hook_bindings in HS. clear -HS. sep auto. }
 clear H. eapply astar_mono in K;[ |intros st HS;exact HS|apply V293_raw_cells_move_frame].
 rewrite V293_raw_cells_append in K.
 eapply astar_mono in K.
 2: { intros st HS;exact HS. }
 2: { apply astar_mono;[intros st HS;exact HS| ]. apply V293_raw_cells_mono. apply V293_raw_cells_move_frame. }
 clear -K. sep auto.
 eapply V293_raw_cells_mono;[ |exact K].
 apply astar_mono;[intros st HS;exact HS| ].
 intros st HS. apply V293_raw_cells_move_frame in HS. clear -HS. sep auto.
Qed.

Lemma V293_tcb_success_return_bindings : forall table bg bu bc bp bs bb bi bz be bo bh bgrp br bn,
 V293_hook_bindings table bg bu bc bp bs bb bi bz be bo bh bgrp br bn ==>
 V293_tcb_success_local_bindings bu bc bp bs bb bi bz be bo **
 V293_tcb_success_global_bindings table bg bh bgrp br bn.
Proof.
 intros table bg bu bc bp bs bb bi bz be bo bh bgrp br bn s H.
 unfold V293_hook_bindings,V293_tcb_success_bindings,V293_tcb_success_extra,
 V293_tcb_fields_bindings,V293_tcb_table_binding,V293_pub_bindings in H.
 unfold V293_tcb_success_local_bindings,V293_tcb_success_global_bindings.
 sep auto. all: destruct_s s; simpl in *; join auto.
Qed.

Lemma V293_tcb_success_internal_exit : forall table bg bu bc bp bs bb bi bz be bo bt base p
 top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs result,
 V293_link_return_post table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present g row n R aop isr is cs result ==>
 V293_tcb_internal_post_cells ** ([|result=Some(Vint32 Int.zero)|] **
 V293_tcb_success_external table bg bh bgrp br bn
 (V293_tcb_success_post_owned table bg bt base p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present g row n) R aop isr is cs).
Proof.
 intros table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs result s H.
 unfold V293_link_return_post,V293_pub_return_post in H.
 apply astar_l_apure_elim in H. destruct H as [Code H].
 unfold V293_pub_hstate,V293_link_residual_frame in H.
 set(xs:=V293_pub_cells bc bt base bh bgrp br bn oldblock oldbase present
 (V293_prio_row p)(V293_prio_bit p)(V293_pub_old_head present oldblock oldbase)
 Vnull(Vptr(bt,Int.repr base))(Nat.setbit g(V293_prio_row p))(Nat.setbit row(V293_prio_bit p))
 (S n)(Vptr(bt,Int.repr base))) in *.
 set(ys:=V293_link_residual table bg bu bp bs bb bi bz be bo bt base p top bottom identity size ext options next) in *.
 assert(Flat:s |= <||aop||> ** V293_rdy_raw_cells (xs++ys)
 (OS[isr,false,is,cs] ** (V293_hook_bindings table bg bu bc bp bs bb bi bz be bo bh bgrp br bn ** R))).
 { eapply astar_mono;[intros st HS;exact HS| |exact H].
   intros st HS.
   assert(K:st |= V293_rdy_raw_cells(xs++ys)
    ((OS[isr,false,is,cs] ** V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z bc bh bgrp br bn) **
    (V293_tcb_success_bindings bg bu bc bp bs bb bi bz be bo ** (V293_tcb_table_binding table ** R)))).
   { apply V293_link_exchange. eapply V293_raw_cells_mono;[ |exact HS]. intros st1 H1. clear -H1. sep auto. }
   eapply V293_raw_cells_mono;[ |exact K]. intros st1 H1.
   unfold V293_hook_bindings. clear -H1. sep auto. }
 eapply astar_mono in Flat;[ |intros st HS;exact HS| ].
 2: { apply V293_link_cells_permutation. apply V293_tcb_success_exit_layout. }
 eapply astar_mono in Flat;[ |intros st HS;exact HS| ].
 2: { apply V293_raw_cells_mono. apply astar_mono;[intros st HS;exact HS| ].
      apply astar_mono;[apply V293_tcb_success_return_bindings|intros st HS;exact HS]. }
 set(owned:=V293_tcb_success_post_owned table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n) in *.
 set(locals:=V293_tcb_success_local_cells bu bc bp bs bb bi bz be bo p top bottom identity size ext options (Vptr(bt,Int.repr base))(Vint32 Int.zero)) in *.
 assert(Factored:s |= <||aop||> **
 (V293_rdy_raw_cells owned (OS[isr,false,is,cs] **
  (V293_tcb_success_global_bindings table bg bh bgrp br bn ** R)) **
 V293_rdy_raw_cells locals (V293_tcb_success_local_bindings bu bc bp bs bb bi bz be bo))).
 { eapply astar_mono;[intros st HS;exact HS| |exact Flat]. intros st HS.
   apply V293_hook_cells_factor.
   eapply V293_raw_cells_mono;[ |exact HS]. intros st1 H1. clear -H1. sep auto. }
 eapply astar_mono in Factored;[ |intros st HS;exact HS| ].
 2: { apply astar_mono;[intros st HS;exact HS| ]. unfold locals. apply V293_tcb_success_internal_pack. }
 unfold V293_tcb_success_external,V293_hook_resource.
 clear -Factored Code. sep auto.
Qed.

Theorem V293_OS_TCBInit_success_internal_resources : forall Spec sd li I tid hi hc slot old table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs,
 GoodI I sd li ->
 p<13 -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 (0<=oldbase)%Z -> (oldbase+24<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 rule_type_val_match (Tptr V293_tcb_type) next=true ->
 g<256 -> row<256 -> n<255 -> GoodFrm R -> (R ==> CurLINV li tid) ->
 forall (Hfun:GoodFunAsrt R),
 Spec hi=Some(
 V293_hook_fpre (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table (slot) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) (V293_hook_resource_good (V293_hook_owned_cells table (slot) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs Hfun),
 V293_hook_fpost (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table (slot) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) (V293_hook_resource_good (V293_hook_owned_cells table (slot) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs Hfun), (Tvoid,[Tptr V293_tcb_type])) ->
 Spec hc=Some(
 V293_hook_fpre (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table (Vptr(bt,Int.repr base)) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) (V293_hook_resource_good (V293_hook_owned_cells table (Vptr(bt,Int.repr base)) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs Hfun),
 V293_hook_fpost (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table (Vptr(bt,Int.repr base)) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) (V293_hook_resource_good (V293_hook_owned_cells table (Vptr(bt,Int.repr base)) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs Hfun), (Tvoid,[Tptr V293_tcb_type])) ->
 InfRules Spec sd li I (fun result => V293_tcb_internal_post_cells ** ([|result=Some(Vint32 Int.zero)|] **
 V293_tcb_success_external table bg bh bgrp br bn
 (V293_tcb_success_post_owned table bg bt base p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present g row n) R aop isr is cs) ** V293_tcb_internal_domain) Afalse
 (V293_tcb_internal_pre_cells (V293_byteval p) top bottom identity size ext options **
 V293_tcb_success_external table bg bh bgrp br bn
 (V293_tcb_success_pre_owned table slot bg bt base old next bh bgrp br bn oldblock oldbase present p oldprev g row n oldback)
 R aop isr is cs ** V293_tcb_internal_domain) (V293_TCBInit_function_body hi hc) Afalse tid.
Proof.
 intros Spec sd li I tid hi hc slot old table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs
 GI Range Base Bound OldBase OldBound Valid Next Group Row Count Frame HR Hfun InitLookup CreateLookup.
 eapply conseq_rule.
 - apply V293_tcb_success_internal_unpack.
 - intros s H;exact H.
 - apply ex_intro_rule. intro pc. apply ex_intro_rule. intro cpu.
   apply ex_intro_rule. intro bo. apply ex_intro_rule. intro be.
   apply ex_intro_rule. intro bz. apply ex_intro_rule. intro bi.
   apply ex_intro_rule. intro bb. apply ex_intro_rule. intro bs.
   apply ex_intro_rule. intro bp. apply ex_intro_rule. intro bc.
   apply ex_intro_rule. intro bu.
   eapply conseq_rule with (q:=Afalse ** V293_tcb_internal_domain);[apply V293_tcb_success_internal_entry| | ].
   + intros s H. destruct_s s. simpl in *. join auto.
   + eapply r_conseq_rule with
      (r:=fun result=>V293_link_return_post table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs result ** V293_tcb_internal_domain)
      (ri:=Afalse ** V293_tcb_internal_domain).
     * intros result s HS.
       eapply astar_mono in HS;[ |apply V293_tcb_success_internal_exit|intros st H;exact H].
       clear -HS. sep auto.
     * intros s H. destruct_s s. simpl in *. join auto.
     * apply frame_rule_all.
       -- exact GI.
       -- apply V293_tcb_success_body_good.
       -- apply V293_tcb_internal_domain_frame.
       -- unfold V293_tcb_table_state. apply V293_star_CurLINV_r.
          apply V293_raw_cells_CurLINV. do 3 apply V293_star_CurLINV_r.
          apply V293_link_frame_linv. exact HR.
       -- eapply V293_OS_TCBInit_hook_calls_body_hoare;eassumption.
Qed.

Definition V293_tcb_success_fpre table slot bg bt base old p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs (good:GoodFunAsrt R) : fpre :=
 fun vl lg tid => @mkfunasrt
 ([|vl=V293_tcb_success_arguments p top bottom identity size ext options|] ** V293_tcb_success_external table bg bh bgrp br bn (V293_tcb_success_pre_owned table slot bg bt base old next bh bgrp br bn oldblock oldbase present p oldprev g row n oldback) R aop isr is cs)
 (conj I (V293_tcb_success_external_good table bg bh bgrp br bn (V293_tcb_success_pre_owned table slot bg bt base old next bh bgrp br bn oldblock oldbase present p oldprev g row n oldback) R aop isr is cs good)).
Definition V293_tcb_success_fpost table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs (good:GoodFunAsrt R) : fpost :=
 fun vl result lg tid => @mkfunasrt
 ([|result=Some(Vint32 Int.zero)|] ** V293_tcb_success_external table bg bh bgrp br bn (V293_tcb_success_post_owned table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n) R aop isr is cs)
 (conj I (V293_tcb_success_external_good table bg bh bgrp br bn (V293_tcb_success_post_owned table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n) R aop isr is cs good)).
Theorem V293_OS_TCBInit_success_internal_contract : forall P f Spec sd li I tid hi hc slot old table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs vl lg pre post,
 GoodI I sd li ->
 p<13 -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 (0<=oldbase)%Z -> (oldbase+24<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 rule_type_val_match (Tptr V293_tcb_type) next=true ->
 g<256 -> row<256 -> n<255 -> GoodFrm R -> (R ==> CurLINV li tid) ->
 forall (Hfun:GoodFunAsrt R),
 Spec hi=Some(
 V293_hook_fpre (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table (slot) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) (V293_hook_resource_good (V293_hook_owned_cells table (slot) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs Hfun),
 V293_hook_fpost (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table (slot) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) (V293_hook_resource_good (V293_hook_owned_cells table (slot) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs Hfun), (Tvoid,[Tptr V293_tcb_type])) ->
 Spec hc=Some(
 V293_hook_fpre (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table (Vptr(bt,Int.repr base)) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) (V293_hook_resource_good (V293_hook_owned_cells table (Vptr(bt,Int.repr base)) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs Hfun),
 V293_hook_fpost (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table (Vptr(bt,Int.repr base)) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) (V293_hook_resource_good (V293_hook_owned_cells table (Vptr(bt,Int.repr base)) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs Hfun), (Tvoid,[Tptr V293_tcb_type])) ->
 P f=Some(V293_TCBInit_function hi hc) ->
 Some pre=BuildPreI P f vl lg (V293_tcb_success_fpre table slot bg bt base old p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs Hfun) tid ->
 Some post=BuildRetI P f vl lg (V293_tcb_success_fpost table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs Hfun) tid ->
 InfRules Spec sd li I post Afalse pre (V293_TCBInit_function_body hi hc) Afalse tid.
Proof.
 intros P f Spec sd li I tid hi hc slot old table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs vl lg pre post
 GI Range Base Bound OldBase OldBound Valid Next Group Row Count Frame HR Hfun InitLookup CreateLookup Code Pre Post.
 unfold BuildPreI in Pre. rewrite Code in Pre.
 cbn [V293_TCBInit_function] in Pre.
 destruct (dl_vl_match V293_TCBInit_parameters (rev vl)) eqn:Typed;[ |discriminate].
 pose proof(dl_vl_match_dv_same_length _ _ Typed) as Length.
 rewrite rev_length in Length. cbn [V293_TCBInit_parameters decllen] in Length.
 destruct vl as [ |v7 vl];[discriminate Length| ].
 destruct vl as [ |v6 vl];[discriminate Length| ].
 destruct vl as [ |v5 vl];[discriminate Length| ].
 destruct vl as [ |v4 vl];[discriminate Length| ].
 destruct vl as [ |v3 vl];[discriminate Length| ].
 destruct vl as [ |v2 vl];[discriminate Length| ].
 destruct vl as [ |v1 vl];[discriminate Length| ].
 destruct vl;[ |discriminate Length].
 fold V293_tcb_internal_declarations in Pre.
 rewrite V293_tcb_internal_buildp in Pre.
 change (Some pre=Some(V293_tcb_internal_pre_cells v1 v2 v3 v4 v5 v6 v7 **
 ([|[v1;v2;v3;v4;v5;v6;v7]=V293_tcb_success_arguments p top bottom identity size ext options|] **
 V293_tcb_success_external table bg bh bgrp br bn (V293_tcb_success_pre_owned table slot bg bt base old next bh bgrp br bn oldblock oldbase present p oldprev g row n oldback) R aop isr is cs) ** V293_tcb_internal_domain)) in Pre.
 inversion Pre;subst pre.
 unfold BuildRetI in Post. rewrite Code in Post.
 change (Some post=Some(fun result=>V293_tcb_internal_post_cells **
 ([|result=Some(Vint32 Int.zero)|] ** V293_tcb_success_external table bg bh bgrp br bn (V293_tcb_success_post_owned table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n) R aop isr is cs) ** V293_tcb_internal_domain)) in Post.
 inversion Post;subst post.
 eapply conseq_rule with (p:=
 V293_tcb_internal_pre_cells (V293_byteval p) top bottom identity size ext options **
 V293_tcb_success_external table bg bh bgrp br bn
 (V293_tcb_success_pre_owned table slot bg bt base old next bh bgrp br bn oldblock oldbase present p oldprev g row n oldback)
 R aop isr is cs ** V293_tcb_internal_domain).
 - intros s H.
   assert(K:s |= [|[v1;v2;v3;v4;v5;v6;v7]=V293_tcb_success_arguments p top bottom identity size ext options|] **
    (V293_tcb_internal_pre_cells v1 v2 v3 v4 v5 v6 v7 ** V293_tcb_success_external table bg bh bgrp br bn (V293_tcb_success_pre_owned table slot bg bt base old next bh bgrp br bn oldblock oldbase present p oldprev g row n oldback) R aop isr is cs ** V293_tcb_internal_domain)).
   { clear -H. sep auto. }
   apply astar_l_apure_elim in K. destruct K as [Args K].
   unfold V293_tcb_success_arguments in Args. inversion Args;subst.
   exact K.
 - intros s H;exact H.
 - eapply V293_OS_TCBInit_success_internal_resources;eassumption.
Qed.


Lemma V293_tcb_internal_local_named : forall x tp b v,
 Alvarenv x tp (b,0%Z) ** Amapsto (b,0%Z) tp true v ==> LV x @ tp |-> v.
Proof. intros x tp b v s H. unfold Alvarmapsto,Alvarenv',Aptrmapsto. exists b. exact H. Qed.
Lemma V293_tcb_success_internal_prepack : forall bu bc bp bs bb bi bz be bo p top bottom identity size ext options pc cpu,
 V293_rdy_raw_cells
 (V293_tcb_success_local_cells bu bc bp bs bb bi bz be bo p top bottom identity size ext options pc cpu)
 (V293_tcb_success_local_bindings bu bc bp bs bb bi bz be bo) ==>
 V293_tcb_internal_pre_cells (V293_byteval p) top bottom identity size ext options.
Proof.
 intros bu bc bp bs bb bi bz be bo p top bottom identity size ext options pc cpu s H.
 unfold V293_tcb_success_local_cells,V293_tcb_success_local_bindings in H.
 cbn [V293_rdy_raw_cells] in H.
 assert (Grouped : s |= ((Alvarenv 107%Z (Tint16) (bo,0%Z) ** Amapsto (bo,0%Z) (Tint16) true (options)) ** ((Alvarenv 106%Z (Tptr Tvoid) (be,0%Z) ** Amapsto (be,0%Z) (Tptr Tvoid) true (ext)) ** ((Alvarenv 105%Z (Tint32) (bz,0%Z) ** Amapsto (bz,0%Z) (Tint32) true (size)) ** ((Alvarenv 104%Z (Tint16) (bi,0%Z) ** Amapsto (bi,0%Z) (Tint16) true (identity)) ** ((Alvarenv 103%Z (Tptr Tint32) (bb,0%Z) ** Amapsto (bb,0%Z) (Tptr Tint32) true (bottom)) ** ((Alvarenv 102%Z (Tptr Tint32) (bs,0%Z) ** Amapsto (bs,0%Z) (Tptr Tint32) true (top)) ** ((Alvarenv 101%Z (Tint8) (bp,0%Z) ** Amapsto (bp,0%Z) (Tint8) true (V293_byteval p)) ** ((Alvarenv 108%Z (Tptr V293_tcb_type) (bc,0%Z) ** Amapsto (bc,0%Z) (Tptr V293_tcb_type) true (pc)) ** ((Alvarenv 109%Z (Tint32) (bu,0%Z) ** Amapsto (bu,0%Z) (Tint32) true (cpu)) ** Aemp)))))))))).
 { clear -H. sep auto. }
 unfold V293_tcb_internal_pre_cells,V293_tcb_internal_locals.
 eapply astar_mono;[apply V293_tcb_internal_local_named| |exact Grouped].
 apply astar_mono;[apply V293_tcb_internal_local_named| ].
 apply astar_mono;[apply V293_tcb_internal_local_named| ].
 apply astar_mono;[apply V293_tcb_internal_local_named| ].
 apply astar_mono;[apply V293_tcb_internal_local_named| ].
 apply astar_mono;[apply V293_tcb_internal_local_named| ].
 apply astar_mono;[apply V293_tcb_internal_local_named| ].
 apply astar_mono;[apply V293_tcb_internal_local_return| ].
 apply astar_mono;[apply V293_tcb_internal_local_return| ].
 intros st HS;exact HS.
Qed.
