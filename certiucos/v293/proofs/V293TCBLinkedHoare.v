(* Whole nonempty body: publication discharged, TWO real CPU Hook contracts remain. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.soundness.
Require CertiOS.framework.proof.simulation.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293TCBPublishHoare.
Require Import Coq.Sorting.Permutation.

Lemma V293_link_cells_permutation : forall xs ys R,
 Permutation xs ys -> V293_rdy_raw_cells xs R ==> V293_rdy_raw_cells ys R.
Proof.
 intros xs ys R H. induction H;intros s HS;cbn [V293_rdy_raw_cells] in *.
 - exact HS.
 - destruct x as [[a tp] v]. cbn [V293_rdy_raw_cells] in *.
   eapply astar_mono;[intros st Hst;exact Hst|exact IHPermutation|exact HS].
 - destruct x as [[a tp] v],y as [[b tq] w]. cbn [V293_rdy_raw_cells] in *.
   clear -HS. sep auto.
 - apply IHPermutation2. apply IHPermutation1. exact HS.
Qed.

(* Deterministic list permutation: extract precisely the desired cell. *)
Ltac V293_link_permute :=
 lazymatch goal with
 | |- Permutation (@nil _) (@nil _) => constructor
 | |- Permutation ?xs (?x::?ys) =>
   let rec extract before rest :=
    lazymatch rest with
    | x::?tail =>
      eapply Permutation_trans with (l':=x::(before++tail));
      [apply Permutation_sym;apply Permutation_middle|apply perm_skip;cbn [app];V293_link_permute]
    | ?h::?tail => extract (before++[h]) tail
    end
   in extract (@nil V293_record_cell) xs
 end.

Definition V293_link_extra bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback :=
 [((bt,(base+24)%Z),Tcom_ptr 410%Z,oldprev);
  ((bh,0%Z),Tptr V293_tcb_type,V293_pub_old_head present oldblock oldbase);
  ((bgrp,0%Z),Tint8,V293_byteval g);
  ((br,Z.of_nat(V293_prio_row p)),Tint8,V293_byteval row);
  ((bn,0%Z),Tint8,V293_byteval n)] ++
 if present then [((oldblock,(oldbase+24)%Z),Tcom_ptr 410%Z,oldback)] else [].
Definition V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R :=
 V293_rdy_raw_cells
 (V293_link_extra bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback)
 (V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z bc bh bgrp br bn ** R).
Definition V293_link_residual table bg bu bp bs bb bi bz be bo bt base p top bottom identity size ext options next :=
 [((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base));
  ((bu,0%Z),Tint32,Vint32 Int.zero);
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
  ((bp,0%Z),Tint8,V293_byteval p);
  ((bs,0%Z),Tptr Tint32,top);
  ((bb,0%Z),Tptr Tint32,bottom);
  ((bi,0%Z),Tint16,identity);
  ((bz,0%Z),Tint32,size);
  ((be,0%Z),Tptr Tvoid,ext);
  ((bo,0%Z),Tint16,options);
  ((bg,0%Z),Tptr V293_tcb_type,next)].
Definition V293_link_residual_frame table bg bu bc bp bs bb bi bz be bo bt base
 p top bottom identity size ext options next R :=
 V293_rdy_raw_cells
 (V293_link_residual table bg bu bp bs bb bi bz be bo bt base p top bottom identity size ext options next)
 (V293_tcb_success_bindings bg bu bc bp bs bb bi bz be bo ** (V293_tcb_table_binding table ** R)).
Lemma V293_link_frame_good : forall bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R,
 GoodFrm R -> GoodFrm(V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R).
Proof. intros. apply V293_raw_cells_good_frame. cbn [GoodFrm]. split;[apply V293_pub_bindings_good|assumption]. Qed.
Lemma V293_link_frame_linv : forall bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R li tid,
 (R ==> CurLINV li tid) -> V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R ==> CurLINV li tid.
Proof. intros bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R li tid HR. unfold V293_link_frame. apply V293_raw_cells_CurLINV. apply V293_star_CurLINV_r. exact HR. Qed.
Lemma V293_link_residual_good : forall table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next R,
 GoodFrm R -> GoodFrm(V293_link_residual_frame table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next R).
Proof.
 intros. apply V293_raw_cells_good_frame. cbn [GoodFrm V293_tcb_success_bindings V293_tcb_success_extra V293_tcb_fields_bindings V293_tcb_table_binding]. tauto.
Qed.
Lemma V293_link_residual_linv : forall table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next R li tid,
 (R ==> CurLINV li tid) -> V293_link_residual_frame table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next R ==> CurLINV li tid.
Proof. intros table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next R li tid HR. unfold V293_link_residual_frame. apply V293_raw_cells_CurLINV. do 2 apply V293_star_CurLINV_r. exact HR. Qed.

Lemma V293_link_layout : forall table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 next bh bgrp br bn oldblock oldbase present oldprev g row n oldback,
 Permutation
 ((((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))::
 V293_tcb_success_cells bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base))(Vint32 Int.zero)next next) ++
 V293_link_extra bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback)
 (V293_pub_cells bc bt base bh bgrp br bn oldblock oldbase present (V293_prio_row p)(V293_prio_bit p)
 next oldprev(V293_pub_old_head present oldblock oldbase)g row n oldback ++
 V293_link_residual table bg bu bp bs bb bi bz be bo bt base p top bottom identity size ext options next).
Proof.
 intros. destruct present;
 unfold V293_tcb_success_cells,V293_tcb_init_final_fields,V293_tcb_prefix_inputs,V293_tcb_init_input_cells,
 V293_tcb_prefix_links,V293_link_extra,V293_pub_cells,V293_link_residual;
 cbn [app tl];V293_link_permute.
Qed.

Lemma V293_link_exchange : forall xs ys A B,
 V293_rdy_raw_cells xs (A ** V293_rdy_raw_cells ys B) ==>
 V293_rdy_raw_cells (xs++ys) (A ** B).
Proof.
 intros xs ys A B. rewrite V293_raw_cells_append. apply V293_raw_cells_mono. apply V293_raw_cells_unmove_frame.
Qed.

Theorem V293_tcb_initialized_publish_view : forall table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs,
 V293_tcb_table_state table (Vptr(bt,Int.repr base)) bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base))(Vint32 Int.zero)next next
 (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs ==>
 V293_pub_hstate 108%Z 93%Z 94%Z 95%Z 96%Z bc bh bgrp br bn
 (V293_pub_cells bc bt base bh bgrp br bn oldblock oldbase present (V293_prio_row p)(V293_prio_bit p)
 next oldprev(V293_pub_old_head present oldblock oldbase)g row n oldback)
 (V293_link_residual_frame table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next R) aop isr is cs.
Proof.
 intros table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs.
 unfold V293_tcb_table_state,V293_link_frame,V293_pub_hstate,V293_link_residual_frame.
 apply astar_mono;[intros s HS;exact HS| ]. intros s HS.
 assert (Flat : s |= V293_rdy_raw_cells
 ((((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr(bt,Int.repr base))::
 V293_tcb_success_cells bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base))(Vint32 Int.zero)next next) ++
 V293_link_extra bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback)
 ((OS[isr,false,is,cs] ** (V293_tcb_success_bindings bg bu bc bp bs bb bi bz be bo ** V293_tcb_table_binding table)) **
 (V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z bc bh bgrp br bn ** R))).
 { apply V293_link_exchange. eapply V293_raw_cells_mono;[ |exact HS]. intros st H. clear -H. sep auto. }
 apply (V293_link_cells_permutation _ _ _ (V293_link_layout table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback)) in Flat.
 rewrite V293_raw_cells_append in Flat.
 eapply V293_raw_cells_mono;[ |exact Flat]. intros st H.
 (* Regroup only bindings, not the owned byte cells. *)
 assert (Reordered : st |= V293_rdy_raw_cells
 (V293_link_residual table bg bu bp bs bb bi bz be bo bt base p top bottom identity size ext options next)
 ((OS[isr,false,is,cs] ** V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z bc bh bgrp br bn) **
 (V293_tcb_success_bindings bg bu bc bp bs bb bi bz be bo ** (V293_tcb_table_binding table ** R)))).
 { eapply V293_raw_cells_mono;[ |exact H]. intros st1 H1. clear -H1. sep auto. }
 apply V293_raw_cells_move_frame in Reordered. clear -Reordered. sep auto.
Qed.

(* All unmodified cells remain spatially owned in the return frame. *)
Definition V293_link_return_post table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs : retasrt :=
 V293_pub_return_post 108%Z 93%Z 94%Z 95%Z 96%Z bc bh bgrp br bn
 (V293_pub_cells bc bt base bh bgrp br bn oldblock oldbase present (V293_prio_row p)(V293_prio_bit p)
  (V293_pub_old_head present oldblock oldbase) Vnull (Vptr(bt,Int.repr base))
  (Nat.setbit g (V293_prio_row p)) (Nat.setbit row (V293_prio_bit p)) (S n) (Vptr(bt,Int.repr base)))
 (V293_link_residual_frame table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next R) aop isr is cs.

Theorem V293_OS_TCBInit_linked_body_hoare : forall Spec sd li I tid hi hc slot old pc cpu table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs,
 p<13 -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 (0<=oldbase)%Z -> (oldbase+24<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 rule_type_val_match (Tptr V293_tcb_type) next=true ->
 g<256 -> row<256 -> n<255 -> GoodFrm R -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I (V293_link_return_post table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs) Afalse
 (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options) (Vptr(bt,Int.repr base)) (Vint32 Int.zero) next next (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs) (scall hi [evar 108%Z]) (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options) (Vptr(bt,Int.repr base)) (Vint32 Int.zero) next next (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs) tid ->
 InfRules Spec sd li I (V293_link_return_post table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs) Afalse
 (V293_tcb_table_state table (Vptr(bt,Int.repr base)) bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options) (Vptr(bt,Int.repr base)) (Vint32 Int.zero) next next (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs) (scall hc [evar 108%Z]) (V293_tcb_table_state table (Vptr(bt,Int.repr base)) bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options) (Vptr(bt,Int.repr base)) (Vint32 Int.zero) next next (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs) tid ->
 InfRules Spec sd li I (V293_link_return_post table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs) Afalse
 (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_old_fields bt base old) pc cpu (Vptr(bt,Int.repr base)) next (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs) (V293_TCBInit_function_body hi hc) Afalse tid.
Proof.
 intros Spec sd li I tid hi hc slot old pc cpu table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs
 Range Base Bound OldBase OldBound Valid Next Group Row Count Frame HR InitHook CreateHook.
 apply V293_OS_TCBInit_nonempty_body_split_hoare;try assumption.
 - apply V293_link_frame_good;exact Frame.
 - apply V293_link_frame_linv;exact HR.
 - eapply conseq_rule.
   + apply V293_tcb_initialized_publish_view.
   + intros s HS. exact HS.
   + unfold V293_link_return_post.
     apply V293_OS_TCBInit_publish_hoare;try assumption;try lia.
     * apply V293_prio_coordinates in Range. tauto.
     * apply V293_prio_coordinates in Range. tauto.
     * apply V293_link_residual_good;exact Frame.
     * apply V293_link_residual_linv;exact HR.
Qed.

Theorem V293_OS_TCBInit_linked_body_semantics : forall Spec sd li I tid hi hc slot old pc cpu table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs,
 p<13 -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 (0<=oldbase)%Z -> (oldbase+24<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 rule_type_val_match (Tptr V293_tcb_type) next=true ->
 g<256 -> row<256 -> n<255 -> GoodFrm R -> (R ==> CurLINV li tid) ->
 InfRules Spec sd li I (V293_link_return_post table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs) Afalse
 (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options) (Vptr(bt,Int.repr base)) (Vint32 Int.zero) next next (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs) (scall hi [evar 108%Z]) (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options) (Vptr(bt,Int.repr base)) (Vint32 Int.zero) next next (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs) tid ->
 InfRules Spec sd li I (V293_link_return_post table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs) Afalse
 (V293_tcb_table_state table (Vptr(bt,Int.repr base)) bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options) (Vptr(bt,Int.repr base)) (Vint32 Int.zero) next next (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs) (scall hc [evar 108%Z]) (V293_tcb_table_state table (Vptr(bt,Int.repr base)) bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options) (Vptr(bt,Int.repr base)) (Vint32 Int.zero) next next (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs) tid ->
 simulation.RuleSem Spec sd li I (V293_link_return_post table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs) Afalse
 (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_old_fields bt base old) pc cpu (Vptr(bt,Int.repr base)) next (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs) (V293_TCBInit_function_body hi hc) Afalse tid.
Proof. intros. apply RuleSound. apply V293_OS_TCBInit_linked_body_hoare;assumption. Qed.
