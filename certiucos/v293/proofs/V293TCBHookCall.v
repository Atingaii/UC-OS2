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

Require Import CertiOS.certiucos.v293.proofs.V293TCBLinkedHoare.

(* Actual Hook call sites. Contracts are external boundary SPECIALIZATIONS,
   not implementations. All caller local cells and bindings stay in the frame. *)
Definition V293_hook_local_cells bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options :=
 ((bu,0%Z),Tint32,Vint32 Int.zero)::
 V293_tcb_prefix_inputs bc bp bs bb bi bz be bo (Vptr(bt,Int.repr base)) p top bottom identity size ext options.
Definition V293_hook_owned_cells table slot bg bt base p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback :=
 ((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,slot)::
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options ++
 V293_tcb_prefix_links bg bt base next next ++
 V293_link_extra bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback).
Definition V293_hook_bindings table bg bu bc bp bs bb bi bz be bo bh bgrp br bn :=
 V293_tcb_success_bindings bg bu bc bp bs bb bi bz be bo **
 (V293_tcb_table_binding table ** V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z bc bh bgrp br bn).
Definition V293_hook_resource cells R aop isr is cs :=
 <||aop||> ** V293_rdy_raw_cells cells (OS[isr,false,is,cs] ** R).
Definition V293_hook_frame locals bindings := V293_rdy_raw_cells locals bindings.

Lemma V293_hook_resource_good : forall cells R aop isr is cs,
 GoodFunAsrt R -> GoodFunAsrt(V293_hook_resource cells R aop isr is cs).
Proof.
 intros cells R aop isr is cs HR. unfold V293_hook_resource. split;[exact I| ].
 induction cells as [ | [[a tp] v] tail IH];cbn [V293_rdy_raw_cells GoodFunAsrt];tauto.
Qed.
Lemma V293_hook_resource_linv : forall cells R aop isr is cs li tid,
 (R ==> CurLINV li tid) -> V293_hook_resource cells R aop isr is cs ==> CurLINV li tid.
Proof.
 intros cells R aop isr is cs li tid HR. unfold V293_hook_resource. apply V293_star_CurLINV_r. apply V293_raw_cells_CurLINV.
 apply V293_star_CurLINV_r. assumption.
Qed.
Lemma V293_hook_frame_good : forall locals table bg bu bc bp bs bb bi bz be bo bh bgrp br bn,
 GoodFrm(V293_hook_frame locals(V293_hook_bindings table bg bu bc bp bs bb bi bz be bo bh bgrp br bn)).
Proof.
 intros. apply V293_raw_cells_good_frame. unfold V293_hook_bindings.
 cbn [GoodFrm]. split;[apply V293_tcb_success_bindings_good| ].
 split;[cbn [V293_tcb_table_binding GoodFrm];tauto|apply V293_pub_bindings_good].
Qed.

(* No local identifiers or caller-local addresses in this function assertion.
   The pointer argument and current task are checked, not ignored. *)
Definition V293_hook_fpre (pointer:val) (owner:tid) (resource:asrt)
 (good:GoodFunAsrt resource) : fpre :=
 fun vl lg tid => @mkfunasrt ([|vl=[pointer] /\ tid=owner|] ** resource) (conj I good).
Definition V293_hook_fpost (pointer:val) (owner:tid) (resource:asrt)
 (good:GoodFunAsrt resource) : fpost :=
 fun vl result lg tid => @mkfunasrt
 ([|vl=[pointer] /\ tid=owner /\ result=None|] ** resource) (conj I good).

Lemma V293_hook_cells_factor : forall xs ys A B s,
 (s |= V293_rdy_raw_cells(xs++ys)(A ** B)) <->
 (s |= V293_rdy_raw_cells xs A ** V293_rdy_raw_cells ys B).
Proof.
 intros xs ys A B s. rewrite V293_raw_cells_append. split;intro HS.
 - assert(K:s |= V293_rdy_raw_cells xs (V293_rdy_raw_cells ys B ** A)).
   { eapply V293_raw_cells_mono;[ |exact HS]. intros st H.
     apply V293_raw_cells_move_frame in H. clear -H. sep auto. }
   apply V293_raw_cells_move_frame in K. clear -K. sep auto.
 - assert(K:s |= V293_rdy_raw_cells ys B ** V293_rdy_raw_cells xs A).
   { clear -HS. sep auto. }
   apply V293_raw_cells_unmove_frame in K.
   eapply V293_raw_cells_mono;[ |exact K]. intros st H.
   assert(K2:st |= A ** V293_rdy_raw_cells ys B). { clear -H. sep auto. }
   apply V293_raw_cells_unmove_frame in K2. exact K2.
Qed.

Lemma V293_hook_layout : forall table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 next bh bgrp br bn oldblock oldbase present oldprev g row n oldback,
 Permutation
 ((((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,slot)::
 V293_tcb_success_cells bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base))(Vint32 Int.zero)next next) ++
 V293_link_extra bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback)
 (V293_hook_owned_cells table slot bg bt base p top bottom identity size ext options next
 bh bgrp br bn oldblock oldbase present oldprev g row n oldback ++
 V293_hook_local_cells bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options).
Proof.
 intros. destruct present;unfold V293_hook_owned_cells,V293_hook_local_cells,
 V293_tcb_success_cells,V293_tcb_init_final_fields,V293_tcb_prefix_inputs,V293_tcb_init_input_cells,
 V293_tcb_prefix_links,V293_link_extra;cbn [app tl];V293_link_permute.
Qed.

Theorem V293_tcb_hook_view : forall table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs s,
 (s |= V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base))(Vint32 Int.zero)next next
 (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs) <-> (s |= (V293_hook_resource (V293_hook_owned_cells table slot bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) ** (V293_hook_frame (V293_hook_local_cells bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options) (V293_hook_bindings table bg bu bc bp bs bb bi bz be bo bh bgrp br bn))).
Proof.
 intros table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs s.
 unfold V293_tcb_table_state,V293_link_frame,V293_hook_resource,V293_hook_frame,V293_hook_bindings.
 set (xs:=((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,slot)::
 V293_tcb_success_cells bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base))(Vint32 Int.zero)next next).
 set (ys:=V293_link_extra bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback).
 set (bindings:=V293_hook_bindings table bg bu bc bp bs bb bi bz be bo bh bgrp br bn).
 set (locals:=V293_hook_local_cells bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options). set (owned:=V293_hook_owned_cells table slot bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback).
 assert(Perm:Permutation (xs++ys)(owned++locals)). { apply V293_hook_layout. }
 assert(Flat:forall st,
 (st |= V293_rdy_raw_cells xs (OS[isr,false,is,cs] **
  (V293_tcb_success_bindings bg bu bc bp bs bb bi bz be bo ** (V293_tcb_table_binding table **
   V293_rdy_raw_cells ys(V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z bc bh bgrp br bn ** R))))) <->
 (st |= V293_rdy_raw_cells (owned++locals)((OS[isr,false,is,cs] ** R) ** bindings))).
 { intro st. split;intro H.
   - assert(K:st |= V293_rdy_raw_cells (xs++ys)
      (((OS[isr,false,is,cs] ** V293_tcb_success_bindings bg bu bc bp bs bb bi bz be bo) ** V293_tcb_table_binding table) **
       (V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z bc bh bgrp br bn ** R))).
     { apply V293_link_exchange. eapply V293_raw_cells_mono;[ |exact H]. intros st1 H1. clear -H1. sep auto. }
     apply (V293_link_cells_permutation _ _ _ Perm) in K.
     eapply V293_raw_cells_mono;[ |exact K]. intros st1 H1. unfold bindings,V293_hook_bindings. clear -H1. sep auto.
   - apply (V293_link_cells_permutation _ _ _ (Permutation_sym Perm)) in H.
     rewrite V293_raw_cells_append in H.
     eapply V293_raw_cells_mono;[ |exact H]. intros st1 H1.
     assert(K:st1 |= V293_rdy_raw_cells ys
      (((OS[isr,false,is,cs] ** V293_tcb_success_bindings bg bu bc bp bs bb bi bz be bo) ** V293_tcb_table_binding table) **
       (V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z bc bh bgrp br bn ** R))).
     { eapply V293_raw_cells_mono;[ |exact H1]. intros st2 H2. unfold bindings,V293_hook_bindings in H2. clear -H2. sep auto. }
     apply V293_raw_cells_move_frame in K. clear -K. sep auto.
 }
 split;intro HS.
 - assert(K:s |= <||aop||> ** V293_rdy_raw_cells(owned++locals)((OS[isr,false,is,cs] ** R) ** bindings)).
   { eapply astar_mono;[intros st H;exact H| |exact HS]. intros st H. apply Flat. exact H. }
   assert(K2:s |= <||aop||> ** (V293_rdy_raw_cells owned(OS[isr,false,is,cs] ** R) ** V293_rdy_raw_cells locals bindings)).
   { eapply astar_mono;[intros st H;exact H| |exact K]. intros st H. apply V293_hook_cells_factor in H. exact H. }
   unfold bindings,V293_hook_bindings in K2. clear -K2. sep auto.
 - assert(K:s |= <||aop||> ** (V293_rdy_raw_cells owned(OS[isr,false,is,cs] ** R) ** V293_rdy_raw_cells locals bindings)).
   { unfold bindings,V293_hook_bindings. clear -HS. sep auto. }
   eapply astar_mono;[intros st H;exact H| |exact K]. intros st H. apply Flat.
   apply V293_hook_cells_factor. exact H.
Qed.

Theorem V293_tcb_hook_argument : forall table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs,
 V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base))(Vint32 Int.zero)next next
 (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs ==> Rvl [evar 108%Z] @ [Tptr V293_tcb_type] == [Vptr(bt,Int.repr base)].
Proof.
 intros table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs s HS. unfold V293_tcb_table_state in HS.
 destruct s as [[[[[[ge le] M] ir] aux] O] op].
 (* Evaluate in the WHOLE caller memory, not a separated submemory. *)
 assert(Env: get le 108%Z=Some(bc,Tptr V293_tcb_type)).
 { change (get (getlenv (ge,le,M,ir,aux,O,op)) 108%Z=Some(bc,Tptr V293_tcb_type)).
   eapply V293_star_env_r with (E:=fun ge le=>get le 108%Z=Some(bc,Tptr V293_tcb_type));[ |exact HS].
   intros st H. V293_success_env H. exact Bc. }
 assert(Read:load (Tptr V293_tcb_type) M (bc,0%Z)=Some(Vptr(bt,Int.repr base))).
 { change (load (Tptr V293_tcb_type) (getmem(ge,le,M,ir,aux,O,op)) (bc,0%Z)=Some(Vptr(bt,Int.repr base))).
   eapply V293_star_load_r;[ |exact HS]. intros st H.
   eapply V293_rdy_raw_load;[ |reflexivity|exact H].
   cbn [V293_tcb_success_cells V293_tcb_init_final_fields V293_tcb_prefix_inputs V293_tcb_init_input_cells].
   do 20 right. left. reflexivity. }
 cbn [sat getsmem evalexprlist evaltype evalval evaladdr get_smem get_lenv].
 cbv delta [env var memory.ident Modules.ident] in *. rewrite Env.
 repeat split;first [assumption|reflexivity|discriminate].
Qed.

Theorem V293_tcb_hook_call : forall Spec sd li I r ri tid f table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs,
 (R ==> CurLINV li tid) ->
 forall (good:GoodFunAsrt (V293_hook_resource (V293_hook_owned_cells table slot bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs)),
 Spec f=Some(V293_hook_fpre (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table slot bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) good,
 V293_hook_fpost (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table slot bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) good,(Tvoid,[Tptr V293_tcb_type])) ->
 InfRules Spec sd li I r ri (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base))(Vint32 Int.zero)next next
 (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs) (scall f [evar 108%Z]) (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base))(Vint32 Int.zero)next next
 (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs) tid.
Proof.
 intros Spec sd li I r ri tid f table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs HR good Lookup.
 eapply conseq_rule with
 (p:=V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_final_fields bt base p top bottom identity size ext options)
 (Vptr(bt,Int.repr base))(Vint32 Int.zero)next next
 (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs)
 (q:=EX result:option val, getasrt(V293_hook_fpost (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table slot bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) good
 [Vptr(bt,Int.repr base)] result [] tid) ** (V293_hook_frame (V293_hook_local_cells bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options) (V293_hook_bindings table bg bu bc bp bs bb bi bz be bo bh bgrp br bn))).
 - intros s H;exact H.
 - intros s [result HS]. apply V293_tcb_hook_view.
   cbn [V293_hook_fpost getasrt] in HS. clear -HS. sep auto.
 - eapply call_rule with
   (pre:=V293_hook_fpre (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table slot bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) good)
   (post:=V293_hook_fpost (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table slot bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) good)
   (vl:=[Vptr(bt,Int.repr base)]) (logicl:=[]) (tp:=Tvoid) (tl:=[Tptr V293_tcb_type])
   (p:=V293_hook_frame (V293_hook_local_cells bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options) (V293_hook_bindings table bg bu bc bp bs bb bi bz be bo bh bgrp br bn)).
   + apply V293_hook_frame_good.
   + exact Lookup.
   + intros s HS. apply V293_tcb_hook_view in HS.
     cbn [V293_hook_fpre getasrt]. clear -HS. sep auto.
   + apply V293_tcb_hook_argument.
   + reflexivity.
   + cbn [V293_hook_fpre getasrt]. apply V293_star_CurLINV_r. apply V293_hook_resource_linv. exact HR.
   + intros s [result HS]. cbn [V293_hook_fpost getasrt] in HS.
     eapply V293_star_CurLINV_r;[apply V293_hook_resource_linv;exact HR|exact HS].
Qed.

(* Both call Hoare premises have been discharged by the REAL call_rule.
   The remaining two lookups are declared CPU-port contracts, not body proofs.
   Additional GoodFunAsrt R excludes caller-local bindings from that contract. *)
Theorem V293_OS_TCBInit_hook_calls_body_hoare : forall Spec sd li I tid hi hc slot old pc cpu table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs,
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
 InfRules Spec sd li I (V293_link_return_post table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs) Afalse
 (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_old_fields bt base old) pc cpu (Vptr(bt,Int.repr base)) next (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs) (V293_TCBInit_function_body hi hc) Afalse tid.
Proof.
 intros Spec sd li I tid hi hc slot old pc cpu table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs
 Range Base Bound OldBase OldBound Valid Next Group Row Count Frame HR Hfun InitLookup CreateLookup.
 apply V293_OS_TCBInit_linked_body_hoare;try assumption.
 - eapply V293_tcb_hook_call;[exact HR|exact InitLookup].
 - eapply V293_tcb_hook_call;[exact HR|exact CreateLookup].
Qed.

Theorem V293_OS_TCBInit_hook_calls_body_semantics : forall Spec sd li I tid hi hc slot old pc cpu table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs,
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
 simulation.RuleSem Spec sd li I (V293_link_return_post table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs) Afalse
 (V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_old_fields bt base old) pc cpu (Vptr(bt,Int.repr base)) next (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs) (V293_TCBInit_function_body hi hc) Afalse tid.
Proof. intros. apply RuleSound. eapply V293_OS_TCBInit_hook_calls_body_hoare;eassumption. Qed.
