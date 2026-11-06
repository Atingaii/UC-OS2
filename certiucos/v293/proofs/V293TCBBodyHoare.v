(* One complete body for both actual free-list cases. The success resource
   is the existing success return assertion at its actual return value, so no
   resource is forgotten. This is not a function-call allocation/free proof. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBLinkedHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublishHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.soundness.
Require CertiOS.framework.proof.simulation.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

(* Standard disjunctive return assertion; no Boolean oracle chooses a branch.
   Each return code retains exactly that branch's entire spatial resource. *)
Definition V293_tcb_body_post (empty ready:asrt) : retasrt := fun result =>
 ([|result=Some(Vint32(Int.repr 66))|] ** empty) \\//
 ([|result=Some(Vint32 Int.zero)|] ** ready).

Lemma V293_tcb_body_post_codes : forall empty ready result s,
 s |= V293_tcb_body_post empty ready result ->
 result=Some(Vint32(Int.repr 66)) \/ result=Some(Vint32 Int.zero).
Proof.
 intros empty ready result s [H|H];apply astar_l_apure_elim in H;
 destruct H as [Code _];auto.
Qed.
Lemma V293_tcb_body_post_empty : forall empty ready s,
 (s |= V293_tcb_body_post empty ready (Some(Vint32(Int.repr 66)))) <-> s |= empty.
Proof.
 intros empty ready s. split.
 - intros [H|H];apply astar_l_apure_elim in H;destruct H as [Code Resource].
   + exact Resource.
   + discriminate Code.
 - intro H. left. apply astar_l_apure_intro;[exact H|reflexivity].
Qed.
Lemma V293_tcb_body_post_ready : forall empty ready s,
 (s |= V293_tcb_body_post empty ready (Some(Vint32 Int.zero))) <-> s |= ready.
Proof.
 intros empty ready s. split.
 - intros [H|H];apply astar_l_apure_elim in H;destruct H as [Code Resource].
   + discriminate Code.
   + exact Resource.
 - intro H. right. apply astar_l_apure_intro;[exact H|reflexivity].
Qed.
Lemma V293_tcb_body_post_no_other : forall empty ready result s,
 result<>Some(Vint32(Int.repr 66)) -> result<>Some(Vint32 Int.zero) ->
 ~(s |= V293_tcb_body_post empty ready result).
Proof.
 intros empty ready result s NotEmpty NotReady H.
 destruct(V293_tcb_body_post_codes _ _ _ _ H);contradiction.
Qed.
Lemma V293_tcb_body_post_no_void : forall empty ready s,
 ~(s |= V293_tcb_body_post empty ready None).
Proof. intros. apply V293_tcb_body_post_no_other;discriminate. Qed.

Theorem V293_OS_TCBInit_body_hoare : forall Spec sd li I tid hi hc slot old pc cpu table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R E aop isr is cs,
 p<13 -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 (0<=oldbase)%Z -> (oldbase+24<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 rule_type_val_match (Tptr V293_tcb_type) next=true ->
 g<256 -> row<256 -> n<255 -> GoodFrm R -> (R ==> CurLINV li tid) ->
 GoodFrm E -> (E ==> CurLINV li tid) ->
 forall (Hfun:GoodFunAsrt R),
 Spec hi=Some(
 V293_hook_fpre (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table (slot) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) (V293_hook_resource_good (V293_hook_owned_cells table (slot) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs Hfun),
 V293_hook_fpost (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table (slot) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) (V293_hook_resource_good (V293_hook_owned_cells table (slot) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs Hfun), (Tvoid,[Tptr V293_tcb_type])) ->
 Spec hc=Some(
 V293_hook_fpre (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table (Vptr(bt,Int.repr base)) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) (V293_hook_resource_good (V293_hook_owned_cells table (Vptr(bt,Int.repr base)) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs Hfun),
 V293_hook_fpost (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table (Vptr(bt,Int.repr base)) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) (V293_hook_resource_good (V293_hook_owned_cells table (Vptr(bt,Int.repr base)) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs Hfun), (Tvoid,[Tptr V293_tcb_type])) ->
 InfRules Spec sd li I (V293_tcb_body_post
 (V293_tcb_empty_state bg bc bu Vnull (Vint32 Int.zero) E aop isr is cs)
 (V293_link_return_post table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs (Some(Vint32 Int.zero)))) Afalse
 ((V293_tcb_empty_state bg bc bu pc cpu E aop isr is cs) \\//
 V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_old_fields bt base old) pc cpu (Vptr(bt,Int.repr base)) next (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs) (V293_TCBInit_function_body hi hc) Afalse tid.
Proof.
 intros Spec sd li I tid hi hc slot old pc cpu table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R E aop isr is cs
 Range Base Bound OldBase OldBound Valid Next Group Row Count Frame HR EmptyFrame HE Hfun InitLookup CreateLookup.
 apply disj_rule.
 - eapply r_conseq_rule with (r:=V293_tcb_empty_post bg bc bu E aop isr is cs) (ri:=Afalse).
   + intros result s H. left. exact H.
   + intros s H. exact H.
   + apply V293_OS_TCBInit_empty_body_hoare;assumption.
 - eapply r_conseq_rule with
   (r:=V293_link_return_post table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs) (ri:=Afalse).
   + intros result s H. right.
     unfold V293_link_return_post,V293_pub_return_post in *.
     apply astar_l_apure_elim in H. destruct H as [Code Resource].
     apply astar_l_apure_intro.
     * apply astar_l_apure_intro;[exact Resource|reflexivity].
     * exact Code.
   + intros s H. exact H.
   + eapply V293_OS_TCBInit_hook_calls_body_hoare;eassumption.
Qed.

Theorem V293_OS_TCBInit_body_semantics : forall Spec sd li I tid hi hc slot old pc cpu table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R E aop isr is cs,
 p<13 -> (0<=base)%Z -> (base+55<=Int.max_unsigned)%Z ->
 (0<=oldbase)%Z -> (oldbase+24<=Int.max_unsigned)%Z ->
 V293_tcb_init_values_valid top bottom identity size ext options ->
 rule_type_val_match (Tptr V293_tcb_type) next=true ->
 g<256 -> row<256 -> n<255 -> GoodFrm R -> (R ==> CurLINV li tid) ->
 GoodFrm E -> (E ==> CurLINV li tid) ->
 forall (Hfun:GoodFunAsrt R),
 Spec hi=Some(
 V293_hook_fpre (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table (slot) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) (V293_hook_resource_good (V293_hook_owned_cells table (slot) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs Hfun),
 V293_hook_fpost (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table (slot) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) (V293_hook_resource_good (V293_hook_owned_cells table (slot) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs Hfun), (Tvoid,[Tptr V293_tcb_type])) ->
 Spec hc=Some(
 V293_hook_fpre (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table (Vptr(bt,Int.repr base)) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) (V293_hook_resource_good (V293_hook_owned_cells table (Vptr(bt,Int.repr base)) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs Hfun),
 V293_hook_fpost (Vptr(bt,Int.repr base)) tid (V293_hook_resource (V293_hook_owned_cells table (Vptr(bt,Int.repr base)) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs) (V293_hook_resource_good (V293_hook_owned_cells table (Vptr(bt,Int.repr base)) bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback) R aop isr is cs Hfun), (Tvoid,[Tptr V293_tcb_type])) ->
 simulation.RuleSem Spec sd li I (V293_tcb_body_post
 (V293_tcb_empty_state bg bc bu Vnull (Vint32 Int.zero) E aop isr is cs)
 (V293_link_return_post table bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs (Some(Vint32 Int.zero)))) Afalse
 ((V293_tcb_empty_state bg bc bu pc cpu E aop isr is cs) \\//
 V293_tcb_table_state table slot bg bu bc bp bs bb bi bz be bo bt base p top bottom identity size ext options
 (V293_tcb_init_old_fields bt base old) pc cpu (Vptr(bt,Int.repr base)) next (V293_link_frame bc bt base bh bgrp br bn oldblock oldbase present p oldprev g row n oldback R) aop isr is cs) (V293_TCBInit_function_body hi hc) Afalse tid.
Proof.
 intros. apply RuleSound. eapply V293_OS_TCBInit_body_hoare;eassumption.
Qed.
