(* Both real OS_TCBInit branches under one standard function contract.
   The disjunction is a logical union, not a caller-supplied branch selector.
   CPU port contracts remain explicit; this is not a whole-program WFIFun. *)
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_tcb_union_fpre (left right:fpre) : fpre :=
 fun vl lg tid => @mkfunasrt
 (Adisj (getasrt(left vl lg tid)) (getasrt(right vl lg tid)))
 (conj (getprop(left vl lg tid)) (getprop(right vl lg tid))).
Definition V293_tcb_union_fpost (left right:fpost) : fpost :=
 fun vl result lg tid => @mkfunasrt
 (Adisj (getasrt(left vl result lg tid)) (getasrt(right vl result lg tid)))
 (conj (getprop(left vl result lg tid)) (getprop(right vl result lg tid))).

Lemma V293_tcb_union_resources : forall A B C D,
 A ** (Adisj B C) ** D ==> Adisj (A ** B ** D) (A ** C ** D).
Proof.
 intros A B C D s H. apply astar_comm in H.
 apply astar_assoc_elim in H. apply disj_star_elim in H.
 destruct H as [H|H].
 - left. clear -H. sep auto.
 - right. clear -H. sep auto.
Qed.
Lemma V293_tcb_union_resources_left : forall A B C D,
 A ** B ** D ==> A ** (Adisj B C) ** D.
Proof.
 intros A B C D. apply astar_mono;[intros s H;exact H| ].
 apply astar_mono;[intros s H;left;exact H|intros s H;exact H].
Qed.
Lemma V293_tcb_union_resources_right : forall A B C D,
 A ** C ** D ==> A ** (Adisj B C) ** D.
Proof.
 intros A B C D. apply astar_mono;[intros s H;exact H| ].
 apply astar_mono;[intros s H;right;exact H|intros s H;exact H].
Qed.

(* A builder algebra lemma used below. Its branch-rule arguments are discharged
   by the two already checked OS_TCBInit contracts, never public oracles. *)
Lemma V293_tcb_union_builder_rule : forall P f Spec sd li I tid body vl lg
 (leftpre rightpre:fpre) (leftpost rightpost:fpost) pre post,
 (forall p q,
  Some p=BuildPreI P f vl lg leftpre tid ->
  Some q=BuildRetI P f vl lg leftpost tid ->
  InfRules Spec sd li I q Afalse p body Afalse tid) ->
 (forall p q,
  Some p=BuildPreI P f vl lg rightpre tid ->
  Some q=BuildRetI P f vl lg rightpost tid ->
  InfRules Spec sd li I q Afalse p body Afalse tid) ->
 Some pre=BuildPreI P f vl lg (V293_tcb_union_fpre leftpre rightpre) tid ->
 Some post=BuildRetI P f vl lg (V293_tcb_union_fpost leftpost rightpost) tid ->
 InfRules Spec sd li I post Afalse pre body Afalse tid.
Proof.
 intros P f Spec sd li I tid body vl lg leftpre rightpre leftpost rightpost pre post
 Left Right Pre Post.
 unfold BuildPreI in Pre.
 destruct(P f) as [[[[rt d1] d2] b] | ] eqn:Code;[ |discriminate].
 destruct(dl_vl_match d1 (rev vl)) eqn:Typed;[ |discriminate].
 destruct(buildp(revlcons d1 d2)vl) as [locals | ] eqn:Cells;[ |discriminate].
 cbn [V293_tcb_union_fpre getasrt] in Pre. inversion Pre;subst pre.
 unfold BuildRetI in Post. rewrite Code in Post.
 destruct(buildq(revlcons d1 d2)) as [returned | ] eqn:ReturnCells;[ |discriminate].
 cbn [V293_tcb_union_fpost getasrt] in Post. inversion Post;subst post.
 assert(LPre : Some(locals ** getasrt(leftpre(rev vl)lg tid) **
 A_dom_lenv(getlenvdom(revlcons d1 d2)))=BuildPreI P f vl lg leftpre tid).
 { unfold BuildPreI. rewrite Code,Typed,Cells. reflexivity. }
 assert(RPre : Some(locals ** getasrt(rightpre(rev vl)lg tid) **
 A_dom_lenv(getlenvdom(revlcons d1 d2)))=BuildPreI P f vl lg rightpre tid).
 { unfold BuildPreI. rewrite Code,Typed,Cells. reflexivity. }
 assert(LPost : Some(fun result=>returned ** getasrt(leftpost(rev vl)result lg tid) **
 A_dom_lenv(getlenvdom(revlcons d1 d2)))=BuildRetI P f vl lg leftpost tid).
 { unfold BuildRetI. rewrite Code,ReturnCells. reflexivity. }
 assert(RPost : Some(fun result=>returned ** getasrt(rightpost(rev vl)result lg tid) **
 A_dom_lenv(getlenvdom(revlcons d1 d2)))=BuildRetI P f vl lg rightpost tid).
 { unfold BuildRetI. rewrite Code,ReturnCells. reflexivity. }
 eapply conseq_rule;[apply V293_tcb_union_resources|intros s H;exact H| ].
 apply disj_rule.
 - eapply r_conseq_rule.
   + intro result. apply V293_tcb_union_resources_left.
   + intros s H;exact H.
   + exact(Left _ _ LPre LPost).
 - eapply r_conseq_rule.
   + intro result. apply V293_tcb_union_resources_right.
   + intros s H;exact H.
   + exact(Right _ _ RPre RPost).
Qed.

Theorem V293_OS_TCBInit_internal_contract : forall P f Spec sd li I tid hi hc slot old table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs vl lg pre post,
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
 Some pre=BuildPreI P f vl lg (V293_tcb_union_fpre (V293_tcb_empty_fpre bg R aop isr is cs Hfun) (V293_tcb_success_fpre table slot bg bt base old p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs Hfun)) tid ->
 Some post=BuildRetI P f vl lg (V293_tcb_union_fpost (V293_tcb_empty_fpost bg R aop isr is cs Hfun) (V293_tcb_success_fpost table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs Hfun)) tid ->
 InfRules Spec sd li I post Afalse pre (V293_TCBInit_function_body hi hc) Afalse tid.
Proof.
 intros P f Spec sd li I tid hi hc slot old table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs vl lg pre post
 GI Range Base Bound OldBase OldBound Valid Next Group Row Count Frame HR Hfun InitLookup CreateLookup Code Pre Post.
 eapply V293_tcb_union_builder_rule;[ | |exact Pre|exact Post].
 - intros lp lq LP LQ.
   exact(V293_OS_TCBInit_empty_internal_contract P f Spec sd li I tid hi hc bg R aop isr is cs Hfun vl lg lp lq Frame HR Code LP LQ).
 - intros rp rq RP RQ.
   exact(V293_OS_TCBInit_success_internal_contract P f Spec sd li I tid hi hc slot old table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs vl lg rp rq GI Range Base Bound OldBase OldBound Valid Next Group Row Count Frame HR Hfun InitLookup CreateLookup Code RP RQ).
Qed.
