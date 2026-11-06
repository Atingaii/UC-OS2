(* A logical initial-head snapshot is checked against the physical free head.
   Exact branch postconditions are retained, not an uncorrelated union. *)
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope nat_scope.


Definition V293_tcb_guard_fpre (condition:Prop) (fp:fpre) : fpre :=
 fun vl lg tid => @mkfunasrt ([|condition|] ** getasrt(fp vl lg tid))
 (conj I (getprop(fp vl lg tid))).
Definition V293_tcb_guard_fpost (condition:Prop) (fq:fpost) : fpost :=
 fun vl result lg tid => @mkfunasrt ([|condition|] ** getasrt(fq vl result lg tid))
 (conj I (getprop(fq vl result lg tid))).
Definition V293_tcb_snapshot_fpre (allocated:val) (empty ready:fpre) : fpre :=
 fun vl lg tid => match lg with
 | [item] => match item with
   | logic_val Vnull => empty vl lg tid
   | logic_val (Vptr pointer) => V293_tcb_guard_fpre (Vptr pointer=allocated) ready vl lg tid
   | _ => @mkfunasrt Afalse I
   end
 | _ => @mkfunasrt Afalse I
 end.
Definition V293_tcb_snapshot_fpost (allocated:val) (empty ready:fpost) : fpost :=
 fun vl result lg tid => match lg with
 | [item] => match item with
   | logic_val Vnull => empty vl result lg tid
   | logic_val (Vptr pointer) => V293_tcb_guard_fpost (Vptr pointer=allocated) ready vl result lg tid
   | _ => @mkfunasrt Afalse I
   end
 | _ => @mkfunasrt Afalse I
 end.

Lemma V293_tcb_guard_builder_rule : forall P f Spec sd li I tid body vl lg
 (condition:Prop) (fp:fpre) (fq:fpost) pre post,
 (forall p q, Some p=BuildPreI P f vl lg fp tid ->
  Some q=BuildRetI P f vl lg fq tid ->
  InfRules Spec sd li I q Afalse p body Afalse tid) ->
 Some pre=BuildPreI P f vl lg (V293_tcb_guard_fpre condition fp) tid ->
 Some post=BuildRetI P f vl lg (V293_tcb_guard_fpost condition fq) tid ->
 InfRules Spec sd li I post Afalse pre body Afalse tid.
Proof.
 intros P f Spec sd li I tid body vl lg condition fp fq pre post Contract Pre Post.
 unfold BuildPreI in Pre.
 destruct(P f) as [[[[rt d1] d2] b] | ] eqn:Code;[ |discriminate].
 destruct(dl_vl_match d1 (rev vl)) eqn:Typed;[ |discriminate].
 destruct(buildp(revlcons d1 d2)vl) as [locals | ] eqn:Cells;[ |discriminate].
 cbn [V293_tcb_guard_fpre getasrt] in Pre. inversion Pre;subst pre.
 unfold BuildRetI in Post. rewrite Code in Post.
 destruct(buildq(revlcons d1 d2)) as [returned | ] eqn:ReturnCells;[ |discriminate].
 cbn [V293_tcb_guard_fpost getasrt] in Post. inversion Post;subst post.
 eapply conseq_rule with (p:=(locals ** getasrt(fp(rev vl)lg tid) **
 A_dom_lenv(getlenvdom(revlcons d1 d2))) ** [|condition|]).
 - intros s H. clear -H. sep auto.
 - intros s H;exact H.
 - apply pure_split_rule. intro Saved.
   eapply r_conseq_rule with (r:=fun result=>returned ** getasrt(fq(rev vl)result lg tid) **
     A_dom_lenv(getlenvdom(revlcons d1 d2))).
   + intros result s H.
     assert(K:s |= [|condition|] ** (returned ** getasrt(fq(rev vl)result lg tid) **
       A_dom_lenv(getlenvdom(revlcons d1 d2)))).
     { apply astar_l_apure_intro;[exact H|exact Saved]. }
     clear -K. sep auto.
   + intros s H;exact H.
   + apply Contract.
     * unfold BuildPreI. rewrite Code,Typed,Cells. reflexivity.
     * unfold BuildRetI. rewrite Code,ReturnCells. reflexivity.
Qed.
Lemma V293_tcb_false_builder_rule : forall P f Spec sd li I tid body vl lg pre post,
 Some pre=BuildPreI P f vl lg (fun _ _ _=>@mkfunasrt Afalse Logic.I) tid ->
 InfRules Spec sd li I post Afalse pre body Afalse tid.
Proof.
 intros P f Spec sd li I tid body vl lg pre post Pre.
 unfold BuildPreI in Pre.
 destruct(P f) as [[[[rt d1] d2] b] | ];[ |discriminate].
 destruct(dl_vl_match d1 (rev vl));[ |discriminate].
 destruct(buildp(revlcons d1 d2)vl) as [locals | ];[ |discriminate].
 cbn [getasrt] in Pre. inversion Pre;subst pre.
 eapply conseq_rule with (p:=Afalse).
 - intros s H. apply astar_comm in H. apply astar_assoc_elim in H.
   apply astar_l_afalse_elim in H. exact H.
 - intros s H;exact H.
 - apply pfalse_rule.
Qed.

Theorem V293_OS_TCBInit_snapshot_internal_contract : forall P f Spec sd li I tid hi hc slot old table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs vl lg pre post,
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
 Some pre=BuildPreI P f vl lg (V293_tcb_snapshot_fpre (Vptr(bt,Int.repr base)) (V293_tcb_empty_fpre bg R aop isr is cs Hfun) (V293_tcb_success_fpre table slot bg bt base old p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs Hfun)) tid ->
 Some post=BuildRetI P f vl lg (V293_tcb_snapshot_fpost (Vptr(bt,Int.repr base)) (V293_tcb_empty_fpost bg R aop isr is cs Hfun) (V293_tcb_success_fpost table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs Hfun)) tid ->
 InfRules Spec sd li I post Afalse pre (V293_TCBInit_function_body hi hc) Afalse tid.
Proof.
 intros P f Spec sd li I tid hi hc slot old table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs vl lg pre post
 GI Range Base Bound OldBase OldBound Valid Next Group Row Count Frame HR Hfun InitLookup CreateLookup Code Pre Post.
 destruct lg as [ |l tail];[eapply V293_tcb_false_builder_rule with (P:=P) (f:=f) (vl:=vl) (lg:=[]);exact Pre| ].
 destruct tail as [ |l2 tail];[ |eapply V293_tcb_false_builder_rule with (P:=P) (f:=f) (vl:=vl) (lg:=[]);exact Pre].
 destruct l as [x|x|x|x|x|head|x|x|x|x|x|x|x];
 try (eapply V293_tcb_false_builder_rule with (P:=P) (f:=f) (vl:=vl) (lg:=[]);exact Pre).
 destruct head as [ | |number|pointer];
 try (eapply V293_tcb_false_builder_rule with (P:=P) (f:=f) (vl:=vl) (lg:=[]);exact Pre).
 - exact(V293_OS_TCBInit_empty_internal_contract P f Spec sd li I tid hi hc bg R aop isr is cs Hfun vl [logic_val Vnull] pre post Frame HR Code Pre Post).
 - eapply V293_tcb_guard_builder_rule with (P:=P) (f:=f) (vl:=vl) (lg:=[logic_val (Vptr pointer)]);[ |exact Pre|exact Post].
   intros rp rq RP RQ.
   exact(V293_OS_TCBInit_success_internal_contract P f Spec sd li I tid hi hc slot old table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs vl [logic_val (Vptr pointer)] rp rq GI Range Base Bound OldBase OldBound Valid Next Group Row Count Frame HR Hfun InitLookup CreateLookup Code RP RQ).
Qed.


(* The memory at entry, not a free Boolean, determines the snapshot. *)
Lemma V293_tcb_snapshot_pre_load : forall allocated empty ready vl lg tid bg saved s,
 (forall args ghosts task st, st |= getasrt(empty args ghosts task) ->
  load(Tptr V293_tcb_type)(getmem st)(bg,0%Z)=Some Vnull) ->
 (forall args ghosts task st, st |= getasrt(ready args ghosts task) ->
  load(Tptr V293_tcb_type)(getmem st)(bg,0%Z)=Some allocated) ->
 lg=[logic_val saved] ->
 s |= getasrt(V293_tcb_snapshot_fpre allocated empty ready vl lg tid) ->
 load(Tptr V293_tcb_type)(getmem s)(bg,0%Z)=Some saved.
Proof.
 intros allocated empty ready vl lg tid bg saved s Empty Ready Ghost Owned. subst lg.
 destruct saved as [ | |number|pointer];cbn [V293_tcb_snapshot_fpre getasrt] in Owned;
 try contradiction.
 - apply Empty in Owned. exact Owned.
 - apply astar_l_apure_elim in Owned. destruct Owned as [Equal Owned].
   subst allocated. apply Ready in Owned. exact Owned.
Qed.
Lemma V293_tcb_empty_pre_head : forall bg R aop isr is cs good vl lg tid s,
 s |= getasrt(V293_tcb_empty_fpre bg R aop isr is cs good vl lg tid) ->
 load(Tptr V293_tcb_type)(getmem s)(bg,0%Z)=Some Vnull.
Proof.
 intros bg R aop isr is cs good vl lg tid s H.
 cbn [V293_tcb_empty_fpre getasrt V293_tcb_empty_external] in H.
 eapply V293_star_load_r;[ |exact H]. intros st H1.
 eapply V293_star_load_l;[ |exact H1]. intros st1 [Points _].
 eapply mapstoval_load;[reflexivity|exact Points].
Qed.
Lemma V293_tcb_success_pre_head : forall table slot bg bt base old p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good vl lg tid s,
 s |= getasrt(V293_tcb_success_fpre table slot bg bt base old p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good vl lg tid) ->
 load(Tptr V293_tcb_type)(getmem s)(bg,0%Z)=Some(Vptr(bt,Int.repr base)).
Proof.
 intros table slot bg bt base old p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present oldprev g row n oldback R aop isr is cs good vl lg tid s H.
 cbn [V293_tcb_success_fpre getasrt] in H.
 eapply V293_star_load_r;[ |exact H]. intros st H1.
 unfold V293_tcb_success_external,V293_hook_resource in H1.
 eapply V293_star_load_r;[ |exact H1]. intros st1 H2.
 eapply V293_rdy_raw_load;[ |reflexivity|exact H2].
 unfold V293_tcb_success_pre_owned. right. apply in_or_app. right.
 apply in_or_app. left. unfold V293_tcb_prefix_links. simpl;auto.
Qed.

(* This is a post-state consequence: it does not assert an execution exists. *)
Lemma V293_tcb_snapshot_post_code : forall allocated empty ready vl lg tid saved result s,
 (forall args ghosts task st r, st |= getasrt(empty args r ghosts task) ->
  r=Some(Vint32(Int.repr 66))) ->
 (forall args ghosts task st r, st |= getasrt(ready args r ghosts task) ->
  r=Some(Vint32 Int.zero)) ->
 lg=[logic_val saved] ->
 s |= getasrt(V293_tcb_snapshot_fpost allocated empty ready vl result lg tid) ->
 (saved=Vnull /\ result=Some(Vint32(Int.repr 66))) \/
 (saved=allocated /\ result=Some(Vint32 Int.zero)).
Proof.
 intros allocated empty ready vl lg tid saved result s Empty Ready Ghost Owned. subst lg.
 destruct saved as [ | |number|pointer];cbn [V293_tcb_snapshot_fpost getasrt] in Owned;
 try contradiction.
 - left. split;[reflexivity|eapply Empty;exact Owned].
 - apply astar_l_apure_elim in Owned. destruct Owned as [Equal Owned].
   right. split;[exact Equal|eapply Ready;exact Owned].
Qed.
Lemma V293_tcb_empty_post_code : forall bg R aop isr is cs good vl result lg tid s,
 s |= getasrt(V293_tcb_empty_fpost bg R aop isr is cs good vl result lg tid) ->
 result=Some(Vint32(Int.repr 66)).
Proof.
 intros bg R aop isr is cs good vl result lg tid s H.
 cbn [V293_tcb_empty_fpost getasrt] in H.
 apply astar_l_apure_elim in H. exact(proj1 H).
Qed.
Lemma V293_tcb_success_post_code : forall table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs good vl result lg tid s,
 s |= getasrt(V293_tcb_success_fpost table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs good vl result lg tid) ->
 result=Some(Vint32 Int.zero).
Proof.
 intros table bg bt base p top bottom identity size ext options next bh bgrp br bn oldblock oldbase present g row n R aop isr is cs good vl result lg tid s H.
 cbn [V293_tcb_success_fpost getasrt] in H.
 apply astar_l_apure_elim in H. exact(proj1 H).
Qed.
