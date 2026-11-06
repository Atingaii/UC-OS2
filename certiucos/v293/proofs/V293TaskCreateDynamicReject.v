(* The rejection class is not an entry parameter. Acquire one pool, then
   classify its physical nesting byte. The pool deliberately excludes NULL. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEnabledReject.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateRejectInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateBodyFailure.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.hoareforward.init_spec.
Require Import CertiOS.tactics.hoareforward.derived_rules.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Definition V293_create_dynamic_cells (table bn:block) p n (slot:addrval) :=
 [((bn,0%Z),Tint8,V293_byteval n);
  ((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,Vptr slot)].
Definition V293_create_dynamic_owned table bn p n slot K :=
 V293_rdy_raw_cells(V293_create_dynamic_cells table bn p n slot)
 (V293_create_rejection_globals V293_create_occupied_priority table bn ** K).
Definition V293_create_reject_pool table bn p K :=
 EX n:nat, EX slot:addrval, [|n<256|] **
 V293_create_dynamic_owned table bn p n slot K.
Definition V293_create_dynamic_acquired bp bc table bn p n slot cpu K F aop ir si ci :=
 <||aop||> ** OS[ir,false,si,true::ci] **
 V293_create_dynamic_owned table bn p n slot K **
 V293_create_enabled_locals bp bc p cpu F.
Definition V293_create_dynamic_return bp bc p F aop ir si ci : retasrt :=
 fun result=>[|result=Some(Vint32(Int.repr 60)) \/
                result=Some(Vint32(Int.repr 40))|] **
 V293_create_enabled_state bp bc p(Vint32 Int.zero)F aop ir si ci.
Definition V293_create_dynamic_slot_frame table p (slot:addrval) K :=
 Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true(Vptr slot) **
 Agvarenv 92%Z(Tarray(Tptr V293_tcb_type)13)(table,0%Z) ** K.

Lemma V293_create_dynamic_close : forall table bn p n slot K,
 n<256 -> V293_create_dynamic_owned table bn p n slot K ==>
 V293_create_reject_pool table bn p K.
Proof. intros table bn p n slot K Bound s H. exists n. exists slot. sep auto. Qed.

Lemma V293_create_dynamic_isr_close : forall table bn p n slot K,
 n<256 ->
 V293_create_borrowed V293_create_from_isr table bn p n slot
 (V293_create_dynamic_slot_frame table p slot K) ==>
 V293_create_reject_pool table bn p K.
Proof.
 intros table bn p n slot K Bound s H.
 apply(V293_create_dynamic_close table bn p n slot K Bound).
 unfold V293_create_borrowed,V293_create_dynamic_slot_frame,
 V293_create_dynamic_owned,V293_create_dynamic_cells in *.
 cbn[V293_create_rejection_extra_cells V293_create_rejection_globals V293_rdy_raw_cells]in *.
 clear -H;sep auto.
Qed.
Lemma V293_create_dynamic_occupied_close : forall table bn p slot K,
 V293_create_borrowed V293_create_occupied_priority table bn p 0 slot K ==>
 V293_create_reject_pool table bn p K.
Proof.
 intros table bn p slot K s H.
 apply(V293_create_dynamic_close table bn p 0 slot K ltac:(lia)). exact H.
Qed.

Lemma V293_create_dynamic_enter : forall Spec sd li I r ri tid
 bp bc table bn p cpu F K aop ir si ci,
 (gettopis si<=INUM)%nat -> GoodFrm F ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==>
  Aisr ir ** V293_create_reject_pool table bn p K) ->
 InfRules Spec sd li I r ri
 (V293_create_enabled_state bp bc p cpu F aop ir si ci)(sprim encrit)
 (EX n:nat, EX slot:addrval, [|n<256|] **
 V293_create_dynamic_acquired bp bc table bn p n slot cpu K F aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid bp bc table bn p cpu F K aop ir si ci Bound Frame Open.
 unfold V293_create_enabled_state. eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,true,si,ci] ** ATopis(gettopis si) ** [|(gettopis si<=INUM)%nat|] **
 V293_create_enabled_locals bp bc p cpu F)
 (q:=<||aop||> ** OS[ir,false,si,true::ci] ** invlth_isr I 0(gettopis si) **
 V293_create_enabled_locals bp bc p cpu F).
 - intros s H. assert(S:s |= Ais si ** Atrue)by(sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top.
   apply astar_l_atopis_elim in Top. destruct Top as[Top _].
   pose proof(@astar_l_atopis_intro s(gettopis si)_ H Top)as HT. clear H;rename HT into H. sep auto.
 - intros s H.
   assert(B:s |= (Aisr ir ** invlth_isr I 0(gettopis si)) **
   (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) ** V293_create_enabled_locals bp bc p cpu F))by(sep auto).
   eapply astar_mono in B;[ |exact Open|intros st HS;exact HS].
   unfold V293_create_reject_pool in B.
   sep normal in B. sep destruct B. sep split in B.
   exists x. exists x0. unfold V293_create_dynamic_acquired. sep auto.
 - apply encrit1_rule. apply V293_create_enabled_good;exact Frame.
Qed.

Lemma V293_create_dynamic_classify_zero : forall bp bc table bn p slot cpu K F aop ir si ci,
 (V293_create_rejection_globals V293_create_occupied_priority table bn ** F ==>
  V293_create_rejection_views V293_create_occupied_priority table bn ** F) ->
 V293_create_dynamic_acquired bp bc table bn p 0 slot cpu K F aop ir si ci ==>
 V293_create_rejection_state V293_create_occupied_priority bp bc table bn p 0 slot cpu(K ** F)aop ir si(true::ci).
Proof.
 intros bp bc table bn p slot cpu K F aop ir si ci Views s H.
 unfold V293_create_dynamic_acquired,V293_create_dynamic_owned,V293_create_dynamic_cells,
 V293_create_enabled_locals in H.
 assert(V:s |= (V293_create_rejection_globals V293_create_occupied_priority table bn ** F) **
 (<||aop||> ** OS[ir,false,si,true::ci] **
 Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) **
 Amapsto(table,(4*Z.of_nat p)%Z)(Tptr V293_tcb_type)true(Vptr slot) ** K **
 Amapsto(bp,0%Z)Tint8 true(V293_byteval p) ** Amapsto(bc,0%Z)Tint32 true cpu **
 Alvarenv 101%Z Tint8(bp,0%Z) ** Alvarenv 109%Z Tint32(bc,0%Z))).
 { cbn[V293_rdy_raw_cells]in H. clear -H;sep auto. }
 eapply astar_mono in V;[ |exact Views|intros st HS;exact HS].
 unfold V293_create_rejection_state,V293_create_rejection_cells,V293_create_rejection_bindings.
 cbn[V293_create_rejection_extra_cells V293_rdy_raw_cells]. clear -V;sep auto.
Qed.
Lemma V293_create_dynamic_classify_positive : forall bp bc table bn p n slot cpu K F aop ir si ci,
 (V293_create_rejection_globals V293_create_from_isr table bn ** F ==>
  V293_create_rejection_views V293_create_from_isr table bn ** F) ->
 V293_create_dynamic_acquired bp bc table bn p n slot cpu K F aop ir si ci ==>
 V293_create_rejection_state V293_create_from_isr bp bc table bn p n slot cpu
 (V293_create_dynamic_slot_frame table p slot K ** F)aop ir si(true::ci).
Proof.
 intros bp bc table bn p n slot cpu K F aop ir si ci Views s H.
 unfold V293_create_dynamic_acquired,V293_create_dynamic_owned,V293_create_dynamic_cells,
 V293_create_enabled_locals in H.
 assert(V:s |= (V293_create_rejection_globals V293_create_from_isr table bn ** F) **
 (<||aop||> ** OS[ir,false,si,true::ci] **
 Amapsto(bn,0%Z)Tint8 true(V293_byteval n) **
 V293_create_dynamic_slot_frame table p slot K **
 Amapsto(bp,0%Z)Tint8 true(V293_byteval p) ** Amapsto(bc,0%Z)Tint32 true cpu **
 Alvarenv 101%Z Tint8(bp,0%Z) ** Alvarenv 109%Z Tint32(bc,0%Z))).
 { unfold V293_create_dynamic_slot_frame. cbn[V293_rdy_raw_cells V293_create_rejection_globals]in *.
   clear -H;sep auto. }
 eapply astar_mono in V;[ |exact Views|intros st HS;exact HS].
 unfold V293_create_rejection_state,V293_create_rejection_cells,V293_create_rejection_bindings.
 cbn[V293_create_rejection_extra_cells V293_rdy_raw_cells]. clear -V;sep auto.
Qed.

Lemma V293_create_dynamic_return_widen : forall k bp bc p F aop ir si ci result,
 (k=V293_create_from_isr \/ k=V293_create_occupied_priority) ->
 V293_create_enabled_return k bp bc p F aop ir si ci result ==>
 V293_create_dynamic_return bp bc p F aop ir si ci result.
Proof.
 intros k bp bc p F aop ir si ci result Kind s H.
 unfold V293_create_enabled_return in H. apply astar_l_apure_elim in H. destruct H as[Code H].
 unfold V293_create_dynamic_return. apply astar_l_apure_intro;[exact H| ].
 destruct Kind;subst k;cbn[V293_create_rejection_code]in Code;auto.
Qed.

Theorem V293_OSTaskCreateExt_dynamic_rejection_body : forall Spec sd li I tid
 bp bc table bn p cpu F K aop ir si ci sched hook tcb,
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm F -> (F ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) <==>
  Aisr ir ** V293_create_reject_pool table bn p K) ->
 (forall k,V293_create_rejection_globals k table bn ** F ==>
  V293_create_rejection_views k table bn ** F) ->
 InfRules Spec sd li I(V293_create_dynamic_return bp bc p F aop ir si ci)Afalse
 (V293_create_enabled_state bp bc p cpu F aop ir si ci)
 (V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z sched hook tcb)Afalse tid.
Proof.
 intros Spec sd li I tid bp bc table bn p cpu F K aop ir si ci sched hook tcb
 Legal Bound Frame HR Borrow Views.
 unfold V293_CreateExt_body,V293_TaskCreateExt_body,V293_TaskCreateExt_prefix.
 eapply seq_rule. { apply V293_create_enabled_cpu. exact HR. }
 eapply seq_rule.
 { apply V293_create_reject_if_false. intros s H.
   exact(V293_create_enabled_priority V293_create_occupied_priority bp bc p 0 _ F aop ir si ci s Legal H). }
 eapply seq_rule.
 { eapply V293_create_dynamic_enter;try eassumption. intros s H. apply Borrow;exact H. }
 apply ex_intro_rule. intro n. apply ex_intro_rule. intro slot.
 apply pure_split_rule'. intro NBound.
 destruct n as [ | n].
 - eapply conseq_rule;[apply V293_create_dynamic_classify_zero;apply Views|intros s H;exact H| ].
   eapply r_conseq_rule with(r:=V293_create_enabled_return V293_create_occupied_priority bp bc p F aop ir si ci)(ri:=Afalse).
   + intro result. apply V293_create_dynamic_return_widen;auto.
   + intros s H;exact H.
   + eapply seq_rule.
     { apply V293_create_reject_if_false. intros s H.
       unfold V293_create_rejection_state in H. apply astar_l_aop'_elim in H. destruct H as[_ H].
       exact(V293_create_rejection_nesting V293_create_occupied_priority bp bc table bn p 0 slot _ _ ir si(true::ci) s
         ltac:(discriminate) Legal H). }
     eapply seq_rule.
     { apply V293_create_reject_if_false. intros s H.
       unfold V293_create_rejection_state in H. apply astar_l_aop'_elim in H. destruct H as[_ H].
       eapply V293_create_rejection_slot;[exact Legal|exact H]. }
     unfold V293_TaskCreateExt_occupied. eapply seq_rule.
     * eapply V293_create_enabled_exit;try eassumption.
       intros s H. apply Borrow.
       eapply astar_mono;[intros st HS;exact HS|apply V293_create_dynamic_occupied_close|exact H].
     * apply(V293_create_enabled_ret _ _ _ _ _ V293_create_occupied_priority).
 - eapply conseq_rule;[apply V293_create_dynamic_classify_positive;apply Views|intros s H;exact H| ].
   eapply r_conseq_rule with(r:=V293_create_enabled_return V293_create_from_isr bp bc p F aop ir si ci)(ri:=Afalse).
   + intro result. apply V293_create_dynamic_return_widen;auto.
   + intros s H;exact H.
   + eapply seq_rule with(p':=Afalse);[ |apply pfalse_rule].
     apply V293_create_reject_if_true.
     * intros s H. unfold V293_create_rejection_state in H.
       apply astar_l_aop'_elim in H. destruct H as[_ H].
       eapply V293_create_rejection_nesting with(k:=V293_create_from_isr)(p:=p)(n:=S n);[discriminate|cbn[V293_create_rejection_valid];lia|exact H].
     * unfold V293_TaskCreateExt_irq_error. eapply seq_rule.
       -- eapply V293_create_enabled_exit;try eassumption.
          intros s H. apply Borrow.
          eapply astar_mono;[intros st HS;exact HS|apply V293_create_dynamic_isr_close;exact NBound|exact H].
       -- apply(V293_create_enabled_ret _ _ _ _ _ V293_create_from_isr).
Qed.

Definition V293_create_dynamic_fpost R aop ir si ci(good:GoodFunAsrt R) : fpost :=
 fun vl result lg tid=>@mkfunasrt
 ([|result=Some(Vint32(Int.repr 60)) \/ result=Some(Vint32(Int.repr 40))|] **
 V293_create_enabled_external R aop ir si ci)
 (conj I(V293_create_enabled_external_good R aop ir si ci good)).
Lemma V293_create_dynamic_return_cells : forall target argv inputtop p identity bottom size ext options
 err psp bp bc R aop ir si ci result,
 V293_create_dynamic_return bp bc p
 (V293_create_reject_frame target argv inputtop identity bottom size ext options err psp R)aop ir si ci result ==>
 V293_create_internal_post_cells **
 ([|result=Some(Vint32(Int.repr 60)) \/ result=Some(Vint32(Int.repr 40))|] **
 V293_create_enabled_external R aop ir si ci) ** V293_create_internal_domain.
Proof.
 intros target argv inputtop p identity bottom size ext options err psp bp bc R aop ir si ci result s H.
 unfold V293_create_dynamic_return in H. apply astar_l_apure_elim in H. destruct H as[Code H].
 unfold V293_create_enabled_state,V293_create_enabled_locals,V293_create_reject_frame in H.
 assert(K:s |= ((Alvarenv 101%Z Tint8(bp,0%Z) ** Amapsto(bp,0%Z)Tint8 true(V293_byteval p)) **
 (Alvarenv 109%Z Tint32(bc,0%Z) ** Amapsto(bc,0%Z)Tint32 true(Vint32 Int.zero))) **
 (<||aop||> ** OS[ir,true,si,ci] ** R ** LV 209%Z @ Tint8 |->err **
 LV 108%Z @ (Tptr Tint32) |->psp **
 V293_create_internal_other_parameters target argv inputtop identity bottom size ext options ** V293_create_internal_domain)).
 { cbn[V293_rdy_raw_cells]in *;clear -H;sep auto. }
 eapply astar_mono in K;[ |apply astar_mono;apply V293_create_raw_local|intros st HS;exact HS].
 assert(Ret:s |= V293_create_internal_pre_cells target argv inputtop p identity bottom size ext options **
 (V293_create_enabled_external R aop ir si ci ** V293_create_internal_domain)).
 { unfold V293_create_internal_pre_cells,V293_create_internal_locals,V293_create_enabled_external,
 V293_create_internal_other_parameters in *;clear -K;sep auto. }
 eapply astar_mono in Ret;[ |apply V293_create_internal_pre_to_post|intros st HS;exact HS].
 clear -Ret Code;sep auto.
Qed.
Theorem V293_OSTaskCreateExt_dynamic_rejection_resources : forall Spec sd li I tid
 table bn p K R aop ir si ci(good:GoodFunAsrt R)
 target argv inputtop identity bottom size ext options sched hook tcb,
 p<13 -> (gettopis si<=INUM)%nat ->
 GoodFrm R -> (R ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) <==> Aisr ir ** V293_create_reject_pool table bn p K) ->
 InfRules Spec sd li I
 (fun result=>V293_create_internal_post_cells **
 getasrt(V293_create_dynamic_fpost R aop ir si ci good
 (V293_create_internal_values target argv inputtop p identity bottom size ext options)result[]tid) ** V293_create_internal_domain)Afalse
 (V293_create_internal_pre_cells target argv inputtop p identity bottom size ext options **
 V293_create_enabled_external R aop ir si ci ** V293_create_internal_domain)
 (V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z sched hook tcb)Afalse tid.
Proof.
 intros Spec sd li I tid table bn p K R aop ir si ci good target argv inputtop identity bottom size ext options sched hook tcb Range Bound Frame HR Borrow.
 eapply conseq_rule;[apply V293_create_internal_unpack|intros s H;exact H| ].
 apply ex_intro_rule. intro cpu. apply ex_intro_rule. intro err.
 apply ex_intro_rule. intro psp. apply ex_intro_rule. intro bp. apply ex_intro_rule. intro bc.
 eapply conseq_rule;[apply V293_create_enabled_entry|intros s H;exact H| ].
 eapply r_conseq_rule with(r:=V293_create_dynamic_return bp bc p
 (V293_create_reject_frame target argv inputtop identity bottom size ext options err psp R)aop ir si ci)(ri:=Afalse).
 - intro result. cbn[V293_create_dynamic_fpost getasrt]. apply V293_create_dynamic_return_cells.
 - intros s H;exact H.
 - eapply V293_OSTaskCreateExt_dynamic_rejection_body with(K:=K);try eassumption.
   + apply V293_create_reject_frame_good;exact Frame.
   + unfold V293_create_reject_frame. do 3 apply V293_star_CurLINV_r.
     apply V293_star_CurLINV_l. exact HR.
   + intro k. apply V293_create_enabled_frame_views.
Qed.

Theorem V293_OSTaskCreateExt_dynamic_rejection_contract : forall P creator Spec sd li I tid
 table bn p K R aop isr is cs(good:GoodFunAsrt R)
 target argv inputtop identity bottom size ext options sched hook tcb vl lg pre post,
 p<13 -> (gettopis is<=INUM)%nat -> GoodFrm R -> (R ==> CurLINV li tid) ->
 (Aisr isr ** invlth_isr I 0(gettopis is) <==> Aisr isr ** V293_create_reject_pool table bn p K) ->
 P creator=Some(V293_CreateExt_function 92%Z 99%Z 97%Z 98%Z sched hook tcb) ->
 Some pre=BuildPreI P creator vl lg
 (V293_create_enabled_fpre target argv inputtop p identity bottom size ext options R aop isr is cs good)tid ->
 Some post=BuildRetI P creator vl lg(V293_create_dynamic_fpost R aop isr is cs good)tid ->
 InfRules Spec sd li I post Afalse pre
 (V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z sched hook tcb)Afalse tid.
Proof.
 intros P creator Spec sd li I tid table bn p K R aop isr is cs good
 target argv inputtop identity bottom size ext options sched hook tcb vl lg pre post Range Bound Frame HR Borrow Code Pre Post.
 unfold BuildPreI in Pre. rewrite Code in Pre. cbn[V293_CreateExt_function]in Pre.
 destruct(dl_vl_match V293_CreateExt_parameters(rev vl))eqn:Typed;[ |discriminate].
 fold V293_create_internal_declarations in Pre.
 destruct(buildp V293_create_internal_declarations vl)as[owned | ]eqn:Owned;[ |discriminate].
 change(Some pre=Some(owned **
 ([|rev vl=V293_create_internal_values target argv inputtop p identity bottom size ext options|] **
 V293_create_enabled_external R aop isr is cs) ** V293_create_internal_domain))in Pre.
 inversion Pre;subst pre.
 unfold BuildRetI in Post. rewrite Code in Post.
 change(Some post=Some(fun result=>V293_create_internal_post_cells **
 getasrt(V293_create_dynamic_fpost R aop isr is cs good
 (V293_create_internal_values target argv inputtop p identity bottom size ext options)result[]tid) ** V293_create_internal_domain))in Post.
 inversion Post;subst post.
 eapply conseq_rule with(p:=(owned ** V293_create_enabled_external R aop isr is cs **
 V293_create_internal_domain) ** [|rev vl=V293_create_internal_values target argv inputtop p identity bottom size ext options|]).
 - intros s H. clear -H;sep auto.
 - intros s H;exact H.
 - apply pure_split_rule. intro Args.
   assert(VL:vl=rev(V293_create_internal_values target argv inputtop p identity bottom size ext options)).
   { rewrite <-Args. symmetry;apply rev_involutive. }
   subst vl. rewrite V293_create_internal_buildp in Owned. inversion Owned;subst owned.
   eapply V293_OSTaskCreateExt_dynamic_rejection_resources with(good:=good)(K:=K);eassumption.
Qed.

Print Assumptions V293_OSTaskCreateExt_dynamic_rejection_contract.
