(* Nullable shared pool for the actual allocation-branch reservation and stack call.
   This is a source fragment, not the whole function, WFIFun or a kernel invariant. *)
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateDynamicReject.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackCall.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
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

Definition V293_create_slot_value (slot:option addrval) : val :=
 match slot with None=>Vnull | Some a=>Vptr a end.
Definition V293_create_slot_cells (table bn:block) p n slot :=
 [((bn,0%Z),Tint8,V293_byteval n);
  ((table,(4*Z.of_nat p)%Z),Tptr V293_tcb_type,V293_create_slot_value slot)].
Definition V293_create_slot_globals table bn br :=
 V293_create_rejection_globals V293_create_occupied_priority table bn **
 Agvarenv 97%Z Tint8(br,0%Z).
Definition V293_create_slot_views table bn br :=
 V293_create_global_binding 99%Z Tint8 bn **
 V293_create_global_binding 92%Z(Tarray(Tptr V293_tcb_type)13)table **
 V293_create_global_binding 97%Z Tint8 br.
Definition V293_create_slot_owned table bn br p n slot K :=
 V293_rdy_raw_cells(V293_create_slot_cells table bn p n slot)
 (V293_create_slot_globals table bn br ** K).
Definition V293_create_nullable_pool table bn br p K :=
 EX n:nat, EX slot:option addrval, [|n<256|] **
 V293_create_slot_owned table bn br p n slot K.
Definition V293_create_slot_state bp bc table bn br p n slot cpu K F aop ir si ci :=
 <||aop||> ** V293_rdy_raw_cells
 ([((bp,0%Z),Tint8,V293_byteval p);((bc,0%Z),Tint32,cpu)]++
 V293_create_slot_cells table bn p n slot)
 (OS[ir,false,si,true::ci] **
 (Alvarenv 101%Z Tint8(bp,0%Z) ** Alvarenv 109%Z Tint32(bc,0%Z) **
 V293_create_slot_views table bn br ** K ** F)).

Lemma V293_create_slot_value_type : forall slot,
 rule_type_val_match(Tptr V293_tcb_type)(V293_create_slot_value slot)=true.
Proof. intros[slot| ];reflexivity. Qed.
Lemma V293_create_slot_drop_views : forall table bn br,
 V293_create_slot_views table bn br ==> V293_create_slot_globals table bn br.
Proof.
 intros table bn br. unfold V293_create_slot_views,V293_create_slot_globals,V293_create_global_binding.
 cbn[V293_create_rejection_globals].
 intros s H.
 assert(V:s |= Agvarenv 99%Z Tint8(bn,0%Z) **
 (Agvarenv 92%Z(Tarray(Tptr V293_tcb_type)13)(table,0%Z) ** Agvarenv 97%Z Tint8(br,0%Z))).
 { refine (@astar_mono _ _ _ _ _ _ s H).
   - intros st[G _];exact G.
   - apply astar_mono;intros st[G _];exact G. }
 clear -V;sep auto.
Qed.
(* Actual creator declaration domain rules out local shadowing of all three
   shared global names. No global-binding axiom is introduced. *)
Lemma V293_create_slot_global_views : forall table bn br,
 V293_create_slot_globals table bn br ** V293_create_internal_domain ==>
 V293_create_slot_views table bn br ** V293_create_internal_domain.
Proof.
 intros table bn br s H. unfold V293_create_slot_globals in H.
 cbn[V293_create_rejection_globals]in H.
 assert(K:s |= (Agvarenv 99%Z Tint8(bn,0%Z) ** V293_create_internal_domain) **
  (Agvarenv 92%Z(Tarray(Tptr V293_tcb_type)13)(table,0%Z) ** Agvarenv 97%Z Tint8(br,0%Z))).
 { clear -H;sep auto. }
 eapply astar_mono in K;[ |apply V293_create_success_global_view;lia|intros st HS;exact HS].
 assert(K2:s |= (Agvarenv 92%Z(Tarray(Tptr V293_tcb_type)13)(table,0%Z) ** V293_create_internal_domain) **
  (V293_create_global_binding 99%Z Tint8 bn ** Agvarenv 97%Z Tint8(br,0%Z))).
 { clear -K;sep auto. }
 eapply astar_mono in K2;[ |apply V293_create_success_global_view;lia|intros st HS;exact HS].
 assert(K3:s |= (Agvarenv 97%Z Tint8(br,0%Z) ** V293_create_internal_domain) **
  (V293_create_global_binding 99%Z Tint8 bn ** V293_create_global_binding 92%Z(Tarray(Tptr V293_tcb_type)13)table)).
 { clear -K2;sep auto. }
 eapply astar_mono in K3;[ |apply V293_create_success_global_view;lia|intros st HS;exact HS].
 unfold V293_create_slot_views. clear -K3;sep auto.
Qed.
Lemma V293_create_nullable_close : forall table bn br p n slot K,
 n<256 -> V293_create_slot_owned table bn br p n slot K ==>
 V293_create_nullable_pool table bn br p K.
Proof. intros table bn br p n slot K Bound s H. exists n. exists slot. sep auto. Qed.

Lemma V293_create_nullable_enter : forall Spec sd li I r ri tid
 bp bc table bn br p cpu K F aop ir si ci,
 (gettopis si<=INUM)%nat -> GoodFrm F ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==>
  Aisr ir ** V293_create_nullable_pool table bn br p K) ->
 (V293_create_slot_globals table bn br ** F ==>
  V293_create_slot_views table bn br ** F) ->
 InfRules Spec sd li I r ri
 (V293_create_enabled_state bp bc p cpu F aop ir si ci)(sprim encrit)
 (EX n:nat, EX slot:option addrval, [|n<256|] **
 V293_create_slot_state bp bc table bn br p n slot cpu K F aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid bp bc table bn br p cpu K F aop ir si ci Bound Frame Open Views.
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
   unfold V293_create_nullable_pool in B. sep normal in B. sep destruct B. sep split in B.
   assert(V:s |= (V293_create_slot_globals table bn br ** F) **
   (<||aop||> ** OS[ir,false,si,true::ci] **
    V293_rdy_raw_cells(V293_create_slot_cells table bn p x x0)K **
    V293_create_enabled_locals bp bc p cpu Aemp)).
   { unfold V293_create_slot_owned,V293_create_enabled_locals in *.
     cbn[V293_rdy_raw_cells V293_create_slot_cells]in *;sep auto. }
   eapply astar_mono in V;[ |exact Views|intros st HS;exact HS].
   exists x. exists x0. apply astar_l_apure_intro;[ |assumption].
   unfold V293_create_slot_state,V293_create_enabled_locals in *.
   cbn[V293_rdy_raw_cells V293_create_slot_cells app]in *;clear -V;sep auto.
 - apply encrit1_rule. apply V293_create_enabled_good;exact Frame.
Qed.

Lemma V293_create_nullable_exit : forall Spec sd li I r ri tid
 bp bc table bn br p n slot cpu K F aop ir si ci,
 n<256 -> GoodFrm F -> (F ==> CurLINV li tid) ->
 (Aisr ir ** V293_create_nullable_pool table bn br p K ==>
  Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_create_slot_state bp bc table bn br p n slot cpu K F aop ir si ci)(sprim excrit)
 (V293_create_enabled_state bp bc p cpu F aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid bp bc table bn br p n slot cpu K F aop ir si ci Bound Frame HR Close.
 eapply conseq_rule with
 (p:=<||aop||> ** OS[ir,false,si,true::ci] ** ATopis(gettopis si) ** invlth_isr I 0(gettopis si) **
 V293_create_enabled_locals bp bc p cpu F)
 (q:=<||aop||> ** OS[ir,true,si,ci] ** V293_create_enabled_locals bp bc p cpu F).
 - intros s H. unfold V293_create_slot_state in H.
   assert(V:s |= V293_create_slot_views table bn br **
    (<||aop||> ** OS[ir,false,si,true::ci] **
     V293_rdy_raw_cells(V293_create_slot_cells table bn p n slot)K **
     V293_create_enabled_locals bp bc p cpu F)).
   { unfold V293_create_enabled_locals. cbn[V293_rdy_raw_cells V293_create_slot_cells app]in *;clear -H;sep auto. }
   eapply astar_mono in V;[ |apply V293_create_slot_drop_views|intros st HS;exact HS].
   assert(B:s |= (Aisr ir ** V293_create_nullable_pool table bn br p K) **
    (<||aop||> ** Aie false ** Ais si ** Acs(true::ci) ** V293_create_enabled_locals bp bc p cpu F)).
   { eapply astar_mono;[apply astar_mono;[intros st HS;exact HS|apply V293_create_nullable_close;exact Bound]|intros st HS;exact HS| ].
     unfold V293_create_slot_owned. cbn[V293_rdy_raw_cells V293_create_slot_cells]in *;clear -V;sep auto. }
   eapply astar_mono in B;[ |exact Close|intros st HS;exact HS].
   assert(S:s |= Ais si ** Atrue)by(clear -B;sep auto).
   pose proof(V293_time_topis si Atrue s S)as Top.
   apply astar_l_atopis_elim in Top. destruct Top as[Top _].
   pose proof(@astar_l_atopis_intro s(gettopis si)_ B Top)as HT. clear -HT;sep auto.
 - unfold V293_create_enabled_state. intros s H;exact H.
 - apply excrit1_rule.
   + apply V293_create_enabled_good;exact Frame.
   + unfold V293_create_enabled_locals. do 2 apply V293_star_CurLINV_r.
     do 2 apply V293_star_CurLINV_r. exact HR.
Qed.

Lemma V293_create_slot_prefix_zero : forall bp bc table bn br p slot cpu K F aop ir si ci,
 V293_create_slot_state bp bc table bn br p 0 slot cpu K F aop ir si ci <==>
 V293_create_prefix_state bp bn bc table 99%Z 97%Z br p cpu(V293_create_slot_value slot)
 (K ** F)aop ir si(true::ci).
Proof.
 intros bp bc table bn br p slot cpu K F aop ir si ci s.
 unfold V293_create_slot_state,V293_create_prefix_state,V293_create_prefix_cells,
 V293_create_prefix_bindings,V293_create_slot_views,V293_tcb_table_binding,V293_create_global_binding.
 cbn[V293_rdy_raw_cells V293_create_slot_cells app]. split;intro H;sep auto.
Qed.

Theorem V293_OSTaskCreateExt_enabled_reservation : forall Spec sd li I r ri tid
 bp bc table bn br p cpu K F aop ir si ci,
 p<13 -> GoodFrm F -> (F ==> CurLINV li tid) ->
 (Aisr ir ** V293_create_nullable_pool table bn br p K ==>
  Aisr ir ** invlth_isr I 0(gettopis si)) ->
 InfRules Spec sd li I r ri
 (V293_create_slot_state bp bc table bn br p 0 None cpu K F aop ir si ci)
 (sseq(sassign(earrayelem(evar 92%Z)(evar 101%Z))(V293_task_prio_reserved_expr 97%Z))(sprim excrit))
 (V293_create_enabled_state bp bc p cpu F aop ir si ci)tid.
Proof.
 intros Spec sd li I r ri tid bp bc table bn br p cpu K F aop ir si ci Range Frame HR Close.
 eapply seq_rule with(p':=V293_create_slot_state bp bc table bn br p 0(Some(br,Int.zero))cpu K F aop ir si ci).
 - eapply conseq_rule;[apply V293_create_slot_prefix_zero|intros s H;apply V293_create_slot_prefix_zero;exact H| ].
   apply V293_create_prefix_reserve_hoare;[exact Range|apply V293_star_CurLINV_r;exact HR].
 - apply V293_create_nullable_exit;[lia|exact Frame|exact HR|exact Close].
Qed.
Print Assumptions V293_OSTaskCreateExt_enabled_reservation.

(* This is the literal contiguous NULL-branch fragment, ending immediately
   after the real Hook call. It is NOT the whole prefix with a truncated
   suffix: that would fall through to the occupied-priority error branch. *)
Theorem V293_OSTaskCreateExt_enabled_stack_fragment : forall Spec sd li I r ri tid hook
 bp bc table bn br p cpu K F Rbefore Rafter aop ir si ci
 (BeforeGood:GoodFunAsrt Rbefore)(AfterGood:GoodFunAsrt Rafter)
 target argv inputtop options stack oldpsp,
 p<13 -> GoodFrm F -> GoodFrm Rbefore ->
 V293_stack_argument_valid argv inputtop options ->
 (Rbefore ==> CurLINV li tid) -> (Rafter ==> CurLINV li tid) ->
 (Aisr ir ** V293_create_nullable_pool table bn br p K ==>
  Aisr ir ** invlth_isr I 0(gettopis si)) ->
 let before:=@mkfunasrt (V293_create_enabled_external Rbefore aop ir si ci)
   (V293_create_enabled_external_good Rbefore aop ir si ci BeforeGood) in
 let after:=@mkfunasrt (V293_create_enabled_external Rafter aop ir si ci)
   (V293_create_enabled_external_good Rafter aop ir si ci AfterGood) in
 Spec hook=Some(V293_create_stack_resource_fpre before(V293_create_stack_values target argv inputtop options),
 V293_create_stack_resource_fpost after(V293_create_stack_values target argv inputtop options)stack,
 (Tptr Tint32,rev V293_stack_argument_types)) ->
 InfRules Spec sd li I r ri
 (V293_create_slot_state bp bc table bn br p 0 None cpu K
  (LV 108%Z @ (Tptr Tint32) |->oldpsp **
   V293_create_stack_arguments target argv inputtop options(Rbefore ** F))aop ir si ci)
 (sseq(sassign(earrayelem(evar 92%Z)(evar 101%Z))(V293_task_prio_reserved_expr 97%Z))
  (sseq(sprim excrit)(V293_TaskCreateExt_stack_call 108%Z hook 201%Z 202%Z 203%Z 204%Z)))
 (V293_create_enabled_external Rafter aop ir si ci **
  LV 108%Z @ (Tptr Tint32) |->stack **
  V293_create_stack_arguments target argv inputtop options
   (V293_create_enabled_locals bp bc p cpu F))tid.
Proof.
 intros Spec sd li I r ri tid hook bp bc table bn br p cpu K F Rbefore Rafter aop ir si ci
 BeforeGood AfterGood target argv inputtop options stack oldpsp
 Range Frame ResourceFrame Valid Before After Close before after Lookup.
 eapply seq_rule with(p':=V293_create_slot_state bp bc table bn br p 0(Some(br,Int.zero))cpu K
  (LV 108%Z @ (Tptr Tint32) |->oldpsp **
   V293_create_stack_arguments target argv inputtop options(Rbefore ** F))aop ir si ci).
 - eapply conseq_rule;[apply V293_create_slot_prefix_zero|intros s H;apply V293_create_slot_prefix_zero;exact H| ].
   apply V293_create_prefix_reserve_hoare;[exact Range| ].
   apply V293_star_CurLINV_r. apply V293_star_CurLINV_r.
   unfold V293_create_stack_arguments. do 4 apply V293_star_CurLINV_r.
   apply V293_star_CurLINV_l;exact Before.
 - eapply seq_rule with(p':=V293_create_enabled_state bp bc p cpu
   (LV 108%Z @ (Tptr Tint32) |->oldpsp **
    V293_create_stack_arguments target argv inputtop options(Rbefore ** F))aop ir si ci).
   + apply V293_create_nullable_exit.
     * lia.
     * unfold V293_create_stack_arguments,Alvarmapsto,Alvarenv',Aptrmapsto.
       cbn[GoodFrm]. tauto.
     * apply V293_star_CurLINV_r. unfold V293_create_stack_arguments.
       do 4 apply V293_star_CurLINV_r. apply V293_star_CurLINV_l;exact Before.
     * exact Close.
   + eapply conseq_rule with
     (p:=getasrt before ** LV 108%Z @ (Tptr Tint32) |->oldpsp **
       V293_create_stack_arguments target argv inputtop options(V293_create_enabled_locals bp bc p cpu F))
     (q:=getasrt after ** LV 108%Z @ (Tptr Tint32) |->stack **
       V293_create_stack_arguments target argv inputtop options(V293_create_enabled_locals bp bc p cpu F)).
     * unfold before,V293_create_enabled_state,V293_create_enabled_locals,
       V293_create_enabled_external,V293_create_stack_arguments. cbn[getasrt V293_rdy_raw_cells].
       intros s H;sep auto.
     * unfold after. cbn[getasrt]. intros s H;exact H.
     * eapply V293_OSTaskCreateExt_stack_resource_call_hoare.
       -- apply V293_create_enabled_good;exact Frame.
       -- exact Valid.
       -- unfold before,V293_create_enabled_external. cbn[getasrt].
          do 2 apply V293_star_CurLINV_r. exact Before.
       -- unfold after,V293_create_enabled_external. cbn[getasrt].
          do 2 apply V293_star_CurLINV_r. exact After.
       -- exact Lookup.
Qed.
Print Assumptions V293_OSTaskCreateExt_enabled_stack_fragment.
