(* Actual right-associated NULL allocation branch through failure return.
   The caller-held RESERVED half is created by the store, framed across both
   calls, and consumed by rollback. This is not the enabled whole function. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEnabledReject.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateBodyFailure.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEnabledFailure.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateFailureHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEnabledSlotPool.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReservationOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateRejectInternal.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtFunction.

Definition V293_create_owned_empty_aux bf bottom identity size ext olderr F :=
 LV 209%Z @ Tint8 |->olderr **
 LV 205%Z @ (Tptr Tint32) |->bottom **
 LV 206%Z @ Tint16 |->identity ** LV 207%Z @ Tint32 |->size **
 LV 208%Z @ (Tptr Tvoid) |->ext **
 (Agvarenv 91%Z (Tptr V293_tcb_type)(bf,0%Z) ** F).
Definition V293_create_owned_empty_kept bn br cpu target argv inputtop F :=
 LV 109%Z @ Tint32 |->cpu **
 V293_create_stack_kept target argv inputtop
 (V293_create_global_binding 99%Z Tint8 bn **
  V293_create_global_binding 97%Z Tint8 br ** F).

Lemma V293_create_owned_empty_seam : forall bp bc bf table bn br p cpu stack
 target argv inputtop options bottom identity size ext olderr R F aop ir si ci,
 V293_create_enabled_external R aop ir si ci **
 LV 108%Z @ (Tptr Tint32) |->stack **
 V293_create_stack_arguments target argv inputtop options
  (V293_create_enabled_locals bp bc p cpu
   (V293_create_owned_share table(br,Int.zero)p ** V293_create_slot_views table bn br **
    V293_create_owned_empty_aux bf bottom identity size ext olderr F)) ==>
 V293_tcb_enabled_external bf R aop ir si ci ** LV 209%Z @ Tint8 |->olderr **
 V293_create_tcb_arguments p stack bottom identity size ext options
  (V293_tcb_table_binding table ** (V293_create_owned_share table(br,Int.zero)p **
   V293_create_owned_empty_kept bn br cpu target argv inputtop F)).
Proof.
 intros bp bc bf table bn br p cpu stack target argv inputtop options bottom identity size ext olderr R F aop ir si ci s H.
 unfold V293_create_enabled_external,V293_create_enabled_locals,
  V293_create_stack_arguments,V293_create_slot_views,V293_create_owned_empty_aux in H.
 cbn[V293_rdy_raw_cells]in H.
 assert(P:s |= (Alvarenv 101%Z Tint8(bp,0%Z) ** Amapsto(bp,0%Z)Tint8 true(V293_byteval p)) **
  ((Alvarenv 109%Z Tint32(bc,0%Z) ** Amapsto(bc,0%Z)Tint32 true cpu) **
   (<||aop||> ** OS[ir,true,si,ci] ** R **
    LV 108%Z @ (Tptr Tint32) |->stack **
    LV 201%Z @ Tint32 |->V293_task_selector target **
    LV 202%Z @ (Tptr Tvoid) |->argv ** LV 203%Z @ (Tptr Tint32) |->inputtop **
    LV 204%Z @ Tint16 |->options ** LV 209%Z @ Tint8 |->olderr **
    LV 205%Z @ (Tptr Tint32) |->bottom ** LV 206%Z @ Tint16 |->identity **
    LV 207%Z @ Tint32 |->size ** LV 208%Z @ (Tptr Tvoid) |->ext **
    Agvarenv 91%Z(Tptr V293_tcb_type)(bf,0%Z) **
    V293_create_owned_share table(br,Int.zero)p **
    V293_create_global_binding 99%Z Tint8 bn **
    V293_create_global_binding 92%Z(Tarray(Tptr V293_tcb_type)13)table **
    V293_create_global_binding 97%Z Tint8 br ** F))).
 { clear -H;sep auto. }
 eapply astar_mono in P;[ |apply V293_create_raw_local|intros st HS;exact HS].
 eapply astar_mono in P;[ |intros st HS;exact HS|apply astar_mono;[apply V293_create_raw_local|intros st HS;exact HS]].
 unfold V293_tcb_enabled_external,V293_create_tcb_arguments,
  V293_create_owned_empty_kept,V293_create_stack_kept,V293_tcb_table_binding,
  V293_create_global_binding in *.
 clear -P;sep auto.
Qed.

Theorem V293_OSTaskCreateExt_owned_empty_branch : forall Spec sd li I tid hook f
 bp bc bf table bn br p cpu K F Rbefore Rafter aop ir si ci
 (BeforeGood:GoodFunAsrt Rbefore)(AfterGood:GoodFunAsrt Rafter)
 target argv inputtop options stack oldpsp bottom identity size ext olderr running sched,
 p<13 -> (gettopis si<=INUM)%nat ->
 GoodFrm F -> GoodFrm Rbefore -> GoodFrm Rafter ->
 V293_stack_argument_valid argv inputtop options ->
 V293_tcb_init_values_valid stack bottom identity size ext options ->
 (Rbefore ==> CurLINV li tid) -> (Rafter ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==>
  Aisr ir ** V293_create_owned_pool table(br,Int.zero)p
   (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) ** K)) ->
 (Aisr ir ** V293_create_owned_pool table(br,Int.zero)p
   (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) ** K) ==>
  Aisr ir ** invlth_isr I 0(gettopis si)) ->
 let before:=@mkfunasrt (V293_create_enabled_external Rbefore aop ir si ci)
   (V293_create_enabled_external_good Rbefore aop ir si ci BeforeGood) in
 let after:=@mkfunasrt (V293_create_enabled_external Rafter aop ir si ci)
   (V293_create_enabled_external_good Rafter aop ir si ci AfterGood) in
 Spec hook=Some(V293_create_stack_resource_fpre before(V293_create_stack_values target argv inputtop options),
 V293_create_stack_resource_fpost after(V293_create_stack_values target argv inputtop options)stack,
 (Tptr Tint32,rev V293_stack_argument_types)) ->
 Spec f=Some(V293_tcb_enabled_fpre bf Rafter aop ir si ci AfterGood,
  V293_tcb_enabled_fpost bf Rafter aop ir si ci AfterGood,(Tint8,rev V293_TCBInit_argument_types)) ->
 InfRules Spec sd li I
 (V293_create_enabled_failure_return table p
  (V293_create_enabled_failure_kept bf stack bottom identity size ext options Rafter
   (V293_create_owned_empty_kept bn br cpu target argv inputtop F))aop ir si ci)Afalse
 (V293_create_slot_state bp bc table bn br p 0 None cpu K
  (LV 108%Z @ (Tptr Tint32) |->oldpsp **
   V293_create_stack_arguments target argv inputtop options
    (Rbefore ** V293_create_owned_empty_aux bf bottom identity size ext olderr F))aop ir si ci)
 (sseq(sassign(earrayelem(evar 92%Z)(evar 101%Z))(V293_task_prio_reserved_expr 97%Z))
  (sseq(sprim excrit)
   (V293_TaskCreateExt_calls 108%Z hook 201%Z 202%Z 203%Z 204%Z 209%Z f 101%Z 205%Z 206%Z 207%Z 208%Z
    (V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z running sched))))Afalse tid.
Proof.
 intros Spec sd li I tid hook f bp bc bf table bn br p cpu K F Rbefore Rafter aop ir si ci
 BeforeGood AfterGood target argv inputtop options stack oldpsp bottom identity size ext olderr running sched
 Range Bound Frame BeforeFrame AfterFrame StackValid TCBValid Before After Open Close before after Hook TCB.
 eapply seq_rule with(p':=V293_create_slot_state bp bc table bn br p 0(Some(br,Int.zero))cpu K
  (LV 108%Z @ (Tptr Tint32) |->oldpsp **
   V293_create_stack_arguments target argv inputtop options(Rbefore ** V293_create_owned_empty_aux bf bottom identity size ext olderr F))aop ir si ci).
 - eapply conseq_rule;[apply V293_create_slot_prefix_zero|intros s H;apply V293_create_slot_prefix_zero;exact H| ].
   apply V293_create_prefix_reserve_hoare;[exact Range| ].
   apply V293_star_CurLINV_r. apply V293_star_CurLINV_r.
   unfold V293_create_stack_arguments. do 4 apply V293_star_CurLINV_r.
   apply V293_star_CurLINV_l;exact Before.
 - eapply seq_rule with(p':=V293_create_enabled_state bp bc p cpu
   (V293_create_owned_share table(br,Int.zero)p ** V293_create_slot_views table bn br **
   (LV 108%Z @ (Tptr Tint32) |->oldpsp **
    V293_create_stack_arguments target argv inputtop options(Rbefore ** V293_create_owned_empty_aux bf bottom identity size ext olderr F)))aop ir si ci).
   + apply V293_create_reservation_owned_exit.
     * unfold V293_create_stack_arguments,V293_create_owned_empty_aux,Alvarmapsto,Alvarenv',Aptrmapsto.
       cbn[GoodFrm]. tauto.
     * apply V293_star_CurLINV_r. unfold V293_create_stack_arguments.
       do 4 apply V293_star_CurLINV_r. apply V293_star_CurLINV_l;exact Before.
     * exact Close.
   + unfold V293_TaskCreateExt_calls. eapply seq_rule.
     * eapply conseq_rule with
       (p:=getasrt before ** LV 108%Z @ (Tptr Tint32) |->oldpsp **
        V293_create_stack_arguments target argv inputtop options(V293_create_enabled_locals bp bc p cpu
         (V293_create_owned_share table(br,Int.zero)p ** V293_create_slot_views table bn br **
          V293_create_owned_empty_aux bf bottom identity size ext olderr F)))
       (q:=getasrt after ** LV 108%Z @ (Tptr Tint32) |->stack **
        V293_create_stack_arguments target argv inputtop options(V293_create_enabled_locals bp bc p cpu
         (V293_create_owned_share table(br,Int.zero)p ** V293_create_slot_views table bn br **
          V293_create_owned_empty_aux bf bottom identity size ext olderr F))).
       -- unfold before,V293_create_enabled_state,V293_create_enabled_locals,
           V293_create_enabled_external,V293_create_stack_arguments. cbn[getasrt V293_rdy_raw_cells].
          intros s H;sep auto.
       -- unfold after. cbn[getasrt]. intros s H;exact H.
       -- eapply V293_OSTaskCreateExt_stack_resource_call_hoare.
          ++ apply V293_create_enabled_good.
             unfold V293_create_owned_share,V293_reservation_owner,V293_create_slot_views,V293_create_global_binding,
              V293_create_owned_empty_aux,Alvarmapsto,Alvarenv',Aptrmapsto.
             cbn[GoodFrm];tauto.
          ++ exact StackValid.
          ++ unfold before,V293_create_enabled_external. cbn[getasrt].
             do 2 apply V293_star_CurLINV_r. exact Before.
          ++ unfold after,V293_create_enabled_external. cbn[getasrt].
             do 2 apply V293_star_CurLINV_r. exact After.
          ++ exact Hook.
     * eapply conseq_rule.
       -- apply V293_create_owned_empty_seam.
       -- intros s H;exact H.
       -- apply V293_OSTaskCreateExt_owned_empty_call_suffix with
           (good:=AfterGood)(K:=Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) ** K).
          ++ exact Range.
          ++ exact Bound.
          ++ exact AfterFrame.
          ++ unfold V293_create_owned_empty_kept,V293_create_stack_kept,V293_create_global_binding,
              Alvarmapsto,Alvarenv',Aptrmapsto. cbn[GoodFrm];tauto.
          ++ exact TCBValid.
          ++ exact After.
          ++ exact Open.
          ++ exact Close.
          ++ exact TCB.
Qed.

(* This tail is definitionally the untouched body after its first encrit. *)
Definition V293_create_owned_empty_tail hook f running sched :=
 sseq(sifthen(ebinop olt(econst32 Int.zero)(ecast(evar 99%Z)Tint32))
  V293_TaskCreateExt_irq_error)
 (sseq(sifthen(ebinop oeq(earrayelem(evar 92%Z)(evar 101%Z))
   (ecast enull(Tptr V293_tcb_type)))
  (sseq(sassign(earrayelem(evar 92%Z)(evar 101%Z))(V293_task_prio_reserved_expr 97%Z))
   (sseq(sprim excrit)
    (V293_TaskCreateExt_calls 108%Z hook 201%Z 202%Z 203%Z 204%Z 209%Z f 101%Z 205%Z 206%Z 207%Z 208%Z
     (V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z running sched)))))
  V293_TaskCreateExt_occupied).
Lemma V293_create_owned_empty_tail_source : forall hook f running sched,
 V293_CreateExt_body 92%Z 99%Z 97%Z running sched hook f =
 sseq(sassign(evar 109%Z)(econst32 Int.zero))
 (sseq(sifthen(ebinop olt(econst32(Int.repr 12))(ecast(evar 101%Z)Tint32))
  (srete(econst32(Int.repr 42))))
 (sseq(sprim encrit)(V293_create_owned_empty_tail hook f running sched))).
Proof. reflexivity. Qed.

Lemma V293_create_owned_empty_guards : forall bp bc table bn br p cpu K F aop ir si ci s,
 p<13 -> s |= V293_create_slot_state bp bc table bn br p 0 None cpu K F aop ir si ci ->
 (evalval(ebinop olt(econst32 Int.zero)(ecast(evar 99%Z)Tint32))(getsmem s)=Some(Vint32 Int.zero) /\
  evaltype(ebinop olt(econst32 Int.zero)(ecast(evar 99%Z)Tint32))(getsmem s)=Some Tint32) /\
 (evalval(ebinop oeq(earrayelem(evar 92%Z)(evar 101%Z))(ecast enull(Tptr V293_tcb_type)))(getsmem s)=Some(Vint32 Int.one) /\
  evaltype(ebinop oeq(earrayelem(evar 92%Z)(evar 101%Z))(ecast enull(Tptr V293_tcb_type)))(getsmem s)=Some Tint32).
Proof.
 intros bp bc table bn br p cpu K F aop ir si ci s Range H.
 apply V293_create_slot_prefix_zero in H.
 unfold V293_create_prefix_state in H. apply astar_l_aop'_elim in H. destruct H as[_ H].
 exact(proj2(V293_create_prefix_guards _ _ _ _ _ _ _ _ _ _ _ _ _ _ Range H)).
Qed.

Theorem V293_OSTaskCreateExt_owned_empty_critical_tail : forall Spec sd li I tid hook f
 bp bc bf table bn br p cpu K F Rbefore Rafter aop ir si ci
 (BeforeGood:GoodFunAsrt Rbefore)(AfterGood:GoodFunAsrt Rafter)
 target argv inputtop options stack oldpsp bottom identity size ext olderr running sched,
 p<13 -> (gettopis si<=INUM)%nat ->
 GoodFrm F -> GoodFrm Rbefore -> GoodFrm Rafter ->
 V293_stack_argument_valid argv inputtop options ->
 V293_tcb_init_values_valid stack bottom identity size ext options ->
 (Rbefore ==> CurLINV li tid) -> (Rafter ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==>
  Aisr ir ** V293_create_owned_pool table(br,Int.zero)p
   (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) ** K)) ->
 (Aisr ir ** V293_create_owned_pool table(br,Int.zero)p
   (Amapsto(bn,0%Z)Tint8 true(V293_byteval 0) ** K) ==>
  Aisr ir ** invlth_isr I 0(gettopis si)) ->
 let before:=@mkfunasrt (V293_create_enabled_external Rbefore aop ir si ci)
   (V293_create_enabled_external_good Rbefore aop ir si ci BeforeGood) in
 let after:=@mkfunasrt (V293_create_enabled_external Rafter aop ir si ci)
   (V293_create_enabled_external_good Rafter aop ir si ci AfterGood) in
 Spec hook=Some(V293_create_stack_resource_fpre before(V293_create_stack_values target argv inputtop options),
 V293_create_stack_resource_fpost after(V293_create_stack_values target argv inputtop options)stack,
 (Tptr Tint32,rev V293_stack_argument_types)) ->
 Spec f=Some(V293_tcb_enabled_fpre bf Rafter aop ir si ci AfterGood,
  V293_tcb_enabled_fpost bf Rafter aop ir si ci AfterGood,(Tint8,rev V293_TCBInit_argument_types)) ->
 InfRules Spec sd li I
 (V293_create_enabled_failure_return table p
  (V293_create_enabled_failure_kept bf stack bottom identity size ext options Rafter
   (V293_create_owned_empty_kept bn br cpu target argv inputtop F))aop ir si ci)Afalse
 (V293_create_slot_state bp bc table bn br p 0 None cpu K
  (LV 108%Z @ (Tptr Tint32) |->oldpsp **
   V293_create_stack_arguments target argv inputtop options
    (Rbefore ** V293_create_owned_empty_aux bf bottom identity size ext olderr F))aop ir si ci)
 (V293_create_owned_empty_tail hook f running sched)Afalse tid.
Proof.
 intros Spec sd li I tid hook f bp bc bf table bn br p cpu K F Rbefore Rafter aop ir si ci
 BeforeGood AfterGood target argv inputtop options stack oldpsp bottom identity size ext olderr running sched
 Range Bound Frame BeforeFrame AfterFrame StackValid TCBValid Before After Open Close before after Hook TCB.
 unfold V293_create_owned_empty_tail.
 eapply seq_rule.
 - apply V293_create_reject_if_false. intros s H.
   exact(proj1(V293_create_owned_empty_guards _ _ _ _ _ _ _ _ _ _ _ _ _ _ Range H)).
 - eapply seq_rule with(p':=Afalse).
   + apply V293_create_reject_if_true.
     * intros s H. exact(proj2(V293_create_owned_empty_guards _ _ _ _ _ _ _ _ _ _ _ _ _ _ Range H)).
     * eapply V293_OSTaskCreateExt_owned_empty_branch; eassumption.
   + apply pfalse_rule.
Qed.
