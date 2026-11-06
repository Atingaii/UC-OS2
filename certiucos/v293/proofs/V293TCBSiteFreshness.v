(* RESERVED distinctness is a static fact about the real table catalogue.
   The original allocator supplies NodeMember; no arbitrary-state Fresh oracle.
   GoodI and external Hook implementation obligations are still explicit. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteAllocator.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBFinitePool.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitChain.
Require Import CertiOS.certiucos.v293.proofs.V293InitMisc.
Require Import CertiOS.certiucos.v293.code.V293OSInitChain.
Require Import CertiOS.certiucos.v293.code.V293OSInitRdyList.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBCall.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TCBAllocatedFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEnabledHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFullPriority.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteSites.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublicationPool.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEnabledPublication.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFreePool.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReservationOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Require Import CertiOS.certiucos.v293.proofs.V293TCBJointShared.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEnabledOwned.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEnabledSlotPool.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEnabledFailure.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEnabledReject.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackSuccess.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateJointShared.
Require Import CertiOS.certiucos.v293.proofs.V293TCBOwnedPriority.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookFrame.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublishHoare.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.tactics.hoareforward.init_spec.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBCall.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSharedContract.
Import ListNotations.
Local Open Scope nat_scope.

Lemma V293_tcb_site_reserved_distinct : forall bt reserved node,
 ~In reserved(V293_tcb_table_sites bt) ->
 In node(V293_tcb_table_sites bt) -> node<>reserved.
Proof. intros bt reserved node Outside Member Equal;subst node;contradiction. Qed.

Lemma V293_tcb_site_reserved_other_block : forall bt rb ro,
 bt<>rb -> ~In(rb,ro)(V293_tcb_table_sites bt).
Proof.
 intros bt rb ro Different Member. unfold V293_tcb_table_sites in Member.
 apply in_map_iff in Member. destruct Member as[i[Equal Range]].
 inversion Equal;contradiction.
Qed.

Theorem V293_OS_TCBInit_site_fresh_body : forall Spec sd li I r tid hi hc tcbtable
 table reserved bf bp bc pc cpu Kfree Kprio Kpub bh bg br bn bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci
 (good:GoodFunAsrt(V293_create_owned_share table reserved p ** R)),
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm R ->
 V293_tcb_init_values_valid top bottom identity size ext options -> (R ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** (V293_tcb_site_free_pool tcbtable bf ** Kfree)) ->
 (Aisr ir ** (V293_tcb_site_free_pool tcbtable bf ** Kfree) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** V293_create_owned_pool table reserved p Kprio) ->
 (Aisr ir ** V293_create_owned_pool table reserved p Kprio ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 Spec hi=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** R)aop ir si ci tid good,
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** R)aop ir si ci tid good,(Tvoid,[Tptr V293_tcb_type])) ->
 Spec hc=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options R aop ir si ci tid (proj2 good),
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options R aop ir si ci tid (proj2 good),(Tvoid,[Tptr V293_tcb_type])) ->
 (V293_tcb_enabled_state bf bp bc Vnull(Vint32 Int.zero)
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))))aop ir si ci ==>
 r(Some(Vint32(Int.repr 66)))) ->
 (~In reserved(V293_tcb_table_sites tcbtable)) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==>
 Aisr ir ** (V293_tcb_finite_shared tcbtable bh bg br bn(V293_prio_row p) ** Kpub)) ->
 (Aisr ir ** (V293_tcb_finite_shared tcbtable bh bg br bn(V293_prio_row p) ** Kpub) ==>
 Aisr ir ** invlth_isr I 0(gettopis si)) ->
 (forall b off,
 V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_tcb_publication_globals bh bg br bn ** R)))aop ir si ci ==>
 r(Some(Vint32 Int.zero))) ->
 InfRules Spec sd li I r Afalse
 (V293_tcb_enabled_state bf bp bc pc cpu
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))))aop ir si ci)
 (V293_TCBInit_function_body hi hc)Afalse tid.
Proof.
 intros Spec sd li I r tid hi hc tcbtable table reserved bf bp bc pc cpu Kfree Kprio Kpub bh bg br bn bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci good Range Bound Frame Valid HR FreeOpen FreeClose PriorityOpen PriorityClose FirstLookup SecondLookup Empty Outside PubOpen PubClose Return.
 assert(PF:GoodFrm(V293_tcb_publication_globals bh bg br bn ** R))by(cbn[V293_tcb_publication_globals GoodFrm];tauto).
 assert(InputFrame:GoodFrm(V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R)))).
 { unfold V293_tcb_table_binding,V293_create_owned_share,V293_reservation_owner;cbn[GoodFrm];tauto. }
 assert(InputLinv:(V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))) ==> CurLINV li tid).
 { repeat apply V293_star_CurLINV_r;exact HR. }
 apply V293_OS_TCBInit_site_free_body_with_success with(tcbtable:=tcbtable)(K:=Kfree);try assumption.
 - apply V293_tcb_allocated_inputs_good;exact InputFrame.
 - apply V293_tcb_allocated_inputs_linv;exact InputLinv.
 - intros b off next NodeMember NodeBound NextTyped.
   eapply seq_rule;[apply V293_tcb_allocated_fields;assumption| ].
   eapply conseq_rule with
   (p:=V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
    (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
     V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
     (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))))aop ir si ci **
     [|(b,off)<>reserved|]).
   + intros s H. apply astar_comm. apply astar_l_apure_intro;[exact H|eapply V293_tcb_site_reserved_distinct;[exact Outside|exact NodeMember]].
   + intros s H;exact H.
   + apply pure_split_rule. intro Distinct.
     eapply conseq_rule with
     (p:=V293_tcb_priority_state table bprio bp p(Vptr(b,off))
       (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
       ((V293_create_owned_share table reserved p ** R) **
        (V293_tcb_publication_globals bh bg br bn ** V293_tcb_priority_caller_frame bf bp bc bprio bs bb bi bz be bo(Vint32 Int.zero)top bottom identity size ext options)))aop ir true si ci).
     * intros s H. apply V293_tcb_full_priority_view in H.
       unfold V293_tcb_priority_state,V293_tcb_priority_resources in *.
       cbn[V293_tcb_priority_locals V293_rdy_raw_cells]in *;clear -H;sep auto.
     * intros s H;exact H.
     * apply V293_OS_TCBInit_owned_suffix_after_first_hook with(reserved:=reserved)(K:=Kprio)(good:=good);try assumption.
       -- cbn[GoodFrm]. split;[cbn[V293_tcb_publication_globals GoodFrm];tauto|apply V293_tcb_priority_caller_frame_good].
       -- eapply seq_rule.
          ++ apply V293_tcb_priority_first_hook with(good:=proj2 good);try assumption.
             cbn[GoodFrm]. split;[cbn[V293_tcb_publication_globals GoodFrm];tauto|apply V293_tcb_priority_caller_frame_good].
          ++ eapply conseq_rule with
             (p:=V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
              (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
               V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
               (V293_tcb_table_binding table ** (V293_tcb_publication_globals bh bg br bn ** R)))aop ir si ci).
             ** intros s H. apply V293_tcb_full_priority_restore.
                unfold V293_tcb_priority_state,V293_tcb_priority_resources in *.
                cbn[V293_tcb_priority_locals V293_rdy_raw_cells]in *;clear -H;sep auto.
             ** intros s H;exact H.
             ** eapply conseq_rule;[apply V293_tcb_full_publication_view;assumption|intros s H;exact H| ].
          apply ex_intro_rule. intro prev.
          apply V293_OS_TCBInit_publish_finite_enabled with(tcbtable:=tcbtable)(K:=Kpub);try assumption.
                --- pose proof(Int.unsigned_range off);lia.
                --- unfold V293_prio_row. destruct(p <? 8);lia.
                --- unfold V293_prio_bit. destruct(p <? 8)eqn:E;apply Nat.ltb_lt in E||apply Nat.ltb_ge in E;lia.
                --- rewrite Int.repr_unsigned. exact NodeMember.
                --- apply V293_tcb_publication_caller_frame_good;exact Frame.
                --- apply V293_tcb_publication_caller_frame_linv;exact HR.
                --- intros s H. apply Return with(b:=b)(off:=off). eapply V293_tcb_full_publication_restore;exact H.
Qed.

Theorem V293_OS_TCBInit_site_fresh_joint_body : forall Spec sd li r tid hi hc tcbtable
 table reserved bf bp bc pc cpu bh bg br bn nesting bprio bs bb bi bz be bo p top bottom identity size ext options R aop si ci
 (good:GoodFunAsrt(V293_create_owned_share table reserved p ** R)),
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm R ->
 V293_tcb_init_values_valid top bottom identity size ext options -> (R ==> CurLINV li tid) ->
 Spec hi=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** R)aop (fun _=>false) si ci tid good,
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** R)aop (fun _=>false) si ci tid good,(Tvoid,[Tptr V293_tcb_type])) ->
 Spec hc=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options R aop (fun _=>false) si ci tid (proj2 good),
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options R aop (fun _=>false) si ci tid (proj2 good),(Tvoid,[Tptr V293_tcb_type])) ->
 (V293_tcb_enabled_state bf bp bc Vnull(Vint32 Int.zero)
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))))aop (fun _=>false) si ci ==>
 r(Some(Vint32(Int.repr 66)))) ->
 (~In reserved(V293_tcb_table_sites tcbtable)) ->
 (forall b off,
 V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_tcb_publication_globals bh bg br bn ** R)))aop (fun _=>false) si ci ==>
 r(Some(Vint32 Int.zero))) ->
 InfRules Spec sd li (V293_create_joint_inv tcbtable bf table bh bg br bn nesting reserved) r Afalse
 (V293_tcb_enabled_state bf bp bc pc cpu
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))))aop (fun _=>false) si ci)
 (V293_TCBInit_function_body hi hc)Afalse tid.
Proof.
 intros Spec sd li r tid hi hc tcbtable table reserved bf bp bc pc cpu bh bg br bn nesting bprio bs bb bi bz be bo p top bottom identity size ext options R aop si ci good Range Bound Frame Valid HR FirstLookup SecondLookup Empty Outside Return.
 assert(Y:V293_prio_row p<2)by(unfold V293_prio_row;destruct(p <? 8);lia).
 eapply V293_OS_TCBInit_site_fresh_body with
 (Kfree:=(V293_tcb_joint_free_rest tcbtable table bh bg br bn reserved ** Amapsto(nesting,0%Z)Tint8 true(V293_byteval 0)))
 (Kprio:=(Amapsto(nesting,0%Z)Tint8 true(V293_byteval 0) ** V293_tcb_joint_priority_rest tcbtable bf table bh bg br bn reserved p))
 (Kpub:=(V293_tcb_joint_publication_rest tcbtable bf table reserved ** Amapsto(nesting,0%Z)Tint8 true(V293_byteval 0)));try eassumption.
 - intros s H. exact(proj1(V293_create_joint_borrow_free tcbtable bf table bh bg br bn nesting reserved (gettopis si)s)H).
 - intros s H. exact(proj2(V293_create_joint_borrow_free tcbtable bf table bh bg br bn nesting reserved (gettopis si)s)H).
 - intros s H. exact(proj1(V293_create_joint_borrow_priority tcbtable bf table bh bg br bn nesting reserved (gettopis si)p Range s)H).
 - intros s H. exact(proj2(V293_create_joint_borrow_priority tcbtable bf table bh bg br bn nesting reserved (gettopis si)p Range s)H).
 - intros s H. exact(proj1(V293_create_joint_borrow_publication tcbtable bf table bh bg br bn nesting reserved (gettopis si)(V293_prio_row p)Y s)H).
 - intros s H. exact(proj2(V293_create_joint_borrow_publication tcbtable bf table bh bg br bn nesting reserved (gettopis si)(V293_prio_row p)Y s)H).
Qed.

Theorem V293_OS_TCBInit_site_fresh_internal_resources : forall Spec sd li tid hi hc tcbtable table reserved bf bh bg br bn nesting
 p top bottom identity size ext options R aop si ci (good:GoodFunAsrt R),
 GoodI(V293_create_joint_inv tcbtable bf table bh bg br bn nesting reserved)sd li ->
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm R ->
 V293_tcb_init_values_valid top bottom identity size ext options -> (R ==> CurLINV li tid) ->
 Spec hi=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** R)aop(fun _=>false)si ci tid
 (V293_tcb_hook_owner_accepted table reserved p R good),
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** R)aop(fun _=>false)si ci tid
 (V293_tcb_hook_owner_accepted table reserved p R good),(Tvoid,[Tptr V293_tcb_type])) ->
 Spec hc=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options R aop(fun _=>false)si ci tid
 (proj2(V293_tcb_hook_owner_accepted table reserved p R good)),
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options R aop(fun _=>false)si ci tid
 (proj2(V293_tcb_hook_owner_accepted table reserved p R good)),(Tvoid,[Tptr V293_tcb_type])) ->
 (~In reserved(V293_tcb_table_sites tcbtable)) ->
 InfRules Spec sd li(V293_create_joint_inv tcbtable bf table bh bg br bn nesting reserved)
 (fun result=>V293_tcb_internal_post_cells **
 getasrt(V293_tcb_shared_fpost table reserved bf bh bg br bn p R aop(fun _=>false)si ci good []result[]tid) ** V293_tcb_internal_domain)Afalse
 (V293_tcb_internal_pre_cells(V293_byteval p)top bottom identity size ext options **
 V293_tcb_shared_external table bf bh bg br bn(V293_create_owned_share table reserved p ** R)aop(fun _=>false)si ci **
 V293_tcb_internal_domain)(V293_TCBInit_function_body hi hc)Afalse tid.
Proof.
 intros Spec sd li tid hi hc tcbtable table reserved bf bh bg br bn nesting
 p top bottom identity size ext options R aop si ci good GI Range Bound Frame Valid HR FirstLookup SecondLookup Outside.
 eapply conseq_rule.
 - apply V293_tcb_success_internal_unpack.
 - intros s H;exact H.
 - apply ex_intro_rule. intro pc. apply ex_intro_rule. intro cpu.
   apply ex_intro_rule. intro bo. apply ex_intro_rule. intro be.
   apply ex_intro_rule. intro bz. apply ex_intro_rule. intro bi.
   apply ex_intro_rule. intro bb. apply ex_intro_rule. intro bs.
   apply ex_intro_rule. intro bp. apply ex_intro_rule. intro bc.
   apply ex_intro_rule. intro bu.
   eapply conseq_rule with(q:=Afalse ** V293_tcb_internal_domain).
   + apply V293_tcb_shared_internal_entry.
   + intros s H;clear -H;destruct_s s;simpl in *;join auto.
   + eapply r_conseq_rule with
     (r:=fun result=>(V293_tcb_internal_post_cells **
 getasrt(V293_tcb_shared_fpost table reserved bf bh bg br bn p R aop(fun _=>false)si ci good []result[]tid)) ** V293_tcb_internal_domain)
     (ri:=Afalse ** V293_tcb_internal_domain).
     * intros result s H;clear -H;sep auto.
     * intros s H;clear -H;destruct_s s;simpl in *;join auto.
     * apply frame_rule_all.
       -- exact GI.
       -- apply V293_tcb_success_body_good.
       -- apply V293_tcb_internal_domain_frame.
       -- unfold V293_tcb_enabled_state,V293_tcb_enabled_resources.
          do 5 apply V293_star_CurLINV_r. apply V293_tcb_allocated_inputs_linv.
          do 3 apply V293_star_CurLINV_r;exact HR.
       -- eapply conseq_rule with
          (p:=V293_tcb_enabled_state bf bc bu pc cpu
          (V293_tcb_allocated_inputs bc bp bs bb bi bz be bo p top bottom identity size ext options
          (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p **
          (V293_tcb_publication_globals bh bg br bn ** R))))aop(fun _=>false)si ci).
          ++ intros s H. unfold V293_tcb_enabled_state,V293_tcb_enabled_resources,V293_tcb_allocated_inputs in *.
             cbn[V293_rdy_raw_cells]in *;clear -H;sep auto.
          ++ intros s H;exact H.
          ++ eapply V293_OS_TCBInit_site_fresh_joint_body with
          (good:=V293_tcb_hook_owner_accepted table reserved p R good);try eassumption.
             ** intros s H.
                assert(E:s |= V293_tcb_internal_post_cells **
               V293_tcb_shared_external table bf bh bg br bn(V293_create_owned_share table reserved p ** R)aop(fun _=>false)si ci).
             { eapply V293_tcb_shared_internal_exit.
               unfold V293_tcb_enabled_state,V293_tcb_enabled_resources,V293_tcb_allocated_inputs in *.
               cbn[V293_rdy_raw_cells]in *;clear -H;sep auto. }
             eapply astar_mono;[intros st HS;exact HS| |exact E].
             intros st HS. cbn[V293_tcb_shared_fpost getasrt]. left.
             apply astar_l_apure_intro;[exact HS|reflexivity].
             ** intros b off s H.
             pose proof(V293_tcb_shared_internal_exit table bf bu bc bp bs bb bi bz be bo bh bg br bn
               p top bottom identity size ext options(Vptr(b,off))(Vint32 Int.zero)R aop(fun _=>false)si ci s H)as E.
             eapply astar_mono;[intros st HS;exact HS| |exact E].
             intros st HS. cbn[V293_tcb_shared_fpost getasrt]. right.
             apply astar_l_apure_intro;[exact HS|reflexivity].
Qed.

Theorem V293_OS_TCBInit_site_fresh_internal_contract : forall P f vl lg pre post Spec sd li tid hi hc tcbtable table reserved bf bh bg br bn nesting
 p top bottom identity size ext options R aop si ci (good:GoodFunAsrt R),
 GoodI(V293_create_joint_inv tcbtable bf table bh bg br bn nesting reserved)sd li ->
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm R ->
 V293_tcb_init_values_valid top bottom identity size ext options -> (R ==> CurLINV li tid) ->
 Spec hi=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** R)aop(fun _=>false)si ci tid
 (V293_tcb_hook_owner_accepted table reserved p R good),
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** R)aop(fun _=>false)si ci tid
 (V293_tcb_hook_owner_accepted table reserved p R good),(Tvoid,[Tptr V293_tcb_type])) ->
 Spec hc=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options R aop(fun _=>false)si ci tid
 (proj2(V293_tcb_hook_owner_accepted table reserved p R good)),
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options R aop(fun _=>false)si ci tid
 (proj2(V293_tcb_hook_owner_accepted table reserved p R good)),(Tvoid,[Tptr V293_tcb_type])) ->
 (~In reserved(V293_tcb_table_sites tcbtable)) ->
 P f=Some(V293_TCBInit_function hi hc) ->
 Some pre=BuildPreI P f vl lg
 (V293_tcb_shared_fpre table reserved bf bh bg br bn p top bottom identity size ext options R aop(fun _=>false)si ci good)tid ->
 Some post=BuildRetI P f vl lg
 (V293_tcb_shared_fpost table reserved bf bh bg br bn p R aop(fun _=>false)si ci good)tid ->
 InfRules Spec sd li(V293_create_joint_inv tcbtable bf table bh bg br bn nesting reserved)
 post Afalse pre(V293_TCBInit_function_body hi hc)Afalse tid.
Proof.
 intros P f vl lg pre post Spec sd li tid hi hc tcbtable table reserved bf bh bg br bn nesting
 p top bottom identity size ext options R aop si ci good GI Range Bound Frame Valid HR FirstLookup SecondLookup Outside Code Pre Post.
 unfold BuildPreI in Pre. rewrite Code in Pre. cbn[V293_TCBInit_function]in Pre.
 destruct(dl_vl_match V293_TCBInit_parameters(rev vl))eqn:Typed;[idtac|discriminate].
 pose proof(dl_vl_match_dv_same_length _ _ Typed)as Length.
 rewrite rev_length in Length. cbn[V293_TCBInit_parameters decllen]in Length.
 destruct vl as [ |v7 vl];[discriminate Length|idtac].
 destruct vl as [ |v6 vl];[discriminate Length|idtac].
 destruct vl as [ |v5 vl];[discriminate Length|idtac].
 destruct vl as [ |v4 vl];[discriminate Length|idtac].
 destruct vl as [ |v3 vl];[discriminate Length|idtac].
 destruct vl as [ |v2 vl];[discriminate Length|idtac].
 destruct vl as [ |v1 vl];[discriminate Length|idtac].
 destruct vl;[idtac|discriminate Length].
 fold V293_tcb_internal_declarations in Pre. rewrite V293_tcb_internal_buildp in Pre.
 change(Some pre=Some(V293_tcb_internal_pre_cells v1 v2 v3 v4 v5 v6 v7 **
 ([|[v1;v2;v3;v4;v5;v6;v7]=V293_tcb_success_arguments p top bottom identity size ext options|] **
 V293_tcb_shared_external table bf bh bg br bn(V293_create_owned_share table reserved p ** R)aop(fun _=>false)si ci) ** V293_tcb_internal_domain))in Pre.
 inversion Pre;subst pre.
 unfold BuildRetI in Post. rewrite Code in Post.
 change(Some post=Some(fun result=>V293_tcb_internal_post_cells ** getasrt(V293_tcb_shared_fpost table reserved bf bh bg br bn p R aop(fun _=>false)si ci good []result[]tid) ** V293_tcb_internal_domain))in Post.
 inversion Post;subst post.
 eapply conseq_rule with(p:=V293_tcb_internal_pre_cells(V293_byteval p)top bottom identity size ext options **
 V293_tcb_shared_external table bf bh bg br bn(V293_create_owned_share table reserved p ** R)aop(fun _=>false)si ci ** V293_tcb_internal_domain).
 - intros s H.
   assert(K:s |= [|[v1;v2;v3;v4;v5;v6;v7]=V293_tcb_success_arguments p top bottom identity size ext options|] **
   (V293_tcb_internal_pre_cells v1 v2 v3 v4 v5 v6 v7 ** V293_tcb_shared_external table bf bh bg br bn(V293_create_owned_share table reserved p ** R)aop(fun _=>false)si ci ** V293_tcb_internal_domain)).
   { clear -H;sep auto. }
   apply astar_l_apure_elim in K. destruct K as[Args K].
   unfold V293_tcb_success_arguments in Args. inversion Args;subst;exact K.
 - intros s H;exact H.
 - eapply V293_OS_TCBInit_site_fresh_internal_resources;eassumption.
Qed.
