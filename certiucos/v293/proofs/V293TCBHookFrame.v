(* Corrected Hook resource boundary; old frozen conditional theorems remain unchanged. *)
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
Import ListNotations.
Local Open Scope nat_scope.


Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateJointShared.
Require Import CertiOS.certiucos.v293.proofs.V293TCBOwnedPriority.
(* Caller-local lookup conditions are NOT function resources. These controls
   isolate local shadow facts, globals, and half permission independently. *)
Lemma V293_tcb_hook_local_shadow_rejected : forall x,
 ~ GoodFunAsrt(A_notin_lenv x).
Proof. intros x H;exact H. Qed.
Lemma V293_tcb_hook_publication_rejected : forall bh bg br bn,
 ~ GoodFunAsrt(V293_tcb_publication_globals bh bg br bn).
Proof. intros bh bg br bn H. exact(proj1 H). Qed.
Lemma V293_tcb_hook_former_premise_rejected : forall table reserved p bh bg br bn R,
 ~ GoodFunAsrt(V293_create_owned_share table reserved p **
 (V293_tcb_publication_globals bh bg br bn ** R)).
Proof. intros table reserved p bh bg br bn R H.
 apply(V293_tcb_hook_publication_rejected bh bg br bn). exact(proj1(proj2 H)). Qed.
Lemma V293_tcb_hook_global_binding_accepted : forall x t l,
 GoodFunAsrt(Agvarenv x t l).
Proof. intros;exact I. Qed.
Lemma V293_tcb_hook_owner_accepted : forall table reserved p R,
 GoodFunAsrt R -> GoodFunAsrt(V293_create_owned_share table reserved p ** R).
Proof. intros. unfold V293_create_owned_share,V293_reservation_owner.
 cbn[GoodFunAsrt]. split;[exact I|assumption]. Qed.

Theorem V293_OS_TCBInit_site_hook_framed : forall Spec sd li I r tid hi hc tcbtable
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
 (forall b off next s,
 s |= V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))))aop ir si ci ->
 (b,off)<>reserved) ->
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
 intros Spec sd li I r tid hi hc tcbtable table reserved bf bp bc pc cpu Kfree Kprio Kpub bh bg br bn bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci good Range Bound Frame Valid HR FreeOpen FreeClose PriorityOpen PriorityClose FirstLookup SecondLookup Empty Fresh PubOpen PubClose Return.
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
   + intros s H. apply astar_comm. apply astar_l_apure_intro;[exact H|eapply Fresh;exact H].
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

Theorem V293_OS_TCBInit_creator_joint_hook_framed : forall Spec sd li r tid hi hc tcbtable
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
 (forall b off next s,
 s |= V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))))aop (fun _=>false) si ci ->
 (b,off)<>reserved) ->
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
 intros Spec sd li r tid hi hc tcbtable table reserved bf bp bc pc cpu bh bg br bn nesting bprio bs bb bi bz be bo p top bottom identity size ext options R aop si ci good Range Bound Frame Valid HR FirstLookup SecondLookup Empty Fresh Return.
 assert(Y:V293_prio_row p<2)by(unfold V293_prio_row;destruct(p <? 8);lia).
 eapply V293_OS_TCBInit_site_hook_framed with
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
Print Assumptions V293_tcb_hook_local_shadow_rejected.
Print Assumptions V293_tcb_hook_publication_rejected.
Print Assumptions V293_tcb_hook_former_premise_rejected.
Print Assumptions V293_tcb_hook_global_binding_accepted.
Print Assumptions V293_tcb_hook_owner_accepted.
Print Assumptions V293_OS_TCBInit_site_hook_framed.
Print Assumptions V293_OS_TCBInit_creator_joint_hook_framed.
