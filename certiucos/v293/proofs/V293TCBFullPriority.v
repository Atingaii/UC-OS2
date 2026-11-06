(* Lossless seven-parameter/two-local views connect the original whole body
   to the owned priority slot bracket. No new AST or axiom. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBOwnedPriority.
Require Import CertiOS.certiucos.v293.proofs.V293TCBAllocatedFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFreePool.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEnabledHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReservationOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

(* Only empty-heap environment facts are copied, never parameter bytes. *)
Lemma V293_tcb_fields_priority_copy : forall bp bprio bs bb bi bz be bo,
 V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 bp bprio bs bb bi bz be bo ==>
 (Alvarenv 101%Z Tint8(bprio,0%Z) //\\ Alvarenv 108%Z(Tptr V293_tcb_type)(bp,0%Z)) **
 V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 bp bprio bs bb bi bz be bo.
Proof.
 intros bp bprio bs bb bi bz be bo s H.
 destruct s as [[[[[[ge le] M] irq] aux] O] op].
 apply sat_split'. exists empmem. exists M. exists empabst. exists O.
 split;[apply map_join_comm;apply map_join_emp| ].
 split;[apply map_join_comm;apply map_join_emp| ].
 split;[ |exact H].
 unfold V293_tcb_fields_bindings in H. destruct H as[HP[HQ Rest]].
 split;[destruct HQ as[b[E[B[HM HO]]]]|destruct HP as[b[E[B[HM HO]]]]];
 cbn[sat]in *;exists b;repeat split;try assumption;reflexivity.
Qed.
Lemma V293_tcb_fields_priority_drop : forall bp bprio bs bb bi bz be bo,
 (Alvarenv 101%Z Tint8(bprio,0%Z) //\\ Alvarenv 108%Z(Tptr V293_tcb_type)(bp,0%Z)) **
 V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 bp bprio bs bb bi bz be bo ==>
 V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 bp bprio bs bb bi bz be bo.
Proof.
 intros bp bprio bs bb bi bz be bo s H.
 destruct s as [[[[[[ge le] M] irq] aux] O] op].
 apply sat_split in H. destruct H as[m1[m2[o1[o2[JM[JO[[H1 H2]H]]]]]]].
 destruct H1 as[b[E[B[HM HO]]]]. cbn[getmem getabst get_smem get_mem]in HM,HO.
 subst m1. unfold emposabst in HO;subst o1.
 apply map_join_emp'' in JM,JO. subst. exact H.
Qed.

(* Six other argument cells, CPU local, and all original environment bindings.
   prio/ptcb physical cells are in the minimal priority view, exactly once. *)
Definition V293_tcb_priority_caller_frame bf bp bc bprio bs bb bi bz be bo
 cpu top bottom identity size ext options :=
 V293_tcb_empty_bindings bf bp bc ** Amapsto(bc,0%Z)Tint32 true cpu **
 V293_rdy_raw_cells
 ([((bs,0%Z),Tptr Tint32,top);((bb,0%Z),Tptr Tint32,bottom);
  ((bi,0%Z),Tint16,identity);((bz,0%Z),Tint32,size);
  ((be,0%Z),Tptr Tvoid,ext);((bo,0%Z),Tint16,options)])
 (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 bp bprio bs bb bi bz be bo).
Lemma V293_tcb_priority_caller_frame_good : forall bf bp bc bprio bs bb bi bz be bo
 cpu top bottom identity size ext options,
 GoodFrm(V293_tcb_priority_caller_frame bf bp bc bprio bs bb bi bz be bo cpu top bottom identity size ext options).
Proof.
 intros bf bp bc bprio bs bb bi bz be bo cpu top bottom identity size ext options. cbn[V293_tcb_priority_caller_frame V293_tcb_empty_bindings V293_tcb_fields_bindings V293_rdy_raw_cells GoodFrm];tauto.
Qed.

Lemma V293_tcb_full_priority_view : forall table bf bp bc bprio bs bb bi bz be bo
 pc cpu p top bottom identity size ext options N R aop ir si ci,
 V293_tcb_enabled_state bf bp bc pc cpu
 (N ** V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** R))aop ir si ci ==>
 V293_tcb_priority_state table bprio bp p pc
 (N ** (R ** V293_tcb_priority_caller_frame bf bp bc bprio bs bb bi bz be bo cpu top bottom identity size ext options))aop ir true si ci.
Proof.
 intros table bf bp bc bprio bs bb bi bz be bo pc cpu p top bottom identity size ext options N R aop ir si ci s H.
 unfold V293_tcb_enabled_state,V293_tcb_enabled_resources,V293_tcb_allocated_inputs in H.
 assert(B:s |= V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 bp bprio bs bb bi bz be bo **
 (<||aop||> ** OS[ir,true,si,ci] ** V293_tcb_empty_bindings bf bp bc **
 Amapsto(bp,0%Z)(Tptr V293_tcb_type)true pc ** Amapsto(bc,0%Z)Tint32 true cpu **
 N ** V293_rdy_raw_cells
 ([((bprio,0%Z),Tint8,V293_byteval p);((bs,0%Z),Tptr Tint32,top);((bb,0%Z),Tptr Tint32,bottom);
 ((bi,0%Z),Tint16,identity);((bz,0%Z),Tint32,size);((be,0%Z),Tptr Tvoid,ext);((bo,0%Z),Tint16,options)])
 (V293_tcb_table_binding table ** R))).
 { cbn[V293_rdy_raw_cells]in *;clear -H;sep auto. }
 eapply astar_mono in B;[ |apply V293_tcb_fields_priority_copy|intros st HS;exact HS].
 unfold V293_tcb_priority_state,V293_tcb_priority_resources,V293_tcb_priority_bindings,V293_tcb_priority_caller_frame.
 cbn[V293_tcb_priority_locals V293_rdy_raw_cells]in *;clear -B;sep auto.
Qed.
Lemma V293_tcb_full_priority_restore : forall table bf bp bc bprio bs bb bi bz be bo
 pc cpu p top bottom identity size ext options N R aop ir si ci,
 V293_tcb_priority_state table bprio bp p pc
 (N ** (R ** V293_tcb_priority_caller_frame bf bp bc bprio bs bb bi bz be bo cpu top bottom identity size ext options))aop ir true si ci ==>
 V293_tcb_enabled_state bf bp bc pc cpu
 (N ** V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** R))aop ir si ci.
Proof.
 intros table bf bp bc bprio bs bb bi bz be bo pc cpu p top bottom identity size ext options N R aop ir si ci s H.
 unfold V293_tcb_priority_state,V293_tcb_priority_resources,V293_tcb_priority_bindings,V293_tcb_priority_caller_frame in H.
 assert(B:s |= ((Alvarenv 101%Z Tint8(bprio,0%Z) //\\ Alvarenv 108%Z(Tptr V293_tcb_type)(bp,0%Z)) **
 V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z bp bprio bs bb bi bz be bo) **
 (<||aop||> ** OS[ir,true,si,ci] ** V293_tcb_empty_bindings bf bp bc **
 Amapsto(bp,0%Z)(Tptr V293_tcb_type)true pc ** Amapsto(bc,0%Z)Tint32 true cpu **
 N ** V293_rdy_raw_cells
 ([((bprio,0%Z),Tint8,V293_byteval p);((bs,0%Z),Tptr Tint32,top);((bb,0%Z),Tptr Tint32,bottom);
 ((bi,0%Z),Tint16,identity);((bz,0%Z),Tint32,size);((be,0%Z),Tptr Tvoid,ext);((bo,0%Z),Tint16,options)])
 (V293_tcb_table_binding table ** R))).
 { cbn[V293_tcb_priority_locals V293_rdy_raw_cells]in *;clear -H;sep auto. }
 eapply astar_mono in B;[ |apply V293_tcb_fields_priority_drop|intros st HS;exact HS].
 unfold V293_tcb_enabled_state,V293_tcb_enabled_resources,V293_tcb_allocated_inputs.
 cbn[V293_rdy_raw_cells]in *;clear -B;sep auto.
Qed.

(* The only remaining Hoare continuation begins at the SECOND Hook and the
   original publication. Freshness is required of an actual selected state,
   not forall pointers, and is NOT yet derived from the production allocator. *)
Theorem V293_OS_TCBInit_free_body_after_owned_priority : forall Spec sd li I r tid hi hc
 table reserved bf bp bc pc cpu Kfree Kprio bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci
 (good:GoodFunAsrt(V293_create_owned_share table reserved p ** R)),
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm R ->
 V293_tcb_init_values_valid top bottom identity size ext options -> (R ==> CurLINV li tid) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** (V293_tcb_free_pool bf ** Kfree)) ->
 (Aisr ir ** (V293_tcb_free_pool bf ** Kfree) ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 (Aisr ir ** invlth_isr I 0(gettopis si) ==> Aisr ir ** V293_create_owned_pool table reserved p Kprio) ->
 (Aisr ir ** V293_create_owned_pool table reserved p Kprio ==> Aisr ir ** invlth_isr I 0(gettopis si)) ->
 Spec hi=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** R)aop ir si ci tid good,
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** R)aop ir si ci tid good,(Tvoid,[Tptr V293_tcb_type])) ->
 (V293_tcb_enabled_state bf bp bc Vnull(Vint32 Int.zero)
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** R)))aop ir si ci ==>
 r(Some(Vint32(Int.repr 66)))) ->
 (forall b off next s,
 s |= V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** R)))aop ir si ci ->
 (b,off)<>reserved) ->
 (forall b off next,(Int.unsigned off+55<=Int.max_unsigned)%Z -> rule_type_val_match(Tcom_ptr 410%Z)next=true ->
 InfRules Spec sd li I r Afalse
 (V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** R))aop ir si ci)
 (sseq(scall hc[evar 108%Z])(V293_TCB_publish 108%Z 93%Z 94%Z 95%Z 96%Z))Afalse tid) ->
 InfRules Spec sd li I r Afalse
 (V293_tcb_enabled_state bf bp bc pc cpu
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** R)))aop ir si ci)
 (V293_TCBInit_function_body hi hc)Afalse tid.
Proof.
 intros Spec sd li I r tid hi hc table reserved bf bp bc pc cpu Kfree Kprio bprio bs bb bi bz be bo p top bottom identity size ext options R aop ir si ci good Range Bound Frame Valid HR FreeOpen FreeClose PriorityOpen PriorityClose Lookup Empty Fresh Rest.
 apply V293_OS_TCBInit_free_body_after_fields with(K:=Kfree);try assumption.
 - unfold V293_tcb_table_binding,V293_create_owned_share,V293_reservation_owner;cbn[GoodFrm];tauto.
 - apply V293_star_CurLINV_r. apply V293_star_CurLINV_r;exact HR.
 - intros b off next NodeBound NextTyped.
   eapply conseq_rule with
   (p:=V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
    (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
     V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
     (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** R)))aop ir si ci **
     [|(b,off)<>reserved|]).
   + intros s H. apply astar_comm. apply astar_l_apure_intro;[exact H|eapply Fresh;exact H].
   + intros s H;exact H.
   + apply pure_split_rule. intro Distinct.
     eapply conseq_rule with
     (p:=V293_tcb_priority_state table bprio bp p(Vptr(b,off))
       (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
       ((V293_create_owned_share table reserved p ** R) **
        V293_tcb_priority_caller_frame bf bp bc bprio bs bb bi bz be bo(Vint32 Int.zero)top bottom identity size ext options))aop ir true si ci).
     * apply V293_tcb_full_priority_view.
     * intros s H;exact H.
     * apply V293_OS_TCBInit_owned_suffix_after_first_hook with(reserved:=reserved)(K:=Kprio)(good:=good);try assumption.
       -- apply V293_tcb_priority_caller_frame_good.
       -- eapply conseq_rule;[apply V293_tcb_full_priority_restore|intros s H;exact H|apply Rest;assumption].
Qed.
Print Assumptions V293_OS_TCBInit_free_body_after_owned_priority.
