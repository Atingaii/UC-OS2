(* One physical core for the original creator reservation/rollback and full
   TCB initializer. Task count and OSIntNesting are distinct bytes. The zero
   nesting instance does not cover active ISR entry or the whole creator API. *)
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


Definition V293_create_joint_core (bt bf table bh bg rows tasks nesting:block)(reserved:addrval) :=
 V293_tcb_joint_core bt bf table bh bg rows tasks reserved **
 Amapsto(nesting,0%Z)Tint8 true(V293_byteval 0).
Lemma V293_create_joint_core_good : forall bt bf table bh bg rows tasks nesting reserved,
 GoodInvAsrt(V293_create_joint_core bt bf table bh bg rows tasks nesting reserved).
Proof. intros. unfold V293_create_joint_core. cbn[GoodInvAsrt]. split;[apply V293_tcb_joint_core_good|auto]. Qed.
Lemma V293_create_joint_core_precise : forall bt bf table bh bg rows tasks nesting reserved,
 precise(V293_create_joint_core bt bf table bh bg rows tasks nesting reserved).
Proof. intros. unfold V293_create_joint_core. apply precise_star;[apply V293_tcb_joint_core_precise|apply V293_tcb_mapsto_precise]. Qed.
Lemma V293_create_joint_core_aux_stable : forall bt bf table bh bg rows tasks nesting reserved ge le M ir aux O op ir' aux',
 (ge,le,M,ir,aux,O,op) |= V293_create_joint_core bt bf table bh bg rows tasks nesting reserved ->
 (ge,le,M,ir',aux',O,op) |= V293_create_joint_core bt bf table bh bg rows tasks nesting reserved.
Proof.
 intros. apply sat_split in H. destruct H as(m1&m2&o1&o2&JM&JO&HC&HN).
 apply sat_split'. exists m1. exists m2. exists o1. exists o2.
 split;[exact JM| ]. split;[exact JO| ]. split;[eapply V293_tcb_joint_core_aux_stable;exact HC|exact HN].
Qed.
Lemma V293_create_joint_core_isr : forall bt bf table bh bg rows tasks nesting reserved,
 assertion.inv_isr_prop(V293_create_joint_core bt bf table bh bg rows tasks nesting reserved).
Proof.
 intros. unfold assertion.inv_isr_prop. repeat split;intros;
 destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];eapply V293_create_joint_core_aux_stable;exact H.
Qed.
Definition V293_create_joint_inv bt bf table bh bg rows tasks nesting reserved : Inv := fun i=>match i with
 | O=>mkinvasrt(V293_create_joint_core_good bt bf table bh bg rows tasks nesting reserved)
  (conj(V293_create_joint_core_precise bt bf table bh bg rows tasks nesting reserved)
       (V293_create_joint_core_isr bt bf table bh bg rows tasks nesting reserved))
 | S j=>V293_shared_inv(S j) end.
Section Borrow.
Variables(bt bf table bh bg rows tasks nesting:block)(reserved:addrval).
Let I:=V293_create_joint_inv bt bf table bh bg rows tasks nesting reserved.
Let C:=V293_create_joint_core bt bf table bh bg rows tasks nesting reserved.
Lemma V293_create_joint_noisr_tail : forall n i,starinv_noisr I(S i)n <==> Aemp.
Proof.
 induction n;intros i s;cbn[starinv_noisr];[reflexivity| ].
 change(s |= Aemp ** starinv_noisr I(S(S i))n <-> s |= Aemp).
 split;intro H.
 - apply astar_l_aemp_elim in H. apply IHn in H;exact H.
 - apply astar_l_aemp_intro. apply IHn;exact H.
Qed.
Lemma V293_create_joint_noisr_core : forall n,starinv_noisr I 0 n <==> C.
Proof.
 intros[ |n]s;[reflexivity| ].
 change(s |= C ** starinv_noisr I 1 n <-> s |= C). split;intro H.
 - apply astar_r_aemp_elim. eapply astar_mono;[intros st HS;exact HS|intros st HS;apply V293_create_joint_noisr_tail in HS;exact HS|exact H].
 - eapply astar_mono;[intros st HS;exact HS|intros st HS;apply V293_create_joint_noisr_tail;exact HS| ]. apply astar_r_aemp_intro;exact H.
Qed.
Theorem V293_create_joint_borrow : forall n,
 Aisr(fun _=>false) ** invlth_isr I 0 n <==> Aisr(fun _=>false) ** C.
Proof.
 intros n s. destruct s as [[[[[[ge le] M] ir] aux] O] op]. split;intro H.
 all: (apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&H1&H2);
 destruct H1 as[E Empty];cbn in E;subst ir;
 apply sat_split';exists m1;exists m2;exists o1;exists o2;
 split;[exact JM| ];split;[exact JO| ];split;[split;[reflexivity|exact Empty]| ]).
 - unfold invlth_isr in H2. rewrite Nat.sub_0_r in H2.
   apply V293_create_joint_noisr_core with(n:=n). eapply invisr_imply_noisr';[ |exact H2]. reflexivity.
 - unfold invlth_isr. rewrite Nat.sub_0_r.
   apply V293_shared_clear_noisr_close;[reflexivity| ]. apply V293_create_joint_noisr_core;exact H2.
Qed.
Theorem V293_create_joint_priority_view : forall p,p<13 ->
 C <==> V293_create_owned_pool table reserved p
  (Amapsto(nesting,0%Z)Tint8 true(V293_byteval 0) **
   V293_tcb_joint_priority_rest bt bf table bh bg rows tasks reserved p).
Proof.
 intros p Range s. pose proof(V293_tcb_joint_priority_view bt bf table bh bg rows tasks reserved p Range)as View.
 unfold C,V293_create_joint_core,V293_create_owned_pool. split;intro H.
 - eapply astar_mono in H;[ |intros st HS;exact(proj1(View st)HS)|intros st HS;exact HS].
   unfold V293_create_owned_pool in H. clear -H;sep auto.
 - assert(HC:s |= (V293_reservation_pool(table,(4*Z.of_nat p)%Z)reserved **
    V293_tcb_joint_priority_rest bt bf table bh bg rows tasks reserved p) **
    Amapsto(nesting,0%Z)Tint8 true(V293_byteval 0))by(clear -H;sep auto).
   eapply astar_mono;[intros st HS;exact(proj2(View st)HS)|intros st HS;exact HS|exact HC].
Qed.
Theorem V293_create_joint_borrow_priority : forall n p,p<13 ->
 Aisr(fun _=>false) ** invlth_isr I 0 n <==>
 Aisr(fun _=>false) ** V293_create_owned_pool table reserved p
  (Amapsto(nesting,0%Z)Tint8 true(V293_byteval 0) **
   V293_tcb_joint_priority_rest bt bf table bh bg rows tasks reserved p).
Proof.
 intros n p Range s. pose proof(V293_create_joint_borrow n s)as B.
 pose proof(V293_create_joint_priority_view p Range)as V. split;intro H.
 - apply B in H. eapply astar_mono;[intros st HS;exact HS|intros st HS;exact(proj1(V st)HS)|exact H].
 - apply B. eapply astar_mono;[intros st HS;exact HS|intros st HS;exact(proj2(V st)HS)|exact H].
Qed.
Theorem V293_create_joint_borrow_free : forall n,
 Aisr(fun _=>false) ** invlth_isr I 0 n <==>
 Aisr(fun _=>false) ** (V293_tcb_site_free_pool bt bf **
  (V293_tcb_joint_free_rest bt table bh bg rows tasks reserved **
   Amapsto(nesting,0%Z)Tint8 true(V293_byteval 0))).
Proof.
 intros n s. pose proof(V293_create_joint_borrow n s)as B.
 unfold C,V293_create_joint_core,V293_tcb_joint_core,V293_tcb_joint_free_rest in *.
 split;intro H;[apply B in H|apply B];clear -H;sep auto.
Qed.
Theorem V293_create_joint_borrow_publication : forall n y,y<2 ->
 Aisr(fun _=>false) ** invlth_isr I 0 n <==>
 Aisr(fun _=>false) ** (V293_tcb_finite_shared bt bh bg rows tasks y **
  (V293_tcb_joint_publication_rest bt bf table reserved **
   Amapsto(nesting,0%Z)Tint8 true(V293_byteval 0))).
Proof.
 intros n y Range s. pose proof(V293_create_joint_borrow n s)as B.
 pose proof(V293_tcb_joint_publication_view bt bf table bh bg rows tasks reserved y Range)as V.
 assert(View:C <==> V293_tcb_finite_shared bt bh bg rows tasks y **
  (V293_tcb_joint_publication_rest bt bf table reserved **
   Amapsto(nesting,0%Z)Tint8 true(V293_byteval 0))).
 { intro st. unfold C,V293_create_joint_core. split;intro H.
   - eapply astar_mono in H;[ |intros q HQ;exact(proj1(V q)HQ)|intros q HQ;exact HQ]. clear -H;sep auto.
   - assert(HC:st |= (V293_tcb_finite_shared bt bh bg rows tasks y **
      V293_tcb_joint_publication_rest bt bf table reserved) **
      Amapsto(nesting,0%Z)Tint8 true(V293_byteval 0))by(clear -H;sep auto).
     eapply astar_mono;[intros q HQ;exact(proj2(V q)HQ)|intros q HQ;exact HQ|exact HC]. }
 split;intro H.
 - apply B in H. eapply astar_mono;[intros q HQ;exact HQ|intros q HQ;exact(proj1(View q)HQ)|exact H].
 - apply B. eapply astar_mono;[intros q HQ;exact HQ|intros q HQ;exact(proj2(View q)HQ)|exact H].
Qed.
End Borrow.

Theorem V293_OS_TCBInit_creator_joint : forall Spec sd li r tid hi hc tcbtable
 table reserved bf bp bc pc cpu bh bg br bn nesting bprio bs bb bi bz be bo p top bottom identity size ext options R aop si ci
 (good:GoodFunAsrt(V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))),
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm R ->
 V293_tcb_init_values_valid top bottom identity size ext options -> (R ==> CurLINV li tid) ->
 Spec hi=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))aop (fun _=>false) si ci tid good,
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))aop (fun _=>false) si ci tid good,(Tvoid,[Tptr V293_tcb_type])) ->
 Spec hc=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options (V293_tcb_publication_globals bh bg br bn ** R) aop (fun _=>false) si ci tid (proj2 good),
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options (V293_tcb_publication_globals bh bg br bn ** R) aop (fun _=>false) si ci tid (proj2 good),(Tvoid,[Tptr V293_tcb_type])) ->
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
 eapply V293_OS_TCBInit_site_allocated_finite_published with
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
Print Assumptions V293_OS_TCBInit_creator_joint.


Theorem V293_OSTaskCreateExt_joint_reservation : forall Spec sd li r ri tid
 bt bf table bh bg rows tasks bp bc nesting token p cpu F aop si ci,
 p<13 -> GoodFrm F -> (F ==> CurLINV li tid) ->
 InfRules Spec sd li(V293_create_joint_inv bt bf table bh bg rows tasks nesting(token,Int.zero))r ri
 (V293_create_slot_state bp bc table nesting token p 0 None cpu
  (V293_tcb_joint_priority_rest bt bf table bh bg rows tasks(token,Int.zero)p)F aop(fun _=>false)si ci)
 (sseq(sassign(earrayelem(evar 92%Z)(evar 101%Z))(V293_task_prio_reserved_expr 97%Z))(sprim excrit))
 (V293_create_enabled_state bp bc p cpu
  (V293_create_owned_share table(token,Int.zero)p ** V293_create_slot_views table nesting token ** F)
  aop(fun _=>false)si ci)tid.
Proof.
 intros Spec sd li r ri tid bt bf table bh bg rows tasks bp bc nesting token p cpu F aop si ci Range Frame HR.
 eapply V293_OSTaskCreateExt_owned_reservation;try eassumption.
 intros st HS. exact(proj2(V293_create_joint_borrow_priority bt bf table bh bg rows tasks nesting(token,Int.zero)(gettopis si)p Range st)HS).
Qed.
Theorem V293_OSTaskCreateExt_joint_rollback : forall Spec sd li r ri tid
 bt bf table bh bg rows tasks nesting reserved p F aop si ci,
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm F -> (F ==> CurLINV li tid) ->
 InfRules Spec sd li(V293_create_joint_inv bt bf table bh bg rows tasks nesting reserved)r ri
 (V293_create_enabled_failure_state table p(V293_create_owned_share table reserved p ** F)aop(fun _=>false)si ci)
 (V293_TaskCreateExt_rollback 92%Z 101%Z)
 (V293_create_enabled_failure_state table p F aop(fun _=>false)si ci)tid.
Proof.
 intros Spec sd li r ri tid bt bf table bh bg rows tasks nesting reserved p F aop si ci Range Bound Frame HR.
 eapply V293_OSTaskCreateExt_owned_rollback with
 (K:=Amapsto(nesting,0%Z)Tint8 true(V293_byteval 0) ** V293_tcb_joint_priority_rest bt bf table bh bg rows tasks reserved p);try eassumption.
 - intros st HS. exact(proj1(V293_create_joint_borrow_priority bt bf table bh bg rows tasks nesting reserved(gettopis si)p Range st)HS).
 - intros st HS. exact(proj2(V293_create_joint_borrow_priority bt bf table bh bg rows tasks nesting reserved(gettopis si)p Range st)HS).
Qed.

Lemma V293_create_joint_initial_enter : forall Spec sd li r ri tid bt bf bh bg rows tasks
 bp bc table bn br p cpu F aop si ci,
 (gettopis si<=INUM)%nat -> GoodFrm F ->
 p<13 ->
 InfRules Spec sd li(V293_create_joint_inv bt bf table bh bg rows tasks bn(br,Int.zero)) r ri
 (V293_create_enabled_state bp bc p cpu(V293_create_slot_views table bn br ** F)aop (fun _=>false) si ci)
 (sprim encrit)
 (EX v:val,[|rule_type_val_match(Tptr V293_tcb_type)v=true|] **
  V293_create_owned_acquired bp bc table bn br p cpu v (V293_tcb_joint_priority_rest bt bf table bh bg rows tasks(br,Int.zero)p) F aop (fun _=>false) si ci)tid.
Proof.
 intros Spec sd li r ri tid bt bf bh bg rows tasks bp bc table bn br p cpu F aop si ci Bound Frame Range.
 eapply V293_create_owned_initial_enter;try eassumption.
 intros st HS. exact(proj1(V293_create_joint_borrow_priority bt bf table bh bg rows tasks bn(br,Int.zero)(gettopis si)p Range st)HS).
Qed.

Theorem V293_OSTaskCreateExt_joint_stack_fragment : forall Spec sd li r ri tid bt bf bh bg rows tasks hook
 bp bc table bn br p cpu F Rbefore Rafter aop si ci
 (BeforeGood:GoodFunAsrt Rbefore)(AfterGood:GoodFunAsrt Rafter)
 target argv inputtop options stack oldpsp,
 p<13 -> GoodFrm F -> GoodFrm Rbefore ->
 V293_stack_argument_valid argv inputtop options ->
 (Rbefore ==> CurLINV li tid) -> (Rafter ==> CurLINV li tid) ->
 let before:=@mkfunasrt (V293_create_enabled_external Rbefore aop (fun _=>false) si ci)
   (V293_create_enabled_external_good Rbefore aop (fun _=>false) si ci BeforeGood) in
 let after:=@mkfunasrt (V293_create_enabled_external Rafter aop (fun _=>false) si ci)
   (V293_create_enabled_external_good Rafter aop (fun _=>false) si ci AfterGood) in
 Spec hook=Some(V293_create_stack_resource_fpre before(V293_create_stack_values target argv inputtop options),
 V293_create_stack_resource_fpost after(V293_create_stack_values target argv inputtop options)stack,
 (Tptr Tint32,rev V293_stack_argument_types)) ->
 InfRules Spec sd li(V293_create_joint_inv bt bf table bh bg rows tasks bn(br,Int.zero)) r ri
 (V293_create_slot_state bp bc table bn br p 0 None cpu (V293_tcb_joint_priority_rest bt bf table bh bg rows tasks(br,Int.zero)p)
  (LV 108%Z @ (Tptr Tint32) |->oldpsp **
   V293_create_stack_arguments target argv inputtop options(Rbefore ** F))aop (fun _=>false) si ci)
 (sseq(sassign(earrayelem(evar 92%Z)(evar 101%Z))(V293_task_prio_reserved_expr 97%Z))
  (sseq(sprim excrit)(V293_TaskCreateExt_stack_call 108%Z hook 201%Z 202%Z 203%Z 204%Z)))
 (V293_create_enabled_external Rafter aop (fun _=>false) si ci **
  LV 108%Z @ (Tptr Tint32) |->stack **
  V293_create_stack_arguments target argv inputtop options
   (V293_create_enabled_locals bp bc p cpu
     (V293_create_owned_share table(br,Int.zero)p ** V293_create_slot_views table bn br ** F)))tid.
Proof.
 intros Spec sd li r ri tid bt bf bh bg rows tasks hook bp bc table bn br p cpu F Rbefore Rafter aop si ci
 BeforeGood AfterGood target argv inputtop options stack oldpsp Range Frame ResourceFrame Valid Before After before after Lookup.
 eapply V293_OSTaskCreateExt_owned_stack_fragment;try eassumption.
 intros st HS. exact(proj2(V293_create_joint_borrow_priority bt bf table bh bg rows tasks bn(br,Int.zero)(gettopis si)p Range st)HS).
Qed.

Lemma V293_init_three_result_creator_joint : forall slots cd nd bt bf table bl bg rows tasks nesting bpr bh btop bcur reserved frame,
 In cd slots -> init_type cd=Tint8 -> init_block cd=tasks ->
 In nd slots -> init_type nd=Tint8 -> init_block nd=nesting -> tasks<>nesting ->
 V293_rdy_raw_cells(V293_tcb_call_result bl bf bt table
  (V293_rdy_globals bg rows bpr bh btop bcur
   (Vint32 Int.zero)(Vint32 Int.zero)(Vint32 Int.zero)(Vint32 Int.zero)(Vint32 Int.zero)Vnull Vnull++
   V293_misc_zero_cells slots++frame))Atrue ==>
 V293_create_joint_core bt bf table bl bg rows tasks nesting reserved ** V293_rdy_raw_cells frame Atrue.
Proof.
 intros slots cd nd bt bf table bl bg rows tasks nesting bpr bh btop bcur reserved frame
 Count CT CB Nest NT NB Distinct s H.
 apply in_split in Nest. destruct Nest as(before&after&Order). subst slots.
 assert(CountRest:In cd(before++after)).
 { apply in_app_iff. apply in_app_iff in Count. destruct Count as[L|[Same|R]].
   - left;exact L.
   - exfalso;apply Distinct;congruence.
   - right;exact R. }
 assert(OrderMisc:Permutation(V293_misc_zero_cells(before++nd::after)++frame)
  (V293_misc_zero_cells(before++after)++((nesting,0%Z),Tint8,Vint32 Int.zero)::frame)).
 { unfold V293_misc_zero_cells. repeat rewrite map_app. cbn[map]. rewrite NT,NB.
   repeat rewrite <-app_assoc. apply Permutation_app_head. apply Permutation_middle. }
 assert(OrderAll:Permutation
  (V293_tcb_call_result bl bf bt table
   (V293_rdy_globals bg rows bpr bh btop bcur
    (Vint32 Int.zero)(Vint32 Int.zero)(Vint32 Int.zero)(Vint32 Int.zero)(Vint32 Int.zero)Vnull Vnull++
    V293_misc_zero_cells(before++nd::after)++frame))
  (V293_tcb_call_result bl bf bt table
   (V293_rdy_globals bg rows bpr bh btop bcur
    (Vint32 Int.zero)(Vint32 Int.zero)(Vint32 Int.zero)(Vint32 Int.zero)(Vint32 Int.zero)Vnull Vnull++
    V293_misc_zero_cells(before++after)++((nesting,0%Z),Tint8,Vint32 Int.zero)::frame))).
 { unfold V293_tcb_call_result. repeat apply Permutation_app_head. exact OrderMisc. }
 pose proof(V293_raw_cells_permutation _ _ OrderAll Atrue s H)as Reordered.
 eapply V293_init_three_result_joint with(d:=cd)(reserved:=reserved)in Reordered;[ |exact CountRest|exact CT|exact CB].
 unfold V293_create_joint_core. cbn[V293_rdy_raw_cells]in Reordered.
 change(s |= (V293_tcb_joint_core bt bf table bl bg rows tasks reserved **
  Amapsto(nesting,0%Z)Tint8 true(Vint32 Int.zero)) ** V293_rdy_raw_cells frame Atrue).
 clear -Reordered;sep auto.
Qed.

Theorem V293_OSInit_three_calls_creator_joint : forall d nd bcount nesting reserved slots oldtcbs oldprios frame P ks ge caller M ir aux O op
  misc ready tcbs clear dest size group rows prio high top current ri
  bg br bpr bh btop bcur table priorities list_head free_head ix ix_next ptcb1 ptcb2 bt bp bl bf
  vg vlo vhi vp vh vt vc vl vf,
  In d slots -> init_type d=Tint8 -> init_block d=bcount ->
  In nd slots -> init_type nd=Tint8 -> init_block nd=nesting -> bcount<>nesting ->
  Forall V293_init_scalar slots ->
  P misc=Some (Tvoid,dnil,dnil,sseq (V293_init_program slots) sret) ->
  P ready=Some (V293_InitRdyList_function group rows prio high top current ri) ->
  P tcbs=Some (V293_InitTCBList_function clear table priorities list_head free_head ix ix_next ptcb1 ptcb2) ->
  P clear=Some (V293_MemClr_function dest size) -> dest<>size ->
  (ix<ix_next)%Z -> (ix_next<ptcb1)%Z -> (ptcb1<ptcb2)%Z ->
  (forall bi, V293_rdy_env ge (V293_rdy_locals ri bi)
    group rows prio high top current ri bg br bpr bh btop bcur bi) ->
  (forall bi bn b1 b2, V293_tcb_link_env ge (V293_tcb_call_locals ix ix_next ptcb1 ptcb2 bi bn b1 b2)
    table list_head free_head ix ix_next ptcb1 ptcb2 bt bl bf bi bn b1 b2) ->
  (forall bi bn b1 b2, get (V293_tcb_call_locals ix ix_next ptcb1 ptcb2 bi bn b1 b2) priorities=None) ->
  get ge priorities=Some (bp,V293_tcb_prio_table_type) ->
  length oldtcbs=728%nat -> length oldprios=52%nat ->
  (ge,emp,M,ir,aux,O,op) |= V293_init_resources slots false
    (V293_rdy_raw_cells
      (V293_rdy_globals bg br bpr bh btop bcur vg vlo vhi vp vh vt vc++
       V293_clr_bytes bt 0 oldtcbs++V293_clr_bytes bp 0 oldprios++V293_tcb_call_heads bl bf vl vf++frame) Atrue) ->
  exists (Mmisc Mrdy Mf:mem)(bri bi bn b1 b2:block),
    cstepstar P (curs (V293_init_three_calls misc ready tcbs),(kenil,ks)) (ge,caller,M)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    cstepstar P (curs (scall misc nil),(kenil,kseq (sseq (scall ready nil) (scall tcbs nil)) ks)) (ge,caller,M)
      (curs (sskip None),(kenil,kseq (sseq (scall ready nil) (scall tcbs nil)) ks)) (ge,caller,Mmisc) /\
    cstepstar P (curs (scall ready nil),(kenil,kseq (scall tcbs nil) ks)) (ge,caller,Mmisc)
      (curs (sskip None),(kenil,kseq (scall tcbs nil) ks)) (ge,caller,Mrdy) /\
    cstepstar P (curs (scall tcbs nil),(kenil,ks)) (ge,caller,Mrdy)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    (ge,caller,Mf,ir,aux,O,op) |=
      V293_create_joint_core bt bf bp bl bg br bcount nesting reserved ** V293_rdy_raw_cells frame Atrue /\
    get Mrdy (bri,0%Z)=None /\
    (forall c tp k, In (c,tp) [(bi,Tint8);(bn,Tint8);(b1,Tptr V293_tcb_type);(b2,Tptr V293_tcb_type)] ->
      (k<typelen tp)%nat -> get Mf (c,Z.of_nat k)=None).
Proof.
 intros d nd bcount nesting reserved slots oldtcbs oldprios frame P ks ge caller M ir aux O op
  misc ready tcbs clear dest size group rows prio high top current ri
  bg br bpr bh btop bcur table priorities list_head free_head ix ix_next ptcb1 ptcb2 bt bp bl bf
  vg vlo vhi vp vh vt vc vl vf Member Ty Bl Nest NT NB Distinct Scalar Misc Ready TCB Clear DS IX IN PN REnv CEnv NPrio GPrio LT LP Owned.
 destruct(V293_OSInit_three_calls slots oldtcbs oldprios frame P ks ge caller M ir aux O op
  misc ready tcbs clear dest size group rows prio high top current ri
  bg br bpr bh btop bcur table priorities list_head free_head ix ix_next ptcb1 ptcb2 bt bp bl bf
  vg vlo vhi vp vh vt vc vl vf Scalar Misc Ready TCB Clear DS IX IN PN REnv CEnv NPrio GPrio LT LP Owned)
  as(Mmisc&Mrdy&Mf&bri&bi&bn&b1&b2&Exec&EM&ER&ET&Final&FR&FT).
 exists Mmisc. exists Mrdy. exists Mf. exists bri. exists bi. exists bn. exists b1. exists b2.
 repeat split;try assumption.
 eapply V293_init_three_result_creator_joint;[exact Member|exact Ty|exact Bl|exact Nest|exact NT|exact NB|exact Distinct|exact Final].
Qed.
Print Assumptions V293_OSInit_three_calls_creator_joint.
