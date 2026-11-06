(* Independent enabled whole-function entry and one-Spec composition checks.
   Finite counter0/empty-allocator scope, not production Inv or initialization. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEnabledSlotPool.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEnabledReject.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReservationOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEnabledFailure.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateFailureHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.tactics.hoareforward.init_spec.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEnabledOwned.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateRejectInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEmptyInternal.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateBodyFailure.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Definition EOBaseGE : env := set (set (sig 91%Z (401%positive,Tptr V293_tcb_type))
 OSTCBCur (402%positive,Tptr Tvoid)) 92%Z (403%positive,Tarray(Tptr V293_tcb_type)13).
Definition EOGE : env := set(set EOBaseGE 99%Z(404%positive,Tint8))97%Z(405%positive,Tint8).
Definition EOBaseLE : env := set (set (set (set (set (set (set (sig 101%Z (201%positive,Tint8)) 108%Z (208%positive,Tptr Tint32)) 205%Z (205%positive,Tptr Tint32)) 206%Z (206%positive,Tint16)) 207%Z (207%positive,Tint32)) 208%Z (210%positive,Tptr Tvoid)) 204%Z (204%positive,Tint16)) 209%Z (209%positive,Tint8).
Definition EOLE : env := set(set(set(set EOBaseLE
 201%Z(211%positive,Tint32))202%Z(212%positive,Tptr Tvoid))
 203%Z(213%positive,Tptr Tint32))109%Z(214%positive,Tint32).
Definition EOTid : tid := (301%positive,Int.repr 8).
Definition EOBytes b permission tp v := V293_encoded_memory b 0 permission(encode_val tp v).
Definition EOState le M cs : RstateOP :=
 (EOGE,le,M,(fun _=>false),(true,nil,cs),(emp:osabst),spec_done None).
Definition EOCurrent := EOBytes 402%positive false(Tptr Tvoid)(Vptr EOTid).
Definition EOSentinel := EOBytes 601%positive true Tint8(Vint32(Int.repr 77)).
Definition EOOuter := merge EOCurrent EOSentinel.
Definition EOR := CurTid EOTid ** LINV V293_witness_li EOTid nil **
 Amapsto(601%positive,0%Z)Tint8 true(Vint32(Int.repr 77)).
Lemma EOStar : forall le m1 m2 m cs p q,
 join m1 m2 m -> EOState le m1 cs |= p -> EOState le m2 cs |= q -> EOState le m cs |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2. exists(emp:osabst). exists(emp:osabst).
 split;[exact H| ]. split;[apply map_join_emp| ]. split;assumption.
Qed.
Lemma EOLocal : forall le x b tp v cs,
 get le x=Some(b,tp) -> EOState le(EOBytes b true tp v)cs |= LV x @ tp |->v.
Proof.
 intros le x b tp v cs E. unfold Alvarmapsto,Alvarenv'. exists b.
 eapply EOStar with(m1:=emp)(m2:=EOBytes b true tp v).
 - apply map_join_comm;apply map_join_emp.
 - exists b. split;[exact E| ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma EORSpatial : forall le cs, EOState le EOOuter cs |= EOR.
Proof.
 intros le cs. unfold EOR,EOOuter.
 eapply EOStar with(m1:=EOCurrent)(m2:=EOSentinel).
 - apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 402%positive);[subst b;right;left|left];
   unfold EOCurrent,EOSentinel,EOBytes;apply V293_encoded_memory_outside;left;congruence.
 - unfold CurTid. exists Tvoid. exists 402%positive.
   eapply EOStar with(m1:=emp)(m2:=EOCurrent).
   + apply map_join_comm;apply map_join_emp.
   + exists 402%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply EOStar with(m1:=emp)(m2:=EOSentinel).
   + apply map_join_comm;apply map_join_emp.
   + unfold LINV. apply astar_comm. apply astar_l_apure_intro.
     * split;reflexivity.
     * apply V293_witness_li_good.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma EORGood : GoodFrm EOR.
Proof. cbn[EOR CurTid LINV V293_witness_li GoodFrm];repeat split;exact I. Qed.
Lemma EORFun : GoodFunAsrt EOR.
Proof.
 cbn[EOR CurTid LINV V293_witness_li GoodFunAsrt Agvarmapsto Agvarenv' Aptrmapsto].
 repeat split;intros;repeat split;exact I.
Qed.
Lemma EORInv : EOR ==> CurLINV V293_witness_li EOTid.
Proof. intros s H. unfold CurLINV. exists(nil:list logicvar). unfold EOR in H;clear -H;sep auto. Qed.
Definition EOFree := EOBytes 401%positive false(Tptr V293_tcb_type)Vnull.
Definition EOReserved : addrval := (405%positive,Int.zero).
Definition EOCounter := EOBytes 404%positive true Tint8(V293_byteval 0).
Definition EOOwner := V293_encoded_memory 403%positive 44 false(encode_val(Tptr V293_tcb_type)(Vptr EOReserved)).
Definition EOSlot slot := V293_encoded_memory 403%positive 44(V293_reservation_permission EOReserved slot)(encode_val(Tptr V293_tcb_type)slot).
Definition EOCore := V293_tcb_empty_pool 401%positive(V293_create_owned_pool 403%positive EOReserved 11(Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0))).
Lemma EOBytesUnique : forall vl l permission m1 m2,
 ptomvallist l permission vl m1 -> ptomvallist l permission vl m2 -> m1=m2.
Proof.
 induction vl as [ |head tail IH];intros[b off] permission m1 m2 H1 H2.
 - cbn[ptomvallist]in *;congruence.
 - cbn[ptomvallist]in H1,H2.
   destruct H1 as[a1[t1[J1[P1 T1]]]]. destruct H2 as[a2[t2[J2[P2 T2]]]].
   unfold ptomval in P1,P2. subst a1 a2.
   assert(E:t1=t2)by(eapply IH;eauto). subst t2.
   eapply map_join_deter;eauto.
Qed.
Lemma EOHeadPrecise : precise(Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull).
Proof.
 intros s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 destruct s as [[[[[[ge le] mem] ir] aux] oldO] op].
 change(mapstoval(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull M1 /\ O1=emp)in H1.
 change(mapstoval(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull M2 /\ O2=emp)in H2.
 destruct H1 as[[v1[E1 P1]]Oe1]. destruct H2 as[[v2[E2 P2]]Oe2].
 subst v1 v2. split;[eapply EOBytesUnique;eauto|congruence].
Qed.
Lemma EOCounterPrecise : precise(Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0)).
Proof.
 intros s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 destruct s as [[[[[[ge le] mem] ir] aux] oldO] op].
 change(mapstoval(404%positive,0%Z)Tint8 true(V293_byteval 0)M1 /\ O1=emp)in H1.
 change(mapstoval(404%positive,0%Z)Tint8 true(V293_byteval 0)M2 /\ O2=emp)in H2.
 destruct H1 as[[v1[E1 P1]]Oe1]. destruct H2 as[[v2[E2 P2]]Oe2].
 subst v1 v2. split;[eapply V293_reservation_bytes_exact;eauto|congruence].
Qed.
Lemma EOCorePrecise : precise EOCore.
Proof.
 unfold EOCore,V293_tcb_empty_pool,V293_create_owned_pool. apply precise_star;[apply EOHeadPrecise| ].
 apply precise_star;[apply V293_reservation_pool_precise|apply EOCounterPrecise].
Qed.
Lemma EOCoreGood : GoodInvAsrt EOCore.
Proof. cbn[EOCore V293_tcb_empty_pool V293_create_owned_pool V293_reservation_pool GoodInvAsrt];tauto. Qed.
Lemma EOCoreISR : assertion.inv_isr_prop EOCore.
Proof.
 unfold assertion.inv_isr_prop,EOCore,V293_tcb_empty_pool,V293_create_owned_pool,V293_reservation_pool.
 repeat split;intros;destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];exact H.
Qed.
Definition EOInv : Inv := fun i=>match i with
 | O=>mkinvasrt EOCoreGood(conj EOCorePrecise EOCoreISR)
 | S j=>V293_shared_inv(S j) end.
Lemma EONoisrTail : forall n i,starinv_noisr EOInv(S i)n <==> Aemp.
Proof.
 induction n;intros i s;cbn[starinv_noisr];[reflexivity| ].
 change(s |= Aemp ** starinv_noisr EOInv(S(S i))n <-> s |= Aemp).
 split;intro H.
 - apply astar_l_aemp_elim in H. apply IHn in H;exact H.
 - apply astar_l_aemp_intro. apply IHn;exact H.
Qed.
Lemma EONoisrCore : forall n,starinv_noisr EOInv 0 n <==> EOCore.
Proof.
 intros[ |n]s;[reflexivity| ].
 change(s |= EOCore ** starinv_noisr EOInv 1 n <-> s |= EOCore).
 split;intro H.
 - apply astar_r_aemp_elim. eapply astar_mono;[intros st HS;exact HS|intros st HS;apply EONoisrTail in HS;exact HS|exact H].
 - eapply astar_mono;[intros st HS;exact HS|intros st HS;apply EONoisrTail;exact HS| ]. apply astar_r_aemp_intro;exact H.
Qed.
Theorem EOBorrowEquivalence : forall n,
 Aisr(fun _=>false) ** invlth_isr EOInv 0 n <==> Aisr(fun _=>false) ** EOCore.
Proof.
 intros n s. destruct s as [[[[[[ge le] M] ir] aux] O] op]. split;intro H.
 all:(apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&H1&H2);
 destruct H1 as[E Empty];cbn in E;subst ir;
 apply sat_split';exists m1;exists m2;exists o1;exists o2;
 split;[exact JM| ];split;[exact JO| ];split;[split;[reflexivity|exact Empty]| ]).
 - unfold invlth_isr in H2. rewrite Nat.sub_0_r in H2.
   apply EONoisrCore with(n:=n). eapply invisr_imply_noisr';[ |exact H2]. reflexivity.
 - unfold invlth_isr. rewrite Nat.sub_0_r.
   apply V293_shared_clear_noisr_close;[reflexivity| ]. apply EONoisrCore;exact H2.
Qed.
Theorem EOSharedLiteral : forall le cs slot,
 rule_type_val_match(Tptr V293_tcb_type)slot=true ->
 EOState le(merge EOFree(merge(EOSlot slot)EOCounter))cs |= invlth_isr EOInv 0 INUM.
Proof.
 intros le cs slot Typed. unfold invlth_isr. rewrite Nat.sub_0_r.
 apply V293_shared_clear_noisr_close;[reflexivity| ]. apply EONoisrCore.
 unfold EOCore,V293_tcb_empty_pool,V293_create_owned_pool.
 eapply EOStar with(m1:=EOFree)(m2:=merge(EOSlot slot)EOCounter).
 - apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 401%positive);[subst b;right;left|left];
   unfold EOFree,EOSlot,EOCounter,EOBytes;
   repeat first[rewrite map_merge_semp by reflexivity|rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply EOStar with(m1:=EOSlot slot)(m2:=EOCounter).
   + apply map_join_merge;apply map_disjoint;intros[b off].
     destruct(Pos.eq_dec b 403%positive);[subst b;right;left|left];
     unfold EOSlot,EOCounter,EOBytes;apply V293_encoded_memory_outside;left;congruence.
   + exists slot. apply astar_l_apure_intro;[ |exact Typed].
     split;[apply V293_encoded_memory_mapsto|reflexivity].
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Theorem EOSameInvariantFreeReservedOther : forall le cs,
 EOState le(merge EOFree(merge(EOSlot Vnull)EOCounter))cs |= invlth_isr EOInv 0 INUM /\
 EOState le(merge EOFree(merge(EOSlot(Vptr EOReserved))EOCounter))cs |= invlth_isr EOInv 0 INUM /\
 EOState le(merge EOFree(merge(EOSlot(Vptr(701%positive,Int.zero)))EOCounter))cs |= invlth_isr EOInv 0 INUM.
Proof. intros;repeat split;apply EOSharedLiteral;reflexivity. Qed.

Theorem EOOwnedBorrowEquivalence : forall n,
 Aisr(fun _=>false) ** invlth_isr EOInv 0 n <==>
 Aisr(fun _=>false) ** V293_create_owned_pool 403%positive EOReserved 11
   (Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull **
    Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0)).
Proof.
 intros n s. split;intro H.
 - apply EOBorrowEquivalence in H. unfold EOCore,V293_tcb_empty_pool,V293_create_owned_pool in *;clear -H;sep auto.
 - apply EOBorrowEquivalence. unfold EOCore,V293_tcb_empty_pool,V293_create_owned_pool in *;clear -H;sep auto.
Qed.
Definition EOHookBefore cs := @mkfunasrt
 (V293_create_enabled_external EOR(spec_done None)(fun _=>false)nil cs)
 (V293_create_enabled_external_good EOR(spec_done None)(fun _=>false)nil cs EORFun).
Definition EOHookArgs := V293_create_stack_values 5 Vnull Vnull(Vint32(Int.repr 7)).
Definition EOSpec cs : funspec := fun f=>if Z.eq_dec f 500%Z then
 Some(V293_tcb_enabled_fpre 401%positive EOR(spec_done None)(fun _=>false)nil cs EORFun,
      V293_tcb_enabled_fpost 401%positive EOR(spec_done None)(fun _=>false)nil cs EORFun,
      (Tint8,rev V293_TCBInit_argument_types))
 else if Z.eq_dec f 600%Z then
 Some(V293_create_stack_resource_fpre(EOHookBefore cs)EOHookArgs,
      V293_create_stack_resource_fpost(EOHookBefore cs)EOHookArgs Vnull,
      (Tptr Tint32,rev V293_stack_argument_types)) else None.
Definition EOProgram : progunit := fun f=>if Z.eq_dec f 500%Z then
 Some(V293_TCBInit_function 501%Z 502%Z)
 else if Z.eq_dec f 700%Z then
 Some(V293_CreateExt_function 92%Z 99%Z 97%Z 98%Z 601%Z 600%Z 500%Z)else None.
Definition EOArgs := rev(V293_tcb_success_arguments 11 Vnull Vnull
 (Vint32(Int.repr 4))(Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7))).
Definition EOPre cs := V293_tcb_internal_pre_cells(V293_byteval 11)Vnull Vnull
 (Vint32(Int.repr 4))(Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7)) **
 V293_tcb_enabled_external 401%positive EOR(spec_done None)(fun _=>false)nil cs ** V293_tcb_internal_domain.
Definition EOPost cs result := V293_tcb_internal_post_cells **
 ([|result=Some(Vint32(Int.repr 66))|] **
 V293_tcb_enabled_external 401%positive EOR(spec_done None)(fun _=>false)nil cs) ** V293_tcb_internal_domain.
Lemma EOBuilders : forall cs,
 Some(EOPre cs)=BuildPreI EOProgram 500%Z EOArgs nil
 (V293_tcb_enabled_fpre 401%positive EOR(spec_done None)(fun _=>false)nil cs EORFun)EOTid /\
 Some(EOPost cs)=BuildRetI EOProgram 500%Z EOArgs nil
 (V293_tcb_enabled_fpost 401%positive EOR(spec_done None)(fun _=>false)nil cs EORFun)EOTid.
Proof. intros;split;reflexivity. Qed.
Theorem EOCalleeCheckedSameSpec : forall sd cs,
 InfRules(EOSpec cs)sd V293_witness_li EOInv(EOPost cs)Afalse
 (EOPre cs)(V293_TCBInit_function_body 501%Z 502%Z)Afalse EOTid.
Proof.
 intros sd cs. eapply V293_OS_TCBInit_empty_enabled_contract
 with(P:=EOProgram)(f:=500%Z)(K:=V293_create_owned_pool 403%positive EOReserved 11(Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0)))
 (good:=EORFun)(vl:=EOArgs)(lg:=nil)(bf:=401%positive)(R:=EOR)
 (aop:=spec_done None)(isr:=fun _=>false)(is:=nil)(cs:=cs).
 - vm_compute;lia.
 - apply EORGood.
 - apply EORInv.
 - intros s H;apply EOBorrowEquivalence in H;exact H.
 - intros s H;apply EOBorrowEquivalence;exact H.
 - reflexivity.
 - apply(proj1(EOBuilders cs)).
 - apply(proj2(EOBuilders cs)).
Qed.


Definition EOCreatorArgs := rev(V293_create_internal_values 5 Vnull Vnull 11
 (Vint32(Int.repr 4))Vnull(Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7))).
Definition EOGlobals := V293_create_owned_globals 401%positive 403%positive 404%positive 405%positive EOR.
Definition EOGlobalsGood := V293_create_owned_globals_good 401%positive 403%positive 404%positive 405%positive EOR EORFun.
Definition EOEnabledPre cs := V293_create_internal_pre_cells 5 Vnull Vnull 11
 (Vint32(Int.repr 4))Vnull(Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7)) **
 ([|rev EOCreatorArgs=rev EOCreatorArgs|] **
 V293_create_enabled_external EOGlobals(spec_done None)(fun _=>false)nil cs) ** V293_create_internal_domain.
Definition EOEnabledPost cs result := V293_create_internal_post_cells **
 V293_create_owned_post 401%positive 403%positive 404%positive 405%positive EOR EOR
 (spec_done None)(fun _=>false)nil cs result ** V293_create_internal_domain.
Lemma EOEnabledBuilders : forall cs,
 Some(EOEnabledPre cs)=BuildPreI EOProgram 700%Z EOCreatorArgs nil
 (V293_create_enabled_fpre 5 Vnull Vnull 11(Vint32(Int.repr 4))Vnull(Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7))
 EOGlobals(spec_done None)(fun _=>false)nil cs EOGlobalsGood)EOTid /\
 Some(EOEnabledPost cs)=BuildRetI EOProgram 700%Z EOCreatorArgs nil
 (V293_create_owned_fpost 401%positive 403%positive 404%positive 405%positive EOR EOR
 (spec_done None)(fun _=>false)nil cs EORFun EORFun)EOTid.
Proof. intros;split;reflexivity. Qed.
Theorem EOEnabledCheckedSameSpec : forall sd cs,
 InfRules(EOSpec cs)sd V293_witness_li EOInv(EOEnabledPost cs)Afalse
 (EOEnabledPre cs)(V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z 601%Z 600%Z 500%Z)Afalse EOTid.
Proof.
 intros sd cs. eapply V293_OSTaskCreateExt_enabled_owned_contract
 with(P:=EOProgram)(creator:=700%Z)(K:=Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull)
 (BeforeGood:=EORFun)(AfterGood:=EORFun)(vl:=EOCreatorArgs)(lg:=nil)
 (bf:=401%positive)(table:=403%positive)(bn:=404%positive)(br:=405%positive)
 (p:=11%nat)(Rbefore:=EOR)(Rafter:=EOR)
 (aop:=spec_done None)(ir:=fun _=>false)(si:=nil)(ci:=cs)
 (target:=5%Z)(argv:=Vnull)(inputtop:=Vnull)(options:=Vint32(Int.repr 7))(stack:=Vnull)
 (identity:=Vint32(Int.repr 4))(bottom:=Vnull)(size:=Vint32(Int.repr 5))(ext:=Vnull).
 - lia.
 - vm_compute;lia.
 - apply EORGood.
 - apply EORGood.
 - vm_compute;auto.
 - unfold V293_tcb_init_values_valid;vm_compute;repeat split;reflexivity.
 - apply EORInv.
 - apply EORInv.
 - intro Range. intros s;split;intro H.
   + apply EOBorrowEquivalence in H.
     unfold EOCore,V293_tcb_empty_pool,V293_create_owned_pool in *;clear -H;sep auto.
   + apply EOBorrowEquivalence.
     unfold EOCore,V293_tcb_empty_pool,V293_create_owned_pool in *;clear -H;sep auto.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - apply(proj1(EOEnabledBuilders cs)).
 - apply(proj2(EOEnabledBuilders cs)).
Qed.

Lemma EOExactDomain : eq_dom_env EOLE(getlenvdom V293_create_internal_declarations).
Proof.
 unfold eq_dom_env. intros x tp.
 destruct(Z.eq_dec x 109%Z)as[E109|E109].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold EOLE,EOBaseLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 203%Z)as[E203|E203].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold EOLE,EOBaseLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 202%Z)as[E202|E202].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold EOLE,EOBaseLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 201%Z)as[E201|E201].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold EOLE,EOBaseLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 209%Z)as[E209|E209].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold EOLE,EOBaseLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 204%Z)as[E204|E204].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold EOLE,EOBaseLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 208%Z)as[E208|E208].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold EOLE,EOBaseLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 207%Z)as[E207|E207].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold EOLE,EOBaseLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 206%Z)as[E206|E206].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold EOLE,EOBaseLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 205%Z)as[E205|E205].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold EOLE,EOBaseLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 108%Z)as[E108|E108].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold EOLE,EOBaseLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 101%Z)as[E101|E101].
 { subst x. cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold EOLE,EOBaseLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 cbn[V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
 unfold EOLE,EOBaseLE. repeat rewrite map_get_set' by congruence. rewrite map_get_sig' by congruence.
 split.
 - intro H. repeat destruct H as[H|H];try contradiction;inversion H;congruence.
 - intros[b H];discriminate.
Qed.
Definition EOEntryLocal101 := EOBytes 201%positive true(Tint8)(V293_byteval 11).
Definition EOEntryLocal109 := EOBytes 214%positive true(Tint32)(Vint32(Int.repr 99)).
Definition EOEntryLocal108 := EOBytes 208%positive true(Tptr Tint32)(Vnull).
Definition EOEntryLocal205 := EOBytes 205%positive true(Tptr Tint32)(Vnull).
Definition EOEntryLocal206 := EOBytes 206%positive true(Tint16)(Vint32(Int.repr 4)).
Definition EOEntryLocal207 := EOBytes 207%positive true(Tint32)(Vint32(Int.repr 5)).
Definition EOEntryLocal208 := EOBytes 210%positive true(Tptr Tvoid)(Vnull).
Definition EOEntryLocal204 := EOBytes 204%positive true(Tint16)(Vint32(Int.repr 7)).
Definition EOEntryLocal209 := EOBytes 209%positive true(Tint8)(Vundef).
Definition EOEntryLocal201 := EOBytes 211%positive true(Tint32)(V293_task_selector 5).
Definition EOEntryLocal202 := EOBytes 212%positive true(Tptr Tvoid)(Vnull).
Definition EOEntryLocal203 := EOBytes 213%positive true(Tptr Tint32)(Vnull).
Definition EOEntryMemory := merge EOEntryLocal101(merge EOEntryLocal109(merge EOEntryLocal108(merge EOEntryLocal205(merge EOEntryLocal206(merge EOEntryLocal207(merge EOEntryLocal208(merge EOEntryLocal204(merge EOEntryLocal209(merge EOEntryLocal201(merge EOEntryLocal202(merge EOEntryLocal203(EOOuter)))))))))))).
Lemma EOMergeAbsent : forall(m1 m2:mem)a,
 get m1 a=None -> get m2 a=None -> get(merge m1 m2)a=None.
Proof. intros. rewrite map_merge_semp by reflexivity. rewrite H,H0. reflexivity. Qed.
Lemma EOEntryBytes : EOState EOLE EOEntryMemory nil |=
LV 101%Z @ (Tint8) |->(V293_byteval 11) **
 (LV 109%Z @ (Tint32) |->(Vint32(Int.repr 99)) **
 (LV 108%Z @ (Tptr Tint32) |->(Vnull) **
 (LV 205%Z @ (Tptr Tint32) |->(Vnull) **
 (LV 206%Z @ (Tint16) |->(Vint32(Int.repr 4)) **
 (LV 207%Z @ (Tint32) |->(Vint32(Int.repr 5)) **
 (LV 208%Z @ (Tptr Tvoid) |->(Vnull) **
 (LV 204%Z @ (Tint16) |->(Vint32(Int.repr 7)) **
 (LV 209%Z @ (Tint8) |->(Vundef) **
 (LV 201%Z @ (Tint32) |->(V293_task_selector 5) **
 (LV 202%Z @ (Tptr Tvoid) |->(Vnull) **
 (LV 203%Z @ (Tptr Tint32) |->(Vnull) **
 (EOR)))))))))))).
Proof.
 unfold EOEntryMemory.
 eapply EOStar with(m1:=EOEntryLocal101).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 201%positive);[subst other;right;left|left];
   unfold EOEntryLocal101,EOEntryLocal109,EOEntryLocal108,EOEntryLocal205,EOEntryLocal206,EOEntryLocal207,EOEntryLocal208,EOEntryLocal204,EOEntryLocal209,EOEntryLocal201,EOEntryLocal202,EOEntryLocal203,EOOuter,EOCurrent,EOSentinel,EOBytes;
   repeat apply EOMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply EOLocal;vm_compute;reflexivity. }
 eapply EOStar with(m1:=EOEntryLocal109).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 214%positive);[subst other;right;left|left];
   unfold EOEntryLocal101,EOEntryLocal109,EOEntryLocal108,EOEntryLocal205,EOEntryLocal206,EOEntryLocal207,EOEntryLocal208,EOEntryLocal204,EOEntryLocal209,EOEntryLocal201,EOEntryLocal202,EOEntryLocal203,EOOuter,EOCurrent,EOSentinel,EOBytes;
   repeat apply EOMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply EOLocal;vm_compute;reflexivity. }
 eapply EOStar with(m1:=EOEntryLocal108).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 208%positive);[subst other;right;left|left];
   unfold EOEntryLocal101,EOEntryLocal109,EOEntryLocal108,EOEntryLocal205,EOEntryLocal206,EOEntryLocal207,EOEntryLocal208,EOEntryLocal204,EOEntryLocal209,EOEntryLocal201,EOEntryLocal202,EOEntryLocal203,EOOuter,EOCurrent,EOSentinel,EOBytes;
   repeat apply EOMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply EOLocal;vm_compute;reflexivity. }
 eapply EOStar with(m1:=EOEntryLocal205).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 205%positive);[subst other;right;left|left];
   unfold EOEntryLocal101,EOEntryLocal109,EOEntryLocal108,EOEntryLocal205,EOEntryLocal206,EOEntryLocal207,EOEntryLocal208,EOEntryLocal204,EOEntryLocal209,EOEntryLocal201,EOEntryLocal202,EOEntryLocal203,EOOuter,EOCurrent,EOSentinel,EOBytes;
   repeat apply EOMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply EOLocal;vm_compute;reflexivity. }
 eapply EOStar with(m1:=EOEntryLocal206).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 206%positive);[subst other;right;left|left];
   unfold EOEntryLocal101,EOEntryLocal109,EOEntryLocal108,EOEntryLocal205,EOEntryLocal206,EOEntryLocal207,EOEntryLocal208,EOEntryLocal204,EOEntryLocal209,EOEntryLocal201,EOEntryLocal202,EOEntryLocal203,EOOuter,EOCurrent,EOSentinel,EOBytes;
   repeat apply EOMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply EOLocal;vm_compute;reflexivity. }
 eapply EOStar with(m1:=EOEntryLocal207).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 207%positive);[subst other;right;left|left];
   unfold EOEntryLocal101,EOEntryLocal109,EOEntryLocal108,EOEntryLocal205,EOEntryLocal206,EOEntryLocal207,EOEntryLocal208,EOEntryLocal204,EOEntryLocal209,EOEntryLocal201,EOEntryLocal202,EOEntryLocal203,EOOuter,EOCurrent,EOSentinel,EOBytes;
   repeat apply EOMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply EOLocal;vm_compute;reflexivity. }
 eapply EOStar with(m1:=EOEntryLocal208).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 210%positive);[subst other;right;left|left];
   unfold EOEntryLocal101,EOEntryLocal109,EOEntryLocal108,EOEntryLocal205,EOEntryLocal206,EOEntryLocal207,EOEntryLocal208,EOEntryLocal204,EOEntryLocal209,EOEntryLocal201,EOEntryLocal202,EOEntryLocal203,EOOuter,EOCurrent,EOSentinel,EOBytes;
   repeat apply EOMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply EOLocal;vm_compute;reflexivity. }
 eapply EOStar with(m1:=EOEntryLocal204).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 204%positive);[subst other;right;left|left];
   unfold EOEntryLocal101,EOEntryLocal109,EOEntryLocal108,EOEntryLocal205,EOEntryLocal206,EOEntryLocal207,EOEntryLocal208,EOEntryLocal204,EOEntryLocal209,EOEntryLocal201,EOEntryLocal202,EOEntryLocal203,EOOuter,EOCurrent,EOSentinel,EOBytes;
   repeat apply EOMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply EOLocal;vm_compute;reflexivity. }
 eapply EOStar with(m1:=EOEntryLocal209).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 209%positive);[subst other;right;left|left];
   unfold EOEntryLocal101,EOEntryLocal109,EOEntryLocal108,EOEntryLocal205,EOEntryLocal206,EOEntryLocal207,EOEntryLocal208,EOEntryLocal204,EOEntryLocal209,EOEntryLocal201,EOEntryLocal202,EOEntryLocal203,EOOuter,EOCurrent,EOSentinel,EOBytes;
   repeat apply EOMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply EOLocal;vm_compute;reflexivity. }
 eapply EOStar with(m1:=EOEntryLocal201).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 211%positive);[subst other;right;left|left];
   unfold EOEntryLocal101,EOEntryLocal109,EOEntryLocal108,EOEntryLocal205,EOEntryLocal206,EOEntryLocal207,EOEntryLocal208,EOEntryLocal204,EOEntryLocal209,EOEntryLocal201,EOEntryLocal202,EOEntryLocal203,EOOuter,EOCurrent,EOSentinel,EOBytes;
   repeat apply EOMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply EOLocal;vm_compute;reflexivity. }
 eapply EOStar with(m1:=EOEntryLocal202).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 212%positive);[subst other;right;left|left];
   unfold EOEntryLocal101,EOEntryLocal109,EOEntryLocal108,EOEntryLocal205,EOEntryLocal206,EOEntryLocal207,EOEntryLocal208,EOEntryLocal204,EOEntryLocal209,EOEntryLocal201,EOEntryLocal202,EOEntryLocal203,EOOuter,EOCurrent,EOSentinel,EOBytes;
   repeat apply EOMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply EOLocal;vm_compute;reflexivity. }
 eapply EOStar with(m1:=EOEntryLocal203).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 213%positive);[subst other;right;left|left];
   unfold EOEntryLocal101,EOEntryLocal109,EOEntryLocal108,EOEntryLocal205,EOEntryLocal206,EOEntryLocal207,EOEntryLocal208,EOEntryLocal204,EOEntryLocal209,EOEntryLocal201,EOEntryLocal202,EOEntryLocal203,EOOuter,EOCurrent,EOSentinel,EOBytes;
   repeat apply EOMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply EOLocal;vm_compute;reflexivity. }
 apply EORSpatial.
Qed.
Lemma EOEntryViews : EOState EOLE emp nil |=
 OS[(fun _=>false),true,nil,nil] ** <||spec_done None||> **
 Agvarenv 91%Z(Tptr V293_tcb_type)(401%positive,0%Z) **
 Agvarenv 99%Z Tint8(404%positive,0%Z) **
 Agvarenv 92%Z(Tarray(Tptr V293_tcb_type)13)(403%positive,0%Z) **
 Agvarenv 97%Z Tint8(405%positive,0%Z) ** V293_create_internal_domain.
Proof.
 eapply EOStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 { assert(E:EOState EOLE emp nil |= Aemp)by(split;reflexivity).
   assert(S:EOState EOLE emp nil |=
    Aisr(fun _=>false) ** Aie true ** Ais nil ** Acs nil ** Aemp).
   { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
     apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[exact E|reflexivity]. }
   clear -S;sep auto. }
 eapply EOStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 { apply astar_r_aemp_elim. apply astar_l_aop'_intro;[split;reflexivity|reflexivity]. }
 eapply EOStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 { exists 401%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity. }
 eapply EOStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 { exists 404%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity. }
 eapply EOStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 { exists 403%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity. }
 eapply EOStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 { exists 405%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity. }
 split;[apply EOExactDomain|split;reflexivity].
Qed.
Theorem EOEnabledEntryLiteral : EOState EOLE EOEntryMemory nil |= EOEnabledPre nil.
Proof.
 assert(B:=EOEntryBytes). assert(G:=EOEntryViews).
 assert(J:join(emp:mem)EOEntryMemory EOEntryMemory)by(apply map_join_comm;apply map_join_emp).
 pose proof(EOStar EOLE emp EOEntryMemory EOEntryMemory nil _ _ J G B)as H.
 unfold EOEnabledPre,EOGlobals,V293_create_internal_pre_cells,V293_create_internal_locals,
 V293_create_enabled_external,V293_create_owned_globals,V293_create_slot_globals.
 cbn[V293_create_rejection_globals]. clear -H;sep auto.
Qed.
Theorem EOCallerHasNoSharedBytes : forall off,
 get EOEntryMemory(401%positive,off)=None /\
 get EOEntryMemory(403%positive,off)=None /\
 get EOEntryMemory(404%positive,off)=None.
Proof.
 intro off. unfold EOEntryMemory,EOEntryLocal101,EOEntryLocal109,EOEntryLocal108,EOEntryLocal205,EOEntryLocal206,EOEntryLocal207,EOEntryLocal208,EOEntryLocal204,EOEntryLocal209,EOEntryLocal201,EOEntryLocal202,EOEntryLocal203,EOOuter,EOCurrent,EOSentinel,EOBytes.
 repeat split;repeat apply EOMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get].
Qed.
Theorem EOEnabledSharedCompatible : forall slot,
 rule_type_val_match(Tptr V293_tcb_type)slot=true ->
 join EOEntryMemory(merge EOFree(merge(EOSlot slot)EOCounter))
  (merge EOEntryMemory(merge EOFree(merge(EOSlot slot)EOCounter))).
Proof.
 intros slot Typed. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 401%positive);[subst b;left;exact(proj1(EOCallerHasNoSharedBytes off))| ].
 destruct(Pos.eq_dec b 403%positive);[subst b;left;exact(proj1(proj2(EOCallerHasNoSharedBytes off)))| ].
 destruct(Pos.eq_dec b 404%positive);[subst b;left;exact(proj2(proj2(EOCallerHasNoSharedBytes off)))| ].
 right;left. unfold EOFree,EOSlot,EOCounter,EOBytes.
 repeat apply EOMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get].
Qed.

(* Prospective single-factor control: only the compared slot bytes are removed.
   This is a typed-load observation, not a mutant API/interrupt execution. *)
Definition EOComparisonInput := EOSlot(Vptr EOReserved).
Theorem EOComparisonInputReads :
 load(Tptr V293_tcb_type)EOComparisonInput(403%positive,44%Z)=Some(Vptr EOReserved).
Proof. eapply mapstoval_load;[reflexivity|apply V293_encoded_memory_mapsto]. Qed.
Theorem EOComparisonBytesRemoved :
 load(Tptr V293_tcb_type)(emp:mem)(403%positive,44%Z)=None.
Proof. reflexivity. Qed.
Theorem EOComparisonReadNeedsBytes :
 load(Tptr V293_tcb_type)(emp:mem)(403%positive,44%Z)<>
 load(Tptr V293_tcb_type)EOComparisonInput(403%positive,44%Z).
Proof. rewrite EOComparisonInputReads,EOComparisonBytesRemoved;discriminate. Qed.
