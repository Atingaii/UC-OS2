(* Independent literal critical-entry and one-Spec composition checks.
   This is not a production invariant, full creator entry or initialization. *)
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
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateOwnedEmpty.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateBodyFailure.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Definition OEBaseGE : env := set (set (sig 91%Z (401%positive,Tptr V293_tcb_type))
 OSTCBCur (402%positive,Tptr Tvoid)) 92%Z (403%positive,Tarray(Tptr V293_tcb_type)13).
Definition OEGE : env := set(set OEBaseGE 99%Z(404%positive,Tint8))97%Z(405%positive,Tint8).
Definition OEBaseLE : env := set (set (set (set (set (set (set (sig 101%Z (201%positive,Tint8)) 108%Z (208%positive,Tptr Tint32)) 205%Z (205%positive,Tptr Tint32)) 206%Z (206%positive,Tint16)) 207%Z (207%positive,Tint32)) 208%Z (210%positive,Tptr Tvoid)) 204%Z (204%positive,Tint16)) 209%Z (209%positive,Tint8).
Definition OELE : env := set(set(set(set OEBaseLE
 201%Z(211%positive,Tint32))202%Z(212%positive,Tptr Tvoid))
 203%Z(213%positive,Tptr Tint32))109%Z(214%positive,Tint32).
Definition OETid : tid := (301%positive,Int.repr 8).
Definition OEBytes b permission tp v := V293_encoded_memory b 0 permission(encode_val tp v).
Definition OEState le M cs : RstateOP :=
 (OEGE,le,M,(fun _=>false),(false,nil,cs),(emp:osabst),spec_done None).
Definition OECurrent := OEBytes 402%positive false(Tptr Tvoid)(Vptr OETid).
Definition OESentinel := OEBytes 601%positive true Tint8(Vint32(Int.repr 77)).
Definition OEOuter := merge OECurrent OESentinel.
Definition OER := CurTid OETid ** LINV V293_witness_li OETid nil **
 Amapsto(601%positive,0%Z)Tint8 true(Vint32(Int.repr 77)).
Lemma OEStar : forall le m1 m2 m cs p q,
 join m1 m2 m -> OEState le m1 cs |= p -> OEState le m2 cs |= q -> OEState le m cs |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2. exists(emp:osabst). exists(emp:osabst).
 split;[exact H| ]. split;[apply map_join_emp| ]. split;assumption.
Qed.
Lemma OELocal : forall le x b tp v cs,
 get le x=Some(b,tp) -> OEState le(OEBytes b true tp v)cs |= LV x @ tp |->v.
Proof.
 intros le x b tp v cs E. unfold Alvarmapsto,Alvarenv'. exists b.
 eapply OEStar with(m1:=emp)(m2:=OEBytes b true tp v).
 - apply map_join_comm;apply map_join_emp.
 - exists b. split;[exact E| ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma OERSpatial : forall le cs, OEState le OEOuter cs |= OER.
Proof.
 intros le cs. unfold OER,OEOuter.
 eapply OEStar with(m1:=OECurrent)(m2:=OESentinel).
 - apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 402%positive);[subst b;right;left|left];
   unfold OECurrent,OESentinel,OEBytes;apply V293_encoded_memory_outside;left;congruence.
 - unfold CurTid. exists Tvoid. exists 402%positive.
   eapply OEStar with(m1:=emp)(m2:=OECurrent).
   + apply map_join_comm;apply map_join_emp.
   + exists 402%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply OEStar with(m1:=emp)(m2:=OESentinel).
   + apply map_join_comm;apply map_join_emp.
   + unfold LINV. apply astar_comm. apply astar_l_apure_intro.
     * split;reflexivity.
     * apply V293_witness_li_good.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma OERGood : GoodFrm OER.
Proof. cbn[OER CurTid LINV V293_witness_li GoodFrm];repeat split;exact I. Qed.
Lemma OERFun : GoodFunAsrt OER.
Proof.
 cbn[OER CurTid LINV V293_witness_li GoodFunAsrt Agvarmapsto Agvarenv' Aptrmapsto].
 repeat split;intros;repeat split;exact I.
Qed.
Lemma OERInv : OER ==> CurLINV V293_witness_li OETid.
Proof. intros s H. unfold CurLINV. exists(nil:list logicvar). unfold OER in H;clear -H;sep auto. Qed.
Definition OEFree := OEBytes 401%positive false(Tptr V293_tcb_type)Vnull.
Definition OEReserved : addrval := (405%positive,Int.zero).
Definition OECounter := OEBytes 404%positive true Tint8(V293_byteval 0).
Definition OEOwner := V293_encoded_memory 403%positive 44 false(encode_val(Tptr V293_tcb_type)(Vptr OEReserved)).
Definition OESlot slot := V293_encoded_memory 403%positive 44(V293_reservation_permission OEReserved slot)(encode_val(Tptr V293_tcb_type)slot).
Definition OECore := V293_tcb_empty_pool 401%positive(V293_create_owned_pool 403%positive OEReserved 11(Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0))).
Lemma OEBytesUnique : forall vl l permission m1 m2,
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
Lemma OEHeadPrecise : precise(Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull).
Proof.
 intros s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 destruct s as [[[[[[ge le] mem] ir] aux] oldO] op].
 change(mapstoval(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull M1 /\ O1=emp)in H1.
 change(mapstoval(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull M2 /\ O2=emp)in H2.
 destruct H1 as[[v1[E1 P1]]Oe1]. destruct H2 as[[v2[E2 P2]]Oe2].
 subst v1 v2. split;[eapply OEBytesUnique;eauto|congruence].
Qed.
Lemma OECounterPrecise : precise(Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0)).
Proof.
 intros s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 destruct s as [[[[[[ge le] mem] ir] aux] oldO] op].
 change(mapstoval(404%positive,0%Z)Tint8 true(V293_byteval 0)M1 /\ O1=emp)in H1.
 change(mapstoval(404%positive,0%Z)Tint8 true(V293_byteval 0)M2 /\ O2=emp)in H2.
 destruct H1 as[[v1[E1 P1]]Oe1]. destruct H2 as[[v2[E2 P2]]Oe2].
 subst v1 v2. split;[eapply V293_reservation_bytes_exact;eauto|congruence].
Qed.
Lemma OECorePrecise : precise OECore.
Proof.
 unfold OECore,V293_tcb_empty_pool,V293_create_owned_pool. apply precise_star;[apply OEHeadPrecise| ].
 apply precise_star;[apply V293_reservation_pool_precise|apply OECounterPrecise].
Qed.
Lemma OECoreGood : GoodInvAsrt OECore.
Proof. cbn[OECore V293_tcb_empty_pool V293_create_owned_pool V293_reservation_pool GoodInvAsrt];tauto. Qed.
Lemma OECoreISR : assertion.inv_isr_prop OECore.
Proof.
 unfold assertion.inv_isr_prop,OECore,V293_tcb_empty_pool,V293_create_owned_pool,V293_reservation_pool.
 repeat split;intros;destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];exact H.
Qed.
Definition OEInv : Inv := fun i=>match i with
 | O=>mkinvasrt OECoreGood(conj OECorePrecise OECoreISR)
 | S j=>V293_shared_inv(S j) end.
Lemma OENoisrTail : forall n i,starinv_noisr OEInv(S i)n <==> Aemp.
Proof.
 induction n;intros i s;cbn[starinv_noisr];[reflexivity| ].
 change(s |= Aemp ** starinv_noisr OEInv(S(S i))n <-> s |= Aemp).
 split;intro H.
 - apply astar_l_aemp_elim in H. apply IHn in H;exact H.
 - apply astar_l_aemp_intro. apply IHn;exact H.
Qed.
Lemma OENoisrCore : forall n,starinv_noisr OEInv 0 n <==> OECore.
Proof.
 intros[ |n]s;[reflexivity| ].
 change(s |= OECore ** starinv_noisr OEInv 1 n <-> s |= OECore).
 split;intro H.
 - apply astar_r_aemp_elim. eapply astar_mono;[intros st HS;exact HS|intros st HS;apply OENoisrTail in HS;exact HS|exact H].
 - eapply astar_mono;[intros st HS;exact HS|intros st HS;apply OENoisrTail;exact HS| ]. apply astar_r_aemp_intro;exact H.
Qed.
Theorem OEBorrowEquivalence : forall n,
 Aisr(fun _=>false) ** invlth_isr OEInv 0 n <==> Aisr(fun _=>false) ** OECore.
Proof.
 intros n s. destruct s as [[[[[[ge le] M] ir] aux] O] op]. split;intro H.
 all:(apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&H1&H2);
 destruct H1 as[E Empty];cbn in E;subst ir;
 apply sat_split';exists m1;exists m2;exists o1;exists o2;
 split;[exact JM| ];split;[exact JO| ];split;[split;[reflexivity|exact Empty]| ]).
 - unfold invlth_isr in H2. rewrite Nat.sub_0_r in H2.
   apply OENoisrCore with(n:=n). eapply invisr_imply_noisr';[ |exact H2]. reflexivity.
 - unfold invlth_isr. rewrite Nat.sub_0_r.
   apply V293_shared_clear_noisr_close;[reflexivity| ]. apply OENoisrCore;exact H2.
Qed.
Theorem OESharedLiteral : forall le cs slot,
 rule_type_val_match(Tptr V293_tcb_type)slot=true ->
 OEState le(merge OEFree(merge(OESlot slot)OECounter))cs |= invlth_isr OEInv 0 INUM.
Proof.
 intros le cs slot Typed. unfold invlth_isr. rewrite Nat.sub_0_r.
 apply V293_shared_clear_noisr_close;[reflexivity| ]. apply OENoisrCore.
 unfold OECore,V293_tcb_empty_pool,V293_create_owned_pool.
 eapply OEStar with(m1:=OEFree)(m2:=merge(OESlot slot)OECounter).
 - apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 401%positive);[subst b;right;left|left];
   unfold OEFree,OESlot,OECounter,OEBytes;
   repeat first[rewrite map_merge_semp by reflexivity|rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply OEStar with(m1:=OESlot slot)(m2:=OECounter).
   + apply map_join_merge;apply map_disjoint;intros[b off].
     destruct(Pos.eq_dec b 403%positive);[subst b;right;left|left];
     unfold OESlot,OECounter,OEBytes;apply V293_encoded_memory_outside;left;congruence.
   + exists slot. apply astar_l_apure_intro;[ |exact Typed].
     split;[apply V293_encoded_memory_mapsto|reflexivity].
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Theorem OESameInvariantFreeReservedOther : forall le cs,
 OEState le(merge OEFree(merge(OESlot Vnull)OECounter))cs |= invlth_isr OEInv 0 INUM /\
 OEState le(merge OEFree(merge(OESlot(Vptr OEReserved))OECounter))cs |= invlth_isr OEInv 0 INUM /\
 OEState le(merge OEFree(merge(OESlot(Vptr(701%positive,Int.zero)))OECounter))cs |= invlth_isr OEInv 0 INUM.
Proof. intros;repeat split;apply OESharedLiteral;reflexivity. Qed.

Theorem OEOwnedBorrowEquivalence : forall n,
 Aisr(fun _=>false) ** invlth_isr OEInv 0 n <==>
 Aisr(fun _=>false) ** V293_create_owned_pool 403%positive OEReserved 11
   (Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull **
    Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0)).
Proof.
 intros n s. split;intro H.
 - apply OEBorrowEquivalence in H. unfold OECore,V293_tcb_empty_pool,V293_create_owned_pool in *;clear -H;sep auto.
 - apply OEBorrowEquivalence. unfold OECore,V293_tcb_empty_pool,V293_create_owned_pool in *;clear -H;sep auto.
Qed.
Definition OEHookBefore cs := @mkfunasrt
 (V293_create_enabled_external OER(spec_done None)(fun _=>false)nil cs)
 (V293_create_enabled_external_good OER(spec_done None)(fun _=>false)nil cs OERFun).
Definition OEHookArgs := V293_create_stack_values 5 Vnull Vnull(Vint32(Int.repr 7)).
Definition OESpec cs : funspec := fun f=>if Z.eq_dec f 500%Z then
 Some(V293_tcb_enabled_fpre 401%positive OER(spec_done None)(fun _=>false)nil cs OERFun,
      V293_tcb_enabled_fpost 401%positive OER(spec_done None)(fun _=>false)nil cs OERFun,
      (Tint8,rev V293_TCBInit_argument_types))
 else if Z.eq_dec f 600%Z then
 Some(V293_create_stack_resource_fpre(OEHookBefore cs)OEHookArgs,
      V293_create_stack_resource_fpost(OEHookBefore cs)OEHookArgs Vnull,
      (Tptr Tint32,rev V293_stack_argument_types)) else None.
Definition OEProgram : progunit := fun f=>if Z.eq_dec f 500%Z then
 Some(V293_TCBInit_function 501%Z 502%Z)else None.
Definition OEArgs := rev(V293_tcb_success_arguments 11 Vnull Vnull
 (Vint32(Int.repr 4))(Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7))).
Definition OEPre cs := V293_tcb_internal_pre_cells(V293_byteval 11)Vnull Vnull
 (Vint32(Int.repr 4))(Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7)) **
 V293_tcb_enabled_external 401%positive OER(spec_done None)(fun _=>false)nil cs ** V293_tcb_internal_domain.
Definition OEPost cs result := V293_tcb_internal_post_cells **
 ([|result=Some(Vint32(Int.repr 66))|] **
 V293_tcb_enabled_external 401%positive OER(spec_done None)(fun _=>false)nil cs) ** V293_tcb_internal_domain.
Lemma OEBuilders : forall cs,
 Some(OEPre cs)=BuildPreI OEProgram 500%Z OEArgs nil
 (V293_tcb_enabled_fpre 401%positive OER(spec_done None)(fun _=>false)nil cs OERFun)OETid /\
 Some(OEPost cs)=BuildRetI OEProgram 500%Z OEArgs nil
 (V293_tcb_enabled_fpost 401%positive OER(spec_done None)(fun _=>false)nil cs OERFun)OETid.
Proof. intros;split;reflexivity. Qed.
Theorem OECalleeCheckedSameSpec : forall sd cs,
 InfRules(OESpec cs)sd V293_witness_li OEInv(OEPost cs)Afalse
 (OEPre cs)(V293_TCBInit_function_body 501%Z 502%Z)Afalse OETid.
Proof.
 intros sd cs. eapply V293_OS_TCBInit_empty_enabled_contract
 with(P:=OEProgram)(f:=500%Z)(K:=V293_create_owned_pool 403%positive OEReserved 11(Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0)))
 (good:=OERFun)(vl:=OEArgs)(lg:=nil)(bf:=401%positive)(R:=OER)
 (aop:=spec_done None)(isr:=fun _=>false)(is:=nil)(cs:=cs).
 - vm_compute;lia.
 - apply OERGood.
 - apply OERInv.
 - intros s H;apply OEBorrowEquivalence in H;exact H.
 - intros s H;apply OEBorrowEquivalence;exact H.
 - reflexivity.
 - apply(proj1(OEBuilders cs)).
 - apply(proj2(OEBuilders cs)).
Qed.

Definition OEEntry cs := V293_create_slot_state 201%positive 214%positive
 403%positive 404%positive 405%positive 11 0 None(Vint32 Int.zero)
 (Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull)
 (LV 108%Z @ (Tptr Tint32) |->Vnull **
  V293_create_stack_arguments 5 Vnull Vnull(Vint32(Int.repr 7))
   (OER ** V293_create_owned_empty_aux 401%positive Vnull(Vint32(Int.repr 4))
    (Vint32(Int.repr 5))Vnull Vundef Aemp))
 (spec_done None)(fun _=>false)nil cs.
Definition OEReturn cs := V293_create_enabled_failure_return 403%positive 11
 (V293_create_enabled_failure_kept 401%positive Vnull Vnull(Vint32(Int.repr 4))
  (Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7))OER
  (V293_create_owned_empty_kept 404%positive 405%positive(Vint32 Int.zero)5 Vnull Vnull Aemp))
 (spec_done None)(fun _=>false)nil cs.
Theorem OEConnectedTailCheckedSameSpec : forall sd cs,
 InfRules(OESpec cs)sd V293_witness_li OEInv(OEReturn cs)Afalse(OEEntry cs)
 (V293_create_owned_empty_tail 600%Z 500%Z 98%Z 601%Z)Afalse OETid.
Proof.
 intros sd cs. unfold OEEntry,OEReturn.
 eapply V293_OSTaskCreateExt_owned_empty_critical_tail with(BeforeGood:=OERFun)(AfterGood:=OERFun).
 - lia.
 - vm_compute;lia.
 - exact I.
 - apply OERGood.
 - apply OERGood.
 - vm_compute;auto.
 - unfold V293_tcb_init_values_valid. vm_compute;repeat split;reflexivity.
 - apply OERInv.
 - apply OERInv.
 - intros s H. apply OEBorrowEquivalence in H.
   unfold OECore,V293_tcb_empty_pool,V293_create_owned_pool in *;clear -H;sep auto.
 - intros s H. apply OEBorrowEquivalence.
   unfold OECore,V293_tcb_empty_pool,V293_create_owned_pool in *;clear -H;sep auto.
 - reflexivity.
 - reflexivity.
Qed.

Definition OEEntryPrio := V293_encoded_memory 201%positive 0%Z true(encode_val(Tint8)(V293_byteval 11)).
Definition OEEntryCPU := V293_encoded_memory 214%positive 0%Z true(encode_val(Tint32)(Vint32 Int.zero)).
Definition OEEntryLocal108 := V293_encoded_memory 208%positive 0%Z true(encode_val(Tptr Tint32)(Vnull)).
Definition OEEntryLocal205 := V293_encoded_memory 205%positive 0%Z true(encode_val(Tptr Tint32)(Vnull)).
Definition OEEntryLocal206 := V293_encoded_memory 206%positive 0%Z true(encode_val(Tint16)(Vint32(Int.repr 4))).
Definition OEEntryLocal207 := V293_encoded_memory 207%positive 0%Z true(encode_val(Tint32)(Vint32(Int.repr 5))).
Definition OEEntryLocal208 := V293_encoded_memory 210%positive 0%Z true(encode_val(Tptr Tvoid)(Vnull)).
Definition OEEntryLocal204 := V293_encoded_memory 204%positive 0%Z true(encode_val(Tint16)(Vint32(Int.repr 7))).
Definition OEEntryLocal209 := V293_encoded_memory 209%positive 0%Z true(encode_val(Tint8)(Vundef)).
Definition OEEntryLocal201 := V293_encoded_memory 211%positive 0%Z true(encode_val(Tint32)(V293_task_selector 5)).
Definition OEEntryLocal202 := V293_encoded_memory 212%positive 0%Z true(encode_val(Tptr Tvoid)(Vnull)).
Definition OEEntryLocal203 := V293_encoded_memory 213%positive 0%Z true(encode_val(Tptr Tint32)(Vnull)).
Definition OEEntrySlot := V293_encoded_memory 403%positive 44%Z true(encode_val(Tptr V293_tcb_type)(Vnull)).
Definition OEEntryNest := V293_encoded_memory 404%positive 0%Z true(encode_val(Tint8)(V293_byteval 0)).
Definition OEEntryHead := V293_encoded_memory 401%positive 0%Z false(encode_val(Tptr V293_tcb_type)(Vnull)).
Definition OEEntryMemory := merge OEEntryPrio (merge OEEntryCPU (merge OEEntryLocal108 (merge OEEntryLocal205 (merge OEEntryLocal206 (merge OEEntryLocal207 (merge OEEntryLocal208 (merge OEEntryLocal204 (merge OEEntryLocal209 (merge OEEntryLocal201 (merge OEEntryLocal202 (merge OEEntryLocal203 (merge OEEntrySlot (merge OEEntryNest (merge OEEntryHead (OEOuter))))))))))))))).
Lemma OEMergeAbsent : forall(m1 m2:mem)a,
 get m1 a=None -> get m2 a=None -> get(merge m1 m2)a=None.
Proof. intros. rewrite map_merge_semp by reflexivity. rewrite H,H0. reflexivity. Qed.
Lemma OEEntryBytes : OEState OELE OEEntryMemory (true::nil) |=
 Amapsto(201%positive,0%Z)Tint8 true(V293_byteval 11) **
 (Amapsto(214%positive,0%Z)Tint32 true(Vint32 Int.zero) **
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
 (Amapsto(403%positive,44%Z)(Tptr V293_tcb_type)true Vnull **
 (Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0) **
 (Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull **
 (OER))))))))))))))).
Proof.
 unfold OEEntryMemory.
 eapply OEStar with(m1:=OEEntryPrio).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 201%positive);[subst other;right;left|left];
   unfold OEEntryPrio,OEEntryCPU,OEEntryLocal108,OEEntryLocal205,OEEntryLocal206,OEEntryLocal207,OEEntryLocal208,OEEntryLocal204,OEEntryLocal209,OEEntryLocal201,OEEntryLocal202,OEEntryLocal203,OEEntrySlot,OEEntryNest,OEEntryHead,OEOuter,OECurrent,OESentinel,OEBytes;
   repeat apply OEMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply OEStar with(m1:=OEEntryCPU).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 214%positive);[subst other;right;left|left];
   unfold OEEntryPrio,OEEntryCPU,OEEntryLocal108,OEEntryLocal205,OEEntryLocal206,OEEntryLocal207,OEEntryLocal208,OEEntryLocal204,OEEntryLocal209,OEEntryLocal201,OEEntryLocal202,OEEntryLocal203,OEEntrySlot,OEEntryNest,OEEntryHead,OEOuter,OECurrent,OESentinel,OEBytes;
   repeat apply OEMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply OEStar with(m1:=OEEntryLocal108).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 208%positive);[subst other;right;left|left];
   unfold OEEntryPrio,OEEntryCPU,OEEntryLocal108,OEEntryLocal205,OEEntryLocal206,OEEntryLocal207,OEEntryLocal208,OEEntryLocal204,OEEntryLocal209,OEEntryLocal201,OEEntryLocal202,OEEntryLocal203,OEEntrySlot,OEEntryNest,OEEntryHead,OEOuter,OECurrent,OESentinel,OEBytes;
   repeat apply OEMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply OELocal. vm_compute;reflexivity. }
 eapply OEStar with(m1:=OEEntryLocal205).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 205%positive);[subst other;right;left|left];
   unfold OEEntryPrio,OEEntryCPU,OEEntryLocal108,OEEntryLocal205,OEEntryLocal206,OEEntryLocal207,OEEntryLocal208,OEEntryLocal204,OEEntryLocal209,OEEntryLocal201,OEEntryLocal202,OEEntryLocal203,OEEntrySlot,OEEntryNest,OEEntryHead,OEOuter,OECurrent,OESentinel,OEBytes;
   repeat apply OEMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply OELocal. vm_compute;reflexivity. }
 eapply OEStar with(m1:=OEEntryLocal206).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 206%positive);[subst other;right;left|left];
   unfold OEEntryPrio,OEEntryCPU,OEEntryLocal108,OEEntryLocal205,OEEntryLocal206,OEEntryLocal207,OEEntryLocal208,OEEntryLocal204,OEEntryLocal209,OEEntryLocal201,OEEntryLocal202,OEEntryLocal203,OEEntrySlot,OEEntryNest,OEEntryHead,OEOuter,OECurrent,OESentinel,OEBytes;
   repeat apply OEMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply OELocal. vm_compute;reflexivity. }
 eapply OEStar with(m1:=OEEntryLocal207).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 207%positive);[subst other;right;left|left];
   unfold OEEntryPrio,OEEntryCPU,OEEntryLocal108,OEEntryLocal205,OEEntryLocal206,OEEntryLocal207,OEEntryLocal208,OEEntryLocal204,OEEntryLocal209,OEEntryLocal201,OEEntryLocal202,OEEntryLocal203,OEEntrySlot,OEEntryNest,OEEntryHead,OEOuter,OECurrent,OESentinel,OEBytes;
   repeat apply OEMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply OELocal. vm_compute;reflexivity. }
 eapply OEStar with(m1:=OEEntryLocal208).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 210%positive);[subst other;right;left|left];
   unfold OEEntryPrio,OEEntryCPU,OEEntryLocal108,OEEntryLocal205,OEEntryLocal206,OEEntryLocal207,OEEntryLocal208,OEEntryLocal204,OEEntryLocal209,OEEntryLocal201,OEEntryLocal202,OEEntryLocal203,OEEntrySlot,OEEntryNest,OEEntryHead,OEOuter,OECurrent,OESentinel,OEBytes;
   repeat apply OEMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply OELocal. vm_compute;reflexivity. }
 eapply OEStar with(m1:=OEEntryLocal204).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 204%positive);[subst other;right;left|left];
   unfold OEEntryPrio,OEEntryCPU,OEEntryLocal108,OEEntryLocal205,OEEntryLocal206,OEEntryLocal207,OEEntryLocal208,OEEntryLocal204,OEEntryLocal209,OEEntryLocal201,OEEntryLocal202,OEEntryLocal203,OEEntrySlot,OEEntryNest,OEEntryHead,OEOuter,OECurrent,OESentinel,OEBytes;
   repeat apply OEMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply OELocal. vm_compute;reflexivity. }
 eapply OEStar with(m1:=OEEntryLocal209).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 209%positive);[subst other;right;left|left];
   unfold OEEntryPrio,OEEntryCPU,OEEntryLocal108,OEEntryLocal205,OEEntryLocal206,OEEntryLocal207,OEEntryLocal208,OEEntryLocal204,OEEntryLocal209,OEEntryLocal201,OEEntryLocal202,OEEntryLocal203,OEEntrySlot,OEEntryNest,OEEntryHead,OEOuter,OECurrent,OESentinel,OEBytes;
   repeat apply OEMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply OELocal. vm_compute;reflexivity. }
 eapply OEStar with(m1:=OEEntryLocal201).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 211%positive);[subst other;right;left|left];
   unfold OEEntryPrio,OEEntryCPU,OEEntryLocal108,OEEntryLocal205,OEEntryLocal206,OEEntryLocal207,OEEntryLocal208,OEEntryLocal204,OEEntryLocal209,OEEntryLocal201,OEEntryLocal202,OEEntryLocal203,OEEntrySlot,OEEntryNest,OEEntryHead,OEOuter,OECurrent,OESentinel,OEBytes;
   repeat apply OEMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply OELocal. vm_compute;reflexivity. }
 eapply OEStar with(m1:=OEEntryLocal202).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 212%positive);[subst other;right;left|left];
   unfold OEEntryPrio,OEEntryCPU,OEEntryLocal108,OEEntryLocal205,OEEntryLocal206,OEEntryLocal207,OEEntryLocal208,OEEntryLocal204,OEEntryLocal209,OEEntryLocal201,OEEntryLocal202,OEEntryLocal203,OEEntrySlot,OEEntryNest,OEEntryHead,OEOuter,OECurrent,OESentinel,OEBytes;
   repeat apply OEMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply OELocal. vm_compute;reflexivity. }
 eapply OEStar with(m1:=OEEntryLocal203).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 213%positive);[subst other;right;left|left];
   unfold OEEntryPrio,OEEntryCPU,OEEntryLocal108,OEEntryLocal205,OEEntryLocal206,OEEntryLocal207,OEEntryLocal208,OEEntryLocal204,OEEntryLocal209,OEEntryLocal201,OEEntryLocal202,OEEntryLocal203,OEEntrySlot,OEEntryNest,OEEntryHead,OEOuter,OECurrent,OESentinel,OEBytes;
   repeat apply OEMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { apply OELocal. vm_compute;reflexivity. }
 eapply OEStar with(m1:=OEEntrySlot).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 403%positive);[subst other;right;left|left];
   unfold OEEntryPrio,OEEntryCPU,OEEntryLocal108,OEEntryLocal205,OEEntryLocal206,OEEntryLocal207,OEEntryLocal208,OEEntryLocal204,OEEntryLocal209,OEEntryLocal201,OEEntryLocal202,OEEntryLocal203,OEEntrySlot,OEEntryNest,OEEntryHead,OEOuter,OECurrent,OESentinel,OEBytes;
   repeat apply OEMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply OEStar with(m1:=OEEntryNest).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 404%positive);[subst other;right;left|left];
   unfold OEEntryPrio,OEEntryCPU,OEEntryLocal108,OEEntryLocal205,OEEntryLocal206,OEEntryLocal207,OEEntryLocal208,OEEntryLocal204,OEEntryLocal209,OEEntryLocal201,OEEntryLocal202,OEEntryLocal203,OEEntrySlot,OEEntryNest,OEEntryHead,OEOuter,OECurrent,OESentinel,OEBytes;
   repeat apply OEMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply OEStar with(m1:=OEEntryHead).
 { apply map_join_merge;apply map_disjoint;intros[other offset].
   destruct(Pos.eq_dec other 401%positive);[subst other;right;left|left];
   unfold OEEntryPrio,OEEntryCPU,OEEntryLocal108,OEEntryLocal205,OEEntryLocal206,OEEntryLocal207,OEEntryLocal208,OEEntryLocal204,OEEntryLocal209,OEEntryLocal201,OEEntryLocal202,OEEntryLocal203,OEEntrySlot,OEEntryNest,OEEntryHead,OEOuter,OECurrent,OESentinel,OEBytes;
   repeat apply OEMergeAbsent;first[apply V293_encoded_memory_outside;left;congruence|apply map_get_sig';congruence|apply map_emp_get]. }
 { split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 apply OERSpatial.
Qed.
Lemma OEEntryViews : OEState OELE emp(true::nil) |=
 OS[(fun _=>false),false,nil,true::nil] **
 (<||spec_done None||> **
 (Alvarenv 101%Z Tint8(201%positive,0%Z) **
 (Alvarenv 109%Z Tint32(214%positive,0%Z) **
 (V293_create_global_binding 99%Z Tint8 404%positive **
 (V293_create_global_binding 92%Z(Tarray(Tptr V293_tcb_type)13)403%positive **
 (V293_create_global_binding 97%Z Tint8 405%positive **
 (Agvarenv 91%Z(Tptr V293_tcb_type)(401%positive,0%Z) **
 (Aemp)))))))).
Proof.
 eapply OEStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 { assert(E:OEState OELE emp(true::nil) |= Aemp)by(split;reflexivity).
   assert(S:OEState OELE emp(true::nil) |=
    Aisr(fun _=>false) ** Aie false ** Ais nil ** Acs(true::nil) ** Aemp).
   { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
     apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[exact E|reflexivity]. }
   clear -S;sep auto. }
 eapply OEStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 { apply astar_r_aemp_elim. apply astar_l_aop'_intro;[split;reflexivity|reflexivity]. }
 eapply OEStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 { exists 201%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity. }
 eapply OEStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 { exists 214%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity. }
 eapply OEStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 { split.
   - exists 404%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   - split;[ |split;reflexivity]. intros[v H]. vm_compute in H;discriminate. }
 eapply OEStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 { split.
   - exists 403%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   - split;[ |split;reflexivity]. intros[v H]. vm_compute in H;discriminate. }
 eapply OEStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 { split.
   - exists 405%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   - split;[ |split;reflexivity]. intros[v H]. vm_compute in H;discriminate. }
 eapply OEStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 { exists 401%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity. }
 split;reflexivity.
Qed.
Theorem OEEntryLiteral : OEState OELE OEEntryMemory(true::nil) |= OEEntry nil.
Proof.
 assert(B:=OEEntryBytes). assert(G:=OEEntryViews).
 assert(J:join(emp:mem)OEEntryMemory OEEntryMemory)by(apply map_join_comm;apply map_join_emp).
 pose proof(OEStar OELE emp OEEntryMemory OEEntryMemory(true::nil) _ _ J G B)as H.
 unfold OEEntry,V293_create_slot_state,V293_create_slot_views,
  V293_create_stack_arguments,V293_create_owned_empty_aux.
 cbn[V293_rdy_raw_cells V293_create_slot_cells V293_create_slot_value app].
 clear -H;sep auto.
Qed.

(* A bounded physical-store control, not an execution proof of a modified API. *)
Definition OERollbackInput := V293_encoded_memory 403%positive 44 true
 (encode_val(Tptr V293_tcb_type)(Vptr OEReserved)).
Theorem OERollbackInputReadsReserved :
 load(Tptr V293_tcb_type)OERollbackInput(403%positive,44%Z)=Some(Vptr OEReserved).
Proof. eapply mapstoval_load;[reflexivity|apply V293_encoded_memory_mapsto]. Qed.
Theorem OERollbackStoreWritesNull : exists M,
 store(Tptr V293_tcb_type)OERollbackInput(403%positive,44%Z)Vnull=Some M /\
 load(Tptr V293_tcb_type)M(403%positive,44%Z)=Some Vnull.
Proof.
 assert(H:mapstoval(403%positive,44%Z)(Tptr V293_tcb_type)true(Vptr OEReserved)OERollbackInput)
 by apply V293_encoded_memory_mapsto.
 assert(J:join OERollbackInput(emp:mem)OERollbackInput)by apply map_join_emp.
 destruct(store_exist_join' _ _ _ Vnull _ _ _ H J)as[M S].
 destruct(store_mapstoval_frame1 _ _ _ _ _ _ _ _ H J S)as[M1[P[S1 J1]]].
 exists M1. split;[exact S1|eapply mapstoval_load;[reflexivity|exact P]].
Qed.
Theorem OERollbackStoreRemovedKeepsReserved :
 load(Tptr V293_tcb_type)OERollbackInput(403%positive,44%Z)<>Some Vnull.
Proof. rewrite OERollbackInputReadsReserved. discriminate. Qed.
