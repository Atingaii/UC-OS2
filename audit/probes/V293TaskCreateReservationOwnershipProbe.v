(* Independent literal caller/shared partition. The same finite Spec and Inv
   check the actual call/suffix and the full callee, without execution oracles.
   This is not a production reservation invariant or a WFIFun proof. *)
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
Require Import Coq.Lists.List Lia.
Import ListNotations.
Definition ROBaseGE : env := set (set (sig 91%Z (401%positive,Tptr V293_tcb_type))
 OSTCBCur (402%positive,Tptr Tvoid)) 92%Z (403%positive,Tarray(Tptr V293_tcb_type)13).
Definition ROGE : env := set(set ROBaseGE 99%Z(404%positive,Tint8))97%Z(405%positive,Tint8).
Definition ROLE : env := set (set (set (set (set (set (set (sig 101%Z (201%positive,Tint8)) 108%Z (208%positive,Tptr Tint32)) 205%Z (205%positive,Tptr Tint32)) 206%Z (206%positive,Tint16)) 207%Z (207%positive,Tint32)) 208%Z (210%positive,Tptr Tvoid)) 204%Z (204%positive,Tint16)) 209%Z (209%positive,Tint8).
Definition ROTid : tid := (301%positive,Int.repr 8).
Definition ROBytes b permission tp v := V293_encoded_memory b 0 permission(encode_val tp v).
Definition ROState le M cs : RstateOP :=
 (ROGE,le,M,(fun _=>false),(true,nil,cs),(emp:osabst),spec_done None).
Definition ROCurrent := ROBytes 402%positive false(Tptr Tvoid)(Vptr ROTid).
Definition ROSentinel := ROBytes 601%positive true Tint8(Vint32(Int.repr 77)).
Definition ROOuter := merge ROCurrent ROSentinel.
Definition ROR := CurTid ROTid ** LINV V293_witness_li ROTid nil **
 Amapsto(601%positive,0%Z)Tint8 true(Vint32(Int.repr 77)).
Lemma ROStar : forall le m1 m2 m cs p q,
 join m1 m2 m -> ROState le m1 cs |= p -> ROState le m2 cs |= q -> ROState le m cs |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2. exists(emp:osabst). exists(emp:osabst).
 split;[exact H| ]. split;[apply map_join_emp| ]. split;assumption.
Qed.
Lemma ROLocal : forall le x b tp v cs,
 get le x=Some(b,tp) -> ROState le(ROBytes b true tp v)cs |= LV x @ tp |->v.
Proof.
 intros le x b tp v cs E. unfold Alvarmapsto,Alvarenv'. exists b.
 eapply ROStar with(m1:=emp)(m2:=ROBytes b true tp v).
 - apply map_join_comm;apply map_join_emp.
 - exists b. split;[exact E| ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma RORSpatial : forall le cs, ROState le ROOuter cs |= ROR.
Proof.
 intros le cs. unfold ROR,ROOuter.
 eapply ROStar with(m1:=ROCurrent)(m2:=ROSentinel).
 - apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 402%positive);[subst b;right;left|left];
   unfold ROCurrent,ROSentinel,ROBytes;apply V293_encoded_memory_outside;left;congruence.
 - unfold CurTid. exists Tvoid. exists 402%positive.
   eapply ROStar with(m1:=emp)(m2:=ROCurrent).
   + apply map_join_comm;apply map_join_emp.
   + exists 402%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply ROStar with(m1:=emp)(m2:=ROSentinel).
   + apply map_join_comm;apply map_join_emp.
   + unfold LINV. apply astar_comm. apply astar_l_apure_intro.
     * split;reflexivity.
     * apply V293_witness_li_good.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma RORGood : GoodFrm ROR.
Proof. cbn[ROR CurTid LINV V293_witness_li GoodFrm];repeat split;exact I. Qed.
Lemma RORFun : GoodFunAsrt ROR.
Proof.
 cbn[ROR CurTid LINV V293_witness_li GoodFunAsrt Agvarmapsto Agvarenv' Aptrmapsto].
 repeat split;intros;repeat split;exact I.
Qed.
Lemma RORInv : ROR ==> CurLINV V293_witness_li ROTid.
Proof. intros s H. unfold CurLINV. exists(nil:list logicvar). unfold ROR in H;clear -H;sep auto. Qed.
Definition ROFree := ROBytes 401%positive false(Tptr V293_tcb_type)Vnull.
Definition ROReserved : addrval := (405%positive,Int.zero).
Definition ROCounter := ROBytes 404%positive true Tint8(V293_byteval 0).
Definition ROOwner := V293_encoded_memory 403%positive 44 false(encode_val(Tptr V293_tcb_type)(Vptr ROReserved)).
Definition ROSlot slot := V293_encoded_memory 403%positive 44(V293_reservation_permission ROReserved slot)(encode_val(Tptr V293_tcb_type)slot).
Definition ROCore := V293_tcb_empty_pool 401%positive(V293_create_owned_pool 403%positive ROReserved 11(Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0))).
Lemma ROBytesUnique : forall vl l permission m1 m2,
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
Lemma ROHeadPrecise : precise(Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull).
Proof.
 intros s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 destruct s as [[[[[[ge le] mem] ir] aux] oldO] op].
 change(mapstoval(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull M1 /\ O1=emp)in H1.
 change(mapstoval(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull M2 /\ O2=emp)in H2.
 destruct H1 as[[v1[E1 P1]]Oe1]. destruct H2 as[[v2[E2 P2]]Oe2].
 subst v1 v2. split;[eapply ROBytesUnique;eauto|congruence].
Qed.
Lemma ROCounterPrecise : precise(Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0)).
Proof.
 intros s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 destruct s as [[[[[[ge le] mem] ir] aux] oldO] op].
 change(mapstoval(404%positive,0%Z)Tint8 true(V293_byteval 0)M1 /\ O1=emp)in H1.
 change(mapstoval(404%positive,0%Z)Tint8 true(V293_byteval 0)M2 /\ O2=emp)in H2.
 destruct H1 as[[v1[E1 P1]]Oe1]. destruct H2 as[[v2[E2 P2]]Oe2].
 subst v1 v2. split;[eapply V293_reservation_bytes_exact;eauto|congruence].
Qed.
Lemma ROCorePrecise : precise ROCore.
Proof.
 unfold ROCore,V293_tcb_empty_pool,V293_create_owned_pool. apply precise_star;[apply ROHeadPrecise| ].
 apply precise_star;[apply V293_reservation_pool_precise|apply ROCounterPrecise].
Qed.
Lemma ROCoreGood : GoodInvAsrt ROCore.
Proof. cbn[ROCore V293_tcb_empty_pool V293_create_owned_pool V293_reservation_pool GoodInvAsrt];tauto. Qed.
Lemma ROCoreISR : assertion.inv_isr_prop ROCore.
Proof.
 unfold assertion.inv_isr_prop,ROCore,V293_tcb_empty_pool,V293_create_owned_pool,V293_reservation_pool.
 repeat split;intros;destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];exact H.
Qed.
Definition ROInv : Inv := fun i=>match i with
 | O=>mkinvasrt ROCoreGood(conj ROCorePrecise ROCoreISR)
 | S j=>V293_shared_inv(S j) end.
Lemma RONoisrTail : forall n i,starinv_noisr ROInv(S i)n <==> Aemp.
Proof.
 induction n;intros i s;cbn[starinv_noisr];[reflexivity| ].
 change(s |= Aemp ** starinv_noisr ROInv(S(S i))n <-> s |= Aemp).
 split;intro H.
 - apply astar_l_aemp_elim in H. apply IHn in H;exact H.
 - apply astar_l_aemp_intro. apply IHn;exact H.
Qed.
Lemma RONoisrCore : forall n,starinv_noisr ROInv 0 n <==> ROCore.
Proof.
 intros[ |n]s;[reflexivity| ].
 change(s |= ROCore ** starinv_noisr ROInv 1 n <-> s |= ROCore).
 split;intro H.
 - apply astar_r_aemp_elim. eapply astar_mono;[intros st HS;exact HS|intros st HS;apply RONoisrTail in HS;exact HS|exact H].
 - eapply astar_mono;[intros st HS;exact HS|intros st HS;apply RONoisrTail;exact HS| ]. apply astar_r_aemp_intro;exact H.
Qed.
Theorem ROBorrowEquivalence : forall n,
 Aisr(fun _=>false) ** invlth_isr ROInv 0 n <==> Aisr(fun _=>false) ** ROCore.
Proof.
 intros n s. destruct s as [[[[[[ge le] M] ir] aux] O] op]. split;intro H.
 all:(apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&H1&H2);
 destruct H1 as[E Empty];cbn in E;subst ir;
 apply sat_split';exists m1;exists m2;exists o1;exists o2;
 split;[exact JM| ];split;[exact JO| ];split;[split;[reflexivity|exact Empty]| ]).
 - unfold invlth_isr in H2. rewrite Nat.sub_0_r in H2.
   apply RONoisrCore with(n:=n). eapply invisr_imply_noisr';[ |exact H2]. reflexivity.
 - unfold invlth_isr. rewrite Nat.sub_0_r.
   apply V293_shared_clear_noisr_close;[reflexivity| ]. apply RONoisrCore;exact H2.
Qed.
Theorem ROSharedLiteral : forall le cs slot,
 rule_type_val_match(Tptr V293_tcb_type)slot=true ->
 ROState le(merge ROFree(merge(ROSlot slot)ROCounter))cs |= invlth_isr ROInv 0 INUM.
Proof.
 intros le cs slot Typed. unfold invlth_isr. rewrite Nat.sub_0_r.
 apply V293_shared_clear_noisr_close;[reflexivity| ]. apply RONoisrCore.
 unfold ROCore,V293_tcb_empty_pool,V293_create_owned_pool.
 eapply ROStar with(m1:=ROFree)(m2:=merge(ROSlot slot)ROCounter).
 - apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 401%positive);[subst b;right;left|left];
   unfold ROFree,ROSlot,ROCounter,ROBytes;
   repeat first[rewrite map_merge_semp by reflexivity|rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply ROStar with(m1:=ROSlot slot)(m2:=ROCounter).
   + apply map_join_merge;apply map_disjoint;intros[b off].
     destruct(Pos.eq_dec b 403%positive);[subst b;right;left|left];
     unfold ROSlot,ROCounter,ROBytes;apply V293_encoded_memory_outside;left;congruence.
   + exists slot. apply astar_l_apure_intro;[ |exact Typed].
     split;[apply V293_encoded_memory_mapsto|reflexivity].
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Theorem ROSameInvariantFreeReservedOther : forall le cs,
 ROState le(merge ROFree(merge(ROSlot Vnull)ROCounter))cs |= invlth_isr ROInv 0 INUM /\
 ROState le(merge ROFree(merge(ROSlot(Vptr ROReserved))ROCounter))cs |= invlth_isr ROInv 0 INUM /\
 ROState le(merge ROFree(merge(ROSlot(Vptr(701%positive,Int.zero)))ROCounter))cs |= invlth_isr ROInv 0 INUM.
Proof. intros;repeat split;apply ROSharedLiteral;reflexivity. Qed.
Definition ROLocal101 := ROBytes 201%positive true(Tint8)(V293_byteval 11).
Definition ROLocal108 := ROBytes 208%positive true(Tptr Tint32)(Vnull).
Definition ROLocal205 := ROBytes 205%positive true(Tptr Tint32)(Vnull).
Definition ROLocal206 := ROBytes 206%positive true(Tint16)(Vint32(Int.repr 4)).
Definition ROLocal207 := ROBytes 207%positive true(Tint32)(Vint32(Int.repr 5)).
Definition ROLocal208 := ROBytes 210%positive true(Tptr Tvoid)(Vnull).
Definition ROLocal204 := ROBytes 204%positive true(Tint16)(Vint32(Int.repr 7)).
Definition ROLocal209 := ROBytes 209%positive true(Tint8)(Vundef).
Definition ROLocals := merge ROLocal101 (merge ROLocal108 (merge ROLocal205 (merge ROLocal206 (merge ROLocal207 (merge ROLocal208 (merge ROLocal204 (merge ROLocal209 ((emp:mem))))))))).
Definition ROCaller := merge ROLocals ROOuter.
Definition ROFrame := V293_tcb_table_binding 403%positive ** Aemp.
Definition ROInput cs := V293_tcb_enabled_external 401%positive ROR(spec_done None)(fun _=>false)nil cs **
 LV 209%Z @ Tint8 |->Vundef **
 V293_create_tcb_arguments 11 Vnull Vnull(Vint32(Int.repr 4))(Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7))ROFrame.
Lemma ROGlobals : ROState ROLE emp nil |= Agvarenv 91%Z(Tptr V293_tcb_type)(401%positive,0%Z) ** ROFrame.
Proof.
 unfold ROFrame. eapply ROStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 - exists 401%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - apply astar_r_aemp_intro. split.
   + exists 403%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[ |split;reflexivity]. intros[v H]. vm_compute in H;discriminate.
Qed.
Ltac ROLocalsApart b :=
 apply map_join_merge;apply map_disjoint;intros[other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold ROLocals,ROLocal101,ROLocal108,ROLocal205,ROLocal206,ROLocal207,ROLocal208,ROLocal204,ROLocal209,ROBytes;
 repeat first[rewrite map_merge_semp by reflexivity|rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Lemma ROLocalsSpatial : forall cs, ROState ROLE ROLocals cs |=
LV 101%Z @ (Tint8) |->(V293_byteval 11) **
 LV 108%Z @ (Tptr Tint32) |->(Vnull) **
 LV 205%Z @ (Tptr Tint32) |->(Vnull) **
 LV 206%Z @ (Tint16) |->(Vint32(Int.repr 4)) **
 LV 207%Z @ (Tint32) |->(Vint32(Int.repr 5)) **
 LV 208%Z @ (Tptr Tvoid) |->(Vnull) **
 LV 204%Z @ (Tint16) |->(Vint32(Int.repr 7)) **
 LV 209%Z @ (Tint8) |->(Vundef) **
 Aemp.
Proof.
 intro cs. unfold ROLocals.
 eapply ROStar with(m1:=ROLocal101).
 { ROLocalsApart 201%positive. }
 { apply ROLocal. vm_compute;reflexivity. }
 eapply ROStar with(m1:=ROLocal108).
 { ROLocalsApart 208%positive. }
 { apply ROLocal. vm_compute;reflexivity. }
 eapply ROStar with(m1:=ROLocal205).
 { ROLocalsApart 205%positive. }
 { apply ROLocal. vm_compute;reflexivity. }
 eapply ROStar with(m1:=ROLocal206).
 { ROLocalsApart 206%positive. }
 { apply ROLocal. vm_compute;reflexivity. }
 eapply ROStar with(m1:=ROLocal207).
 { ROLocalsApart 207%positive. }
 { apply ROLocal. vm_compute;reflexivity. }
 eapply ROStar with(m1:=ROLocal208).
 { ROLocalsApart 210%positive. }
 { apply ROLocal. vm_compute;reflexivity. }
 eapply ROStar with(m1:=ROLocal204).
 { ROLocalsApart 204%positive. }
 { apply ROLocal. vm_compute;reflexivity. }
 eapply ROStar with(m1:=ROLocal209).
 { ROLocalsApart 209%positive. }
 { apply ROLocal. vm_compute;reflexivity. }
 split;reflexivity.
Qed.
Theorem ROCallerLiteral : ROState ROLE ROCaller nil |= ROInput nil.
Proof.
 unfold ROCaller. assert(L:=ROLocalsSpatial nil). assert(R:=RORSpatial ROLE nil).
 assert(G:=ROGlobals).
 assert(J:join ROLocals ROOuter(merge ROLocals ROOuter)).
 { apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 402%positive)as[E|E];[subst b;left| ].
   - unfold ROLocals,ROLocal101,ROLocal108,ROLocal205,ROLocal206,ROLocal207,ROLocal208,ROLocal204,ROLocal209,ROBytes;
     repeat first[rewrite map_merge_semp by reflexivity|rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
   - destruct(Pos.eq_dec b 601%positive)as[F|F];[subst b;left|right;left].
     + unfold ROLocals,ROLocal101,ROLocal108,ROLocal205,ROLocal206,ROLocal207,ROLocal208,ROLocal204,ROLocal209,ROBytes;
       repeat first[rewrite map_merge_semp by reflexivity|rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
     + unfold ROOuter,ROCurrent,ROSentinel,ROBytes.
       repeat first[rewrite map_merge_semp by reflexivity|rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity. }
 pose proof(ROStar _ _ _ _ _ _ _ J L R)as H.
 assert(B:ROState ROLE(merge ROLocals ROOuter)nil |=
  (Agvarenv 91%Z(Tptr V293_tcb_type)(401%positive,0%Z) ** ROFrame) **
  (LV 101%Z @ Tint8 |->V293_byteval 11 **
   LV 108%Z @ (Tptr Tint32) |->Vnull ** LV 205%Z @ (Tptr Tint32) |->Vnull **
   LV 206%Z @ Tint16 |->Vint32(Int.repr 4) ** LV 207%Z @ Tint32 |->Vint32(Int.repr 5) **
   LV 208%Z @ (Tptr Tvoid) |->Vnull ** LV 204%Z @ Tint16 |->Vint32(Int.repr 7) **
   LV 209%Z @ Tint8 |->Vundef ** ROR)).
 { eapply ROStar with(m1:=emp)(m2:=merge ROLocals ROOuter).
   - apply map_join_comm;apply map_join_emp.
   - exact G.
   - clear -H;sep auto. }
 unfold ROInput,V293_tcb_enabled_external,V293_create_tcb_arguments.
 assert(S:ROState ROLE(merge ROLocals ROOuter)nil |=
  <||spec_done None||> ** OS[(fun _=>false),true,nil,nil] **
  ((Agvarenv 91%Z(Tptr V293_tcb_type)(401%positive,0%Z) ** ROFrame) **
  (LV 101%Z @ Tint8 |->V293_byteval 11 **
   LV 108%Z @ (Tptr Tint32) |->Vnull ** LV 205%Z @ (Tptr Tint32) |->Vnull **
   LV 206%Z @ Tint16 |->Vint32(Int.repr 4) ** LV 207%Z @ Tint32 |->Vint32(Int.repr 5) **
   LV 208%Z @ (Tptr Tvoid) |->Vnull ** LV 204%Z @ Tint16 |->Vint32(Int.repr 7) **
   LV 209%Z @ Tint8 |->Vundef ** ROR))).
 { apply astar_l_aop'_intro;[ |reflexivity].
   assert(Ordered:ROState ROLE(merge ROLocals ROOuter)nil |=
    Aisr(fun _=>false) ** Aie true ** Ais nil ** Acs nil **
    ((Agvarenv 91%Z(Tptr V293_tcb_type)(401%positive,0%Z) ** ROFrame) **
     (LV 101%Z @ Tint8 |->V293_byteval 11 **
      LV 108%Z @ (Tptr Tint32) |->Vnull ** LV 205%Z @ (Tptr Tint32) |->Vnull **
      LV 206%Z @ Tint16 |->Vint32(Int.repr 4) ** LV 207%Z @ Tint32 |->Vint32(Int.repr 5) **
      LV 208%Z @ (Tptr Tvoid) |->Vnull ** LV 204%Z @ Tint16 |->Vint32(Int.repr 7) **
      LV 209%Z @ Tint8 |->Vundef ** ROR))).
   { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
     apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[exact B|reflexivity]. }
   clear -Ordered;sep auto. }
 clear -S;sep auto.
Qed.
Theorem ROCallerHasNoSharedBytes : forall b off,
 b=401%positive \/ b=403%positive -> get ROCaller(b,off)=None.
Proof.
 intros b off[E|E];subst b;
 unfold ROCaller,ROLocals,ROOuter,ROCurrent,ROSentinel,ROLocal101,ROLocal108,ROLocal205,ROLocal206,ROLocal207,ROLocal208,ROLocal204,ROLocal209,ROBytes;
 repeat first[rewrite map_merge_semp by reflexivity|rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Qed.
Definition ROOwnedInput cs := V293_tcb_enabled_external 401%positive ROR(spec_done None)(fun _=>false)nil cs **
 LV 209%Z @ Tint8 |->Vundef **
 V293_create_tcb_arguments 11 Vnull Vnull(Vint32(Int.repr 4))(Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7))
 (V293_tcb_table_binding 403%positive ** (V293_create_owned_share 403%positive ROReserved 11 ** Aemp)).
Lemma ROOwnerLiteral : forall le cs,
 ROState le ROOwner cs |= V293_create_owned_share 403%positive ROReserved 11.
Proof. intros. split;[apply V293_encoded_memory_mapsto|reflexivity]. Qed.
Lemma RORawOwnerJoin : join ROCaller ROOwner(merge ROCaller ROOwner).
Proof.
 apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 403%positive)as[E|E].
 - left. apply ROCallerHasNoSharedBytes;right;exact E.
 - right;left. unfold ROOwner. apply V293_encoded_memory_outside;left;congruence.
Qed.
Theorem ROOwnedCallerLiteral : ROState ROLE(merge ROCaller ROOwner)nil |= ROOwnedInput nil.
Proof.
 pose proof(ROStar _ _ _ _ _ _ _ RORawOwnerJoin ROCallerLiteral(ROOwnerLiteral ROLE nil))as H.
 unfold ROOwnedInput,ROInput,ROFrame,V293_create_tcb_arguments in *;clear -H;sep auto.
Qed.
Theorem ROOwnedBorrowEquivalence : forall n,
 Aisr(fun _=>false) ** invlth_isr ROInv 0 n <==>
 Aisr(fun _=>false) ** V293_create_owned_pool 403%positive ROReserved 11
   (Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull **
    Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0)).
Proof.
 intros n s. split;intro H.
 - apply ROBorrowEquivalence in H. unfold ROCore,V293_tcb_empty_pool,V293_create_owned_pool in *;clear -H;sep auto.
 - apply ROBorrowEquivalence. unfold ROCore,V293_tcb_empty_pool,V293_create_owned_pool in *;clear -H;sep auto.
Qed.
Definition ROSpec cs : funspec := fun f=>if Z.eq_dec f 500%Z then
 Some(V293_tcb_enabled_fpre 401%positive ROR(spec_done None)(fun _=>false)nil cs RORFun,
      V293_tcb_enabled_fpost 401%positive ROR(spec_done None)(fun _=>false)nil cs RORFun,
      (Tint8,rev V293_TCBInit_argument_types))else None.
Definition ROProgram : progunit := fun f=>if Z.eq_dec f 500%Z then
 Some(V293_TCBInit_function 501%Z 502%Z)else None.
Definition ROArgs := rev(V293_tcb_success_arguments 11 Vnull Vnull
 (Vint32(Int.repr 4))(Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7))).
Definition ROPre cs := V293_tcb_internal_pre_cells(V293_byteval 11)Vnull Vnull
 (Vint32(Int.repr 4))(Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7)) **
 V293_tcb_enabled_external 401%positive ROR(spec_done None)(fun _=>false)nil cs ** V293_tcb_internal_domain.
Definition ROPost cs result := V293_tcb_internal_post_cells **
 ([|result=Some(Vint32(Int.repr 66))|] **
 V293_tcb_enabled_external 401%positive ROR(spec_done None)(fun _=>false)nil cs) ** V293_tcb_internal_domain.
Lemma ROBuilders : forall cs,
 Some(ROPre cs)=BuildPreI ROProgram 500%Z ROArgs nil
 (V293_tcb_enabled_fpre 401%positive ROR(spec_done None)(fun _=>false)nil cs RORFun)ROTid /\
 Some(ROPost cs)=BuildRetI ROProgram 500%Z ROArgs nil
 (V293_tcb_enabled_fpost 401%positive ROR(spec_done None)(fun _=>false)nil cs RORFun)ROTid.
Proof. intros;split;reflexivity. Qed.
Theorem ROCalleeCheckedSameSpec : forall sd cs,
 InfRules(ROSpec cs)sd V293_witness_li ROInv(ROPost cs)Afalse
 (ROPre cs)(V293_TCBInit_function_body 501%Z 502%Z)Afalse ROTid.
Proof.
 intros sd cs. eapply V293_OS_TCBInit_empty_enabled_contract
 with(P:=ROProgram)(f:=500%Z)(K:=V293_create_owned_pool 403%positive ROReserved 11(Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0)))
 (good:=RORFun)(vl:=ROArgs)(lg:=nil)(bf:=401%positive)(R:=ROR)
 (aop:=spec_done None)(isr:=fun _=>false)(is:=nil)(cs:=cs).
 - vm_compute;lia.
 - apply RORGood.
 - apply RORInv.
 - intros s H;apply ROBorrowEquivalence in H;exact H.
 - intros s H;apply ROBorrowEquivalence;exact H.
 - reflexivity.
 - apply(proj1(ROBuilders cs)).
 - apply(proj2(ROBuilders cs)).
Qed.
Definition ROReturn cs := V293_create_enabled_failure_return 403%positive 11
 (V293_create_enabled_failure_kept 401%positive Vnull Vnull(Vint32(Int.repr 4))
 (Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7))ROR Aemp)(spec_done None)(fun _=>false)nil cs.
Theorem ROCallerCheckedSameSpec : forall sd cs,
 InfRules(ROSpec cs)sd V293_witness_li ROInv(ROReturn cs)Afalse(ROOwnedInput cs)
 (sseq(V293_TaskCreateExt_TCB_call 209%Z 500%Z 101%Z 108%Z 205%Z 206%Z 207%Z 208%Z 204%Z)
  (V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z 97%Z 503%Z))Afalse ROTid.
Proof.
 intros sd cs. apply V293_OSTaskCreateExt_owned_empty_call_suffix
 with(reserved:=ROReserved)
 (K:=Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull **
      Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0))(good:=RORFun).
 - lia.
 - vm_compute;lia.
 - apply RORGood.
 - exact I.
 - vm_compute;repeat split;discriminate.
 - apply RORInv.
 - intros s H;apply ROOwnedBorrowEquivalence in H;exact H.
 - intros s H;apply ROOwnedBorrowEquivalence;exact H.
 - reflexivity.
Qed.
Print Assumptions ROOwnedCallerLiteral.
Print Assumptions ROCalleeCheckedSameSpec.
Print Assumptions ROCallerCheckedSameSpec.

Definition ROFullReserved := V293_encoded_memory 403%positive 44 true
 (encode_val(Tptr V293_tcb_type)(Vptr ROReserved)).
Lemma ROHalfJoin : join ROOwner ROOwner ROFullReserved.
Proof.
 assert(H:ROState ROLE ROFullReserved nil |=
  Amapsto(403%positive,44%Z)(Tptr V293_tcb_type)true(Vptr ROReserved)).
 { split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 apply separate_rw2ro in H. apply sat_split in H.
 destruct H as[m1[m2[o1[o2[JM[JO[[P1 E1][P2 E2]]]]]]]].
 assert(P:mapstoval(403%positive,44%Z)(Tptr V293_tcb_type)false(Vptr ROReserved)ROOwner).
 { apply V293_encoded_memory_mapsto. }
 destruct P as[vl[V P]]. rewrite <- V in P.
 destruct P1 as[vl1[V1 P1]]. destruct P2 as[vl2[V2 P2]].
 rewrite <- V1 in P1. rewrite <- V2 in P2.
 assert(m1=ROOwner)by(eapply V293_reservation_bytes_exact;eauto).
 assert(m2=ROOwner)by(eapply V293_reservation_bytes_exact;eauto).
 subst m1 m2;exact JM.
Qed.
(* The proposed permission-erased pool would accept both subfragments of the
   same ambient full cell. This is a proved counterexample, not a failed tactic. *)
Definition ROBadPool := EX permission:bool,
 Amapsto(403%positive,44%Z)(Tptr V293_tcb_type)permission(Vptr ROReserved).
Theorem ROArbitraryPermissionNotPrecise : ~precise ROBadPool.
Proof.
 intro Precise.
 assert(Hhalf:ROState ROLE ROOwner nil |= ROBadPool).
 { exists false. split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 assert(Hfull:ROState ROLE ROFullReserved nil |= ROBadPool).
 { exists true. split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 assert(SHalf:Maps.sub ROOwner ROFullReserved)by(exists ROOwner;apply ROHalfJoin).
 assert(SFull:Maps.sub ROFullReserved ROFullReserved)by(exists(emp:mem);apply map_join_emp).
 assert(SO:Maps.sub(emp:osabst)(emp:osabst))by(exists(emp:osabst);apply map_join_emp).
 pose proof(Precise(ROState ROLE emp nil)ROOwner ROFullReserved emp emp
   Hhalf Hfull ROFullReserved emp SHalf SFull SO SO)as[E _].
 assert(G1:get ROOwner(403%positive,44%Z)=Some(false,Pointer 405%positive Int.zero 3)).
 { assert(P:mapstoval(403%positive,44%Z)(Tptr V293_tcb_type)false(Vptr ROReserved)ROOwner)
     by apply V293_encoded_memory_mapsto.
   destruct P as[vl[Encoded P]]. rewrite <- Encoded in P. cbn[encode_val ROReserved inj_pointer]in P.
   eapply V293_reservation_first_byte;exact P. }
 assert(G2:get ROFullReserved(403%positive,44%Z)=Some(true,Pointer 405%positive Int.zero 3)).
 { assert(P:mapstoval(403%positive,44%Z)(Tptr V293_tcb_type)true(Vptr ROReserved)ROFullReserved)
     by apply V293_encoded_memory_mapsto.
   destruct P as[vl[Encoded P]]. rewrite <- Encoded in P. cbn[encode_val ROReserved inj_pointer]in P.
   eapply V293_reservation_first_byte;exact P. }
 rewrite E in G1. rewrite G2 in G1;discriminate.
Qed.

Definition ROWrong := Vptr(701%positive,Int.zero).
Theorem ROWrongAcceptedWithoutOwner :
 ROState ROLE(ROSlot ROWrong)nil |= V293_reservation_pool(403%positive,44%Z)ROReserved.
Proof.
 exists ROWrong. apply astar_l_apure_intro;[ |reflexivity].
 split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Theorem ROWrongCannotJoinOwner : forall M, ~join ROOwner(ROSlot ROWrong)M.
Proof.
 intros M J. assert(H:ROState ROLE M nil |=
 V293_reservation_owner(403%positive,44%Z)ROReserved **
 Amapsto(403%positive,44%Z)(Tptr V293_tcb_type)
  (V293_reservation_permission ROReserved ROWrong)ROWrong).
 { eapply ROStar;[exact J|split;[apply V293_encoded_memory_mapsto|reflexivity]| ].
   split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 eapply V293_reservation_excludes_other_value with(v:=ROWrong);[reflexivity| |exact H].
 unfold ROWrong,ROReserved;congruence.
Qed.
Theorem ROOwnerRemovedAdmitsWrong : exists M, join(emp:mem)(ROSlot ROWrong)M.
Proof. exists(ROSlot ROWrong). apply map_join_comm;apply map_join_emp. Qed.

Lemma ROBaseCallerOutsideShared : forall b off,
 b=401%positive \/ b=403%positive \/ b=404%positive -> get ROCaller(b,off)=None.
Proof.
 intros b off[E|[E|E]];subst b;
 unfold ROCaller,ROLocals,ROOuter,ROCurrent,ROSentinel,ROLocal101,ROLocal108,ROLocal205,ROLocal206,ROLocal207,ROLocal208,ROLocal204,ROLocal209,ROBytes;
 repeat first[rewrite map_merge_semp by reflexivity|rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Qed.
Definition ROWholeMemory := merge ROCaller(merge ROFree(merge ROCounter ROFullReserved)).
Theorem ROOwnedWholeLiteral : ROState ROLE ROWholeMemory nil |=
 ROOwnedInput nil ** invlth_isr ROInv 0 INUM.
Proof.
 assert(H:ROState ROLE ROWholeMemory nil |= ROInput nil **
   (Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull **
    Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0) **
    Amapsto(403%positive,44%Z)(Tptr V293_tcb_type)true(Vptr ROReserved))).
 { unfold ROWholeMemory. eapply ROStar with(m1:=ROCaller).
   - apply map_join_merge;apply map_disjoint;intros[b off].
     destruct(Pos.eq_dec b 401%positive)as[E|E].
     + left;apply ROBaseCallerOutsideShared;auto.
     + destruct(Pos.eq_dec b 403%positive)as[F|F].
       * left;apply ROBaseCallerOutsideShared;auto.
       * destruct(Pos.eq_dec b 404%positive)as[G|G].
         -- left;apply ROBaseCallerOutsideShared;auto.
         -- right;left. unfold ROFree,ROCounter,ROFullReserved,ROBytes;
            repeat first[rewrite map_merge_semp by reflexivity|rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
   - apply ROCallerLiteral.
   - eapply ROStar with(m1:=ROFree).
     + apply map_join_merge;apply map_disjoint;intros[b off].
       destruct(Pos.eq_dec b 401%positive);[subst b;right;left|left];
       unfold ROFree,ROCounter,ROFullReserved,ROBytes;
       repeat first[rewrite map_merge_semp by reflexivity|rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
     + split;[apply V293_encoded_memory_mapsto|reflexivity].
     + eapply ROStar with(m1:=ROCounter).
       * apply map_join_merge;apply map_disjoint;intros[b off].
         destruct(Pos.eq_dec b 404%positive);[subst b;right;left|left];
         unfold ROCounter,ROFullReserved,ROBytes;apply V293_encoded_memory_outside;left;congruence.
       * split;[apply V293_encoded_memory_mapsto|reflexivity].
       * split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 assert(S:ROState ROLE ROWholeMemory nil |=
 Amapsto(403%positive,44%Z)(Tptr V293_tcb_type)true(Vptr ROReserved) **
 (ROInput nil ** Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull **
 Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0)))by(clear -H;sep auto).
 eapply astar_mono in S;[ |apply V293_reservation_publish|intros st HS;exact HS].
 assert(B:ROState ROLE ROWholeMemory nil |= ROOwnedInput nil ** ROCore).
 { unfold ROOwnedInput,ROInput,ROFrame,V293_create_tcb_arguments,V293_create_owned_share,
     ROCore,V293_tcb_empty_pool,V293_create_owned_pool in *;clear -S;sep auto. }
 assert(C:ROState ROLE ROWholeMemory nil |= ROOwnedInput nil ** (Aisr(fun _=>false) ** ROCore)).
 { apply astar_l_aisr_intro with(i:=(fun _=>false))in B;[clear -B;sep auto|reflexivity]. }
 eapply astar_mono in C;[ |intros st HS;exact HS|intros st HS;apply ROBorrowEquivalence;exact HS].
 clear -C;sep auto.
Qed.

Theorem ROReservationCheckedSameSpec : forall sd cs,
 InfRules(ROSpec cs)sd V293_witness_li ROInv (fun _=>Afalse) Afalse
 (V293_create_slot_state 201%positive 211%positive 403%positive 404%positive 405%positive
  11 0 None(Vint32 Int.zero)
  (Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull)ROR
  (spec_done None)(fun _=>false)nil cs)
 (sseq(sassign(earrayelem(evar 92%Z)(evar 101%Z))(V293_task_prio_reserved_expr 97%Z))(sprim excrit))
 (V293_create_enabled_state 201%positive 211%positive 11(Vint32 Int.zero)
  (V293_create_owned_share 403%positive ROReserved 11 **
   V293_create_slot_views 403%positive 404%positive 405%positive ** ROR)
  (spec_done None)(fun _=>false)nil cs)ROTid.
Proof.
 intros sd cs. apply V293_OSTaskCreateExt_owned_reservation.
 - lia.
 - apply RORGood.
 - apply RORInv.
 - intros s H. apply ROBorrowEquivalence.
   unfold ROCore,V293_tcb_empty_pool,V293_create_owned_pool in *;clear -H;sep auto.
Qed.
