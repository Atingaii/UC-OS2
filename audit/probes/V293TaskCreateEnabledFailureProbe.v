(* Independent literal caller/shared partition. The same finite Spec and Inv
   check the actual call/suffix and the full callee, without execution oracles.
   This is not a production reservation invariant or a WFIFun proof. *)
Require Import CertiOS.framework.include_frm.
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
Definition RBGE : env := set (set (sig 91%Z (401%positive,Tptr V293_tcb_type))
 OSTCBCur (402%positive,Tptr Tvoid)) 92%Z (403%positive,Tarray(Tptr V293_tcb_type)13).
Definition RBLE : env := set (set (set (set (set (set (set (sig 101%Z (201%positive,Tint8)) 108%Z (208%positive,Tptr Tint32)) 205%Z (205%positive,Tptr Tint32)) 206%Z (206%positive,Tint16)) 207%Z (207%positive,Tint32)) 208%Z (210%positive,Tptr Tvoid)) 204%Z (204%positive,Tint16)) 209%Z (209%positive,Tint8).
Definition RBTid : tid := (301%positive,Int.repr 8).
Definition RBBytes b permission tp v := V293_encoded_memory b 0 permission(encode_val tp v).
Definition RBState le M cs : RstateOP :=
 (RBGE,le,M,(fun _=>false),(true,nil,cs),(emp:osabst),spec_done None).
Definition RBCurrent := RBBytes 402%positive false(Tptr Tvoid)(Vptr RBTid).
Definition RBSentinel := RBBytes 601%positive true Tint8(Vint32(Int.repr 77)).
Definition RBOuter := merge RBCurrent RBSentinel.
Definition RBR := CurTid RBTid ** LINV V293_witness_li RBTid nil **
 Amapsto(601%positive,0%Z)Tint8 true(Vint32(Int.repr 77)).
Lemma RBStar : forall le m1 m2 m cs p q,
 join m1 m2 m -> RBState le m1 cs |= p -> RBState le m2 cs |= q -> RBState le m cs |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2. exists(emp:osabst). exists(emp:osabst).
 split;[exact H| ]. split;[apply map_join_emp| ]. split;assumption.
Qed.
Lemma RBLocal : forall le x b tp v cs,
 get le x=Some(b,tp) -> RBState le(RBBytes b true tp v)cs |= LV x @ tp |->v.
Proof.
 intros le x b tp v cs E. unfold Alvarmapsto,Alvarenv'. exists b.
 eapply RBStar with(m1:=emp)(m2:=RBBytes b true tp v).
 - apply map_join_comm;apply map_join_emp.
 - exists b. split;[exact E| ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma RBRSpatial : forall le cs, RBState le RBOuter cs |= RBR.
Proof.
 intros le cs. unfold RBR,RBOuter.
 eapply RBStar with(m1:=RBCurrent)(m2:=RBSentinel).
 - apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 402%positive);[subst b;right;left|left];
   unfold RBCurrent,RBSentinel,RBBytes;apply V293_encoded_memory_outside;left;congruence.
 - unfold CurTid. exists Tvoid. exists 402%positive.
   eapply RBStar with(m1:=emp)(m2:=RBCurrent).
   + apply map_join_comm;apply map_join_emp.
   + exists 402%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply RBStar with(m1:=emp)(m2:=RBSentinel).
   + apply map_join_comm;apply map_join_emp.
   + unfold LINV. apply astar_comm. apply astar_l_apure_intro.
     * split;reflexivity.
     * apply V293_witness_li_good.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma RBRGood : GoodFrm RBR.
Proof. cbn[RBR CurTid LINV V293_witness_li GoodFrm];repeat split;exact I. Qed.
Lemma RBRFun : GoodFunAsrt RBR.
Proof.
 cbn[RBR CurTid LINV V293_witness_li GoodFunAsrt Agvarmapsto Agvarenv' Aptrmapsto].
 repeat split;intros;repeat split;exact I.
Qed.
Lemma RBRInv : RBR ==> CurLINV V293_witness_li RBTid.
Proof. intros s H. unfold CurLINV. exists(nil:list logicvar). unfold RBR in H;clear -H;sep auto. Qed.
Definition RBFree := RBBytes 401%positive false(Tptr V293_tcb_type)Vnull.
Definition RBSlot slot := V293_encoded_memory 403%positive 44 true(encode_val(Tptr V293_tcb_type)slot).
Definition RBCore := V293_tcb_empty_pool 401%positive(V293_create_rollback_pool 403%positive 11 Aemp).
Lemma RBBytesUnique : forall vl l permission m1 m2,
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
Lemma RBHeadPrecise : precise(Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull).
Proof.
 intros s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 destruct s as [[[[[[ge le] mem] ir] aux] oldO] op].
 change(mapstoval(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull M1 /\ O1=emp)in H1.
 change(mapstoval(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull M2 /\ O2=emp)in H2.
 destruct H1 as[[v1[E1 P1]]Oe1]. destruct H2 as[[v2[E2 P2]]Oe2].
 subst v1 v2. split;[eapply RBBytesUnique;eauto|congruence].
Qed.
Lemma RBPoolStorage : V293_create_rollback_pool 403%positive 11 Aemp ==>
 V293_storage_cell(403%positive,44%Z)(Tptr V293_tcb_type).
Proof. intros s[v H]. exists v. clear -H;sep auto. Qed.
Lemma RBCorePrecise : precise RBCore.
Proof.
 unfold RBCore,V293_tcb_empty_pool. apply precise_star;[apply RBHeadPrecise| ].
 intros s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 eapply V293_storage_cell_precise;[apply RBPoolStorage;exact H1|apply RBPoolStorage;exact H2|exact HM1|exact HM2|exact HO1|exact HO2].
Qed.
Lemma RBCoreGood : GoodInvAsrt RBCore.
Proof. cbn[RBCore V293_tcb_empty_pool V293_create_rollback_pool GoodInvAsrt];tauto. Qed.
Lemma RBCoreISR : assertion.inv_isr_prop RBCore.
Proof.
 unfold assertion.inv_isr_prop,RBCore,V293_tcb_empty_pool,V293_create_rollback_pool.
 repeat split;intros;destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];exact H.
Qed.
Definition RBInv : Inv := fun i=>match i with
 | O=>mkinvasrt RBCoreGood(conj RBCorePrecise RBCoreISR)
 | S j=>V293_shared_inv(S j) end.
Lemma RBNoisrTail : forall n i,starinv_noisr RBInv(S i)n <==> Aemp.
Proof.
 induction n;intros i s;cbn[starinv_noisr];[reflexivity| ].
 change(s |= Aemp ** starinv_noisr RBInv(S(S i))n <-> s |= Aemp).
 split;intro H.
 - apply astar_l_aemp_elim in H. apply IHn in H;exact H.
 - apply astar_l_aemp_intro. apply IHn;exact H.
Qed.
Lemma RBNoisrCore : forall n,starinv_noisr RBInv 0 n <==> RBCore.
Proof.
 intros[ |n]s;[reflexivity| ].
 change(s |= RBCore ** starinv_noisr RBInv 1 n <-> s |= RBCore).
 split;intro H.
 - apply astar_r_aemp_elim. eapply astar_mono;[intros st HS;exact HS|intros st HS;apply RBNoisrTail in HS;exact HS|exact H].
 - eapply astar_mono;[intros st HS;exact HS|intros st HS;apply RBNoisrTail;exact HS| ]. apply astar_r_aemp_intro;exact H.
Qed.
Theorem RBBorrowEquivalence : forall n,
 Aisr(fun _=>false) ** invlth_isr RBInv 0 n <==> Aisr(fun _=>false) ** RBCore.
Proof.
 intros n s. destruct s as [[[[[[ge le] M] ir] aux] O] op]. split;intro H.
 all:(apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&H1&H2);
 destruct H1 as[E Empty];cbn in E;subst ir;
 apply sat_split';exists m1;exists m2;exists o1;exists o2;
 split;[exact JM| ];split;[exact JO| ];split;[split;[reflexivity|exact Empty]| ]).
 - unfold invlth_isr in H2. rewrite Nat.sub_0_r in H2.
   apply RBNoisrCore with(n:=n). eapply invisr_imply_noisr';[ |exact H2]. reflexivity.
 - unfold invlth_isr. rewrite Nat.sub_0_r.
   apply V293_shared_clear_noisr_close;[reflexivity| ]. apply RBNoisrCore;exact H2.
Qed.
Theorem RBSharedLiteral : forall le cs slot,
 rule_type_val_match(Tptr V293_tcb_type)slot=true ->
 RBState le(merge RBFree(RBSlot slot))cs |= invlth_isr RBInv 0 INUM.
Proof.
 intros le cs slot Typed. unfold invlth_isr. rewrite Nat.sub_0_r.
 apply V293_shared_clear_noisr_close;[reflexivity| ]. apply RBNoisrCore.
 unfold RBCore,V293_tcb_empty_pool.
 eapply RBStar with(m1:=RBFree)(m2:=RBSlot slot).
 - apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 401%positive);[subst b;right;left|left];
   unfold RBFree,RBSlot,RBBytes;apply V293_encoded_memory_outside;left;congruence.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - exists slot. apply astar_l_apure_intro;[ |exact Typed]. apply astar_r_aemp_intro.
   split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Theorem RBSameInvariantDifferentSlots : forall le cs,
 RBState le(merge RBFree(RBSlot Vnull))cs |= invlth_isr RBInv 0 INUM /\
 RBState le(merge RBFree(RBSlot(Vptr(701%positive,Int.zero))))cs |= invlth_isr RBInv 0 INUM.
Proof. intros;split;apply RBSharedLiteral;reflexivity. Qed.
Definition RBLocal101 := RBBytes 201%positive true(Tint8)(V293_byteval 11).
Definition RBLocal108 := RBBytes 208%positive true(Tptr Tint32)(Vnull).
Definition RBLocal205 := RBBytes 205%positive true(Tptr Tint32)(Vnull).
Definition RBLocal206 := RBBytes 206%positive true(Tint16)(Vint32(Int.repr 4)).
Definition RBLocal207 := RBBytes 207%positive true(Tint32)(Vint32(Int.repr 5)).
Definition RBLocal208 := RBBytes 210%positive true(Tptr Tvoid)(Vnull).
Definition RBLocal204 := RBBytes 204%positive true(Tint16)(Vint32(Int.repr 7)).
Definition RBLocal209 := RBBytes 209%positive true(Tint8)(Vundef).
Definition RBLocals := merge RBLocal101 (merge RBLocal108 (merge RBLocal205 (merge RBLocal206 (merge RBLocal207 (merge RBLocal208 (merge RBLocal204 (merge RBLocal209 ((emp:mem))))))))).
Definition RBCaller := merge RBLocals RBOuter.
Definition RBFrame := V293_tcb_table_binding 403%positive ** Aemp.
Definition RBInput cs := V293_tcb_enabled_external 401%positive RBR(spec_done None)(fun _=>false)nil cs **
 LV 209%Z @ Tint8 |->Vundef **
 V293_create_tcb_arguments 11 Vnull Vnull(Vint32(Int.repr 4))(Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7))RBFrame.
Lemma RBGlobals : RBState RBLE emp nil |= Agvarenv 91%Z(Tptr V293_tcb_type)(401%positive,0%Z) ** RBFrame.
Proof.
 unfold RBFrame. eapply RBStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 - exists 401%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - apply astar_r_aemp_intro. split.
   + exists 403%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[ |split;reflexivity]. intros[v H]. vm_compute in H;discriminate.
Qed.
Ltac RBLocalsApart b :=
 apply map_join_merge;apply map_disjoint;intros[other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold RBLocals,RBLocal101,RBLocal108,RBLocal205,RBLocal206,RBLocal207,RBLocal208,RBLocal204,RBLocal209,RBBytes;
 repeat first[rewrite map_merge_semp by reflexivity|rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Lemma RBLocalsSpatial : forall cs, RBState RBLE RBLocals cs |=
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
 intro cs. unfold RBLocals.
 eapply RBStar with(m1:=RBLocal101).
 { RBLocalsApart 201%positive. }
 { apply RBLocal. vm_compute;reflexivity. }
 eapply RBStar with(m1:=RBLocal108).
 { RBLocalsApart 208%positive. }
 { apply RBLocal. vm_compute;reflexivity. }
 eapply RBStar with(m1:=RBLocal205).
 { RBLocalsApart 205%positive. }
 { apply RBLocal. vm_compute;reflexivity. }
 eapply RBStar with(m1:=RBLocal206).
 { RBLocalsApart 206%positive. }
 { apply RBLocal. vm_compute;reflexivity. }
 eapply RBStar with(m1:=RBLocal207).
 { RBLocalsApart 207%positive. }
 { apply RBLocal. vm_compute;reflexivity. }
 eapply RBStar with(m1:=RBLocal208).
 { RBLocalsApart 210%positive. }
 { apply RBLocal. vm_compute;reflexivity. }
 eapply RBStar with(m1:=RBLocal204).
 { RBLocalsApart 204%positive. }
 { apply RBLocal. vm_compute;reflexivity. }
 eapply RBStar with(m1:=RBLocal209).
 { RBLocalsApart 209%positive. }
 { apply RBLocal. vm_compute;reflexivity. }
 split;reflexivity.
Qed.
Theorem RBCallerLiteral : RBState RBLE RBCaller nil |= RBInput nil.
Proof.
 unfold RBCaller. assert(L:=RBLocalsSpatial nil). assert(R:=RBRSpatial RBLE nil).
 assert(G:=RBGlobals).
 assert(J:join RBLocals RBOuter(merge RBLocals RBOuter)).
 { apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 402%positive)as[E|E];[subst b;left| ].
   - unfold RBLocals,RBLocal101,RBLocal108,RBLocal205,RBLocal206,RBLocal207,RBLocal208,RBLocal204,RBLocal209,RBBytes;
     repeat first[rewrite map_merge_semp by reflexivity|rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
   - destruct(Pos.eq_dec b 601%positive)as[F|F];[subst b;left|right;left].
     + unfold RBLocals,RBLocal101,RBLocal108,RBLocal205,RBLocal206,RBLocal207,RBLocal208,RBLocal204,RBLocal209,RBBytes;
       repeat first[rewrite map_merge_semp by reflexivity|rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
     + unfold RBOuter,RBCurrent,RBSentinel,RBBytes.
       repeat first[rewrite map_merge_semp by reflexivity|rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity. }
 pose proof(RBStar _ _ _ _ _ _ _ J L R)as H.
 assert(B:RBState RBLE(merge RBLocals RBOuter)nil |=
  (Agvarenv 91%Z(Tptr V293_tcb_type)(401%positive,0%Z) ** RBFrame) **
  (LV 101%Z @ Tint8 |->V293_byteval 11 **
   LV 108%Z @ (Tptr Tint32) |->Vnull ** LV 205%Z @ (Tptr Tint32) |->Vnull **
   LV 206%Z @ Tint16 |->Vint32(Int.repr 4) ** LV 207%Z @ Tint32 |->Vint32(Int.repr 5) **
   LV 208%Z @ (Tptr Tvoid) |->Vnull ** LV 204%Z @ Tint16 |->Vint32(Int.repr 7) **
   LV 209%Z @ Tint8 |->Vundef ** RBR)).
 { eapply RBStar with(m1:=emp)(m2:=merge RBLocals RBOuter).
   - apply map_join_comm;apply map_join_emp.
   - exact G.
   - clear -H;sep auto. }
 unfold RBInput,V293_tcb_enabled_external,V293_create_tcb_arguments.
 assert(S:RBState RBLE(merge RBLocals RBOuter)nil |=
  <||spec_done None||> ** OS[(fun _=>false),true,nil,nil] **
  ((Agvarenv 91%Z(Tptr V293_tcb_type)(401%positive,0%Z) ** RBFrame) **
  (LV 101%Z @ Tint8 |->V293_byteval 11 **
   LV 108%Z @ (Tptr Tint32) |->Vnull ** LV 205%Z @ (Tptr Tint32) |->Vnull **
   LV 206%Z @ Tint16 |->Vint32(Int.repr 4) ** LV 207%Z @ Tint32 |->Vint32(Int.repr 5) **
   LV 208%Z @ (Tptr Tvoid) |->Vnull ** LV 204%Z @ Tint16 |->Vint32(Int.repr 7) **
   LV 209%Z @ Tint8 |->Vundef ** RBR))).
 { apply astar_l_aop'_intro;[ |reflexivity].
   assert(Ordered:RBState RBLE(merge RBLocals RBOuter)nil |=
    Aisr(fun _=>false) ** Aie true ** Ais nil ** Acs nil **
    ((Agvarenv 91%Z(Tptr V293_tcb_type)(401%positive,0%Z) ** RBFrame) **
     (LV 101%Z @ Tint8 |->V293_byteval 11 **
      LV 108%Z @ (Tptr Tint32) |->Vnull ** LV 205%Z @ (Tptr Tint32) |->Vnull **
      LV 206%Z @ Tint16 |->Vint32(Int.repr 4) ** LV 207%Z @ Tint32 |->Vint32(Int.repr 5) **
      LV 208%Z @ (Tptr Tvoid) |->Vnull ** LV 204%Z @ Tint16 |->Vint32(Int.repr 7) **
      LV 209%Z @ Tint8 |->Vundef ** RBR))).
   { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
     apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[exact B|reflexivity]. }
   clear -Ordered;sep auto. }
 clear -S;sep auto.
Qed.
Theorem RBCallerHasNoSharedBytes : forall b off,
 b=401%positive \/ b=403%positive -> get RBCaller(b,off)=None.
Proof.
 intros b off[E|E];subst b;
 unfold RBCaller,RBLocals,RBOuter,RBCurrent,RBSentinel,RBLocal101,RBLocal108,RBLocal205,RBLocal206,RBLocal207,RBLocal208,RBLocal204,RBLocal209,RBBytes;
 repeat first[rewrite map_merge_semp by reflexivity|rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Qed.
Theorem RBWholePartition : forall slot,
 join RBCaller(merge RBFree(RBSlot slot))(merge RBCaller(merge RBFree(RBSlot slot))).
Proof.
 intro slot. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 401%positive)as[E|E].
 - left. apply RBCallerHasNoSharedBytes;left;exact E.
 - destruct(Pos.eq_dec b 403%positive)as[F|F].
   + left. apply RBCallerHasNoSharedBytes;right;exact F.
   + right;left. unfold RBFree,RBSlot,RBBytes.
     repeat first[rewrite map_merge_semp by reflexivity|rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Qed.
Theorem RBWholeSpatial : forall slot,
 rule_type_val_match(Tptr V293_tcb_type)slot=true ->
 RBState RBLE(merge RBCaller(merge RBFree(RBSlot slot)))nil |= RBInput nil ** invlth_isr RBInv 0 INUM.
Proof.
 intros slot Typed. eapply RBStar.
 - apply RBWholePartition.
 - apply RBCallerLiteral.
 - apply RBSharedLiteral;exact Typed.
Qed.
Definition RBSpec cs : funspec := fun f=>if Z.eq_dec f 500%Z then
 Some(V293_tcb_enabled_fpre 401%positive RBR(spec_done None)(fun _=>false)nil cs RBRFun,
      V293_tcb_enabled_fpost 401%positive RBR(spec_done None)(fun _=>false)nil cs RBRFun,
      (Tint8,rev V293_TCBInit_argument_types))else None.
Definition RBProgram : progunit := fun f=>if Z.eq_dec f 500%Z then
 Some(V293_TCBInit_function 501%Z 502%Z)else None.
Definition RBArgs := rev(V293_tcb_success_arguments 11 Vnull Vnull
 (Vint32(Int.repr 4))(Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7))).
Definition RBPre cs := V293_tcb_internal_pre_cells(V293_byteval 11)Vnull Vnull
 (Vint32(Int.repr 4))(Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7)) **
 V293_tcb_enabled_external 401%positive RBR(spec_done None)(fun _=>false)nil cs ** V293_tcb_internal_domain.
Definition RBPost cs result := V293_tcb_internal_post_cells **
 ([|result=Some(Vint32(Int.repr 66))|] **
 V293_tcb_enabled_external 401%positive RBR(spec_done None)(fun _=>false)nil cs) ** V293_tcb_internal_domain.
Lemma RBBuilders : forall cs,
 Some(RBPre cs)=BuildPreI RBProgram 500%Z RBArgs nil
 (V293_tcb_enabled_fpre 401%positive RBR(spec_done None)(fun _=>false)nil cs RBRFun)RBTid /\
 Some(RBPost cs)=BuildRetI RBProgram 500%Z RBArgs nil
 (V293_tcb_enabled_fpost 401%positive RBR(spec_done None)(fun _=>false)nil cs RBRFun)RBTid.
Proof. intros;split;reflexivity. Qed.
Theorem RBCalleeCheckedSameSpec : forall sd cs,
 InfRules(RBSpec cs)sd V293_witness_li RBInv(RBPost cs)Afalse
 (RBPre cs)(V293_TCBInit_function_body 501%Z 502%Z)Afalse RBTid.
Proof.
 intros sd cs. eapply V293_OS_TCBInit_empty_enabled_contract
 with(P:=RBProgram)(f:=500%Z)(K:=V293_create_rollback_pool 403%positive 11 Aemp)
 (good:=RBRFun)(vl:=RBArgs)(lg:=nil)(bf:=401%positive)(R:=RBR)
 (aop:=spec_done None)(isr:=fun _=>false)(is:=nil)(cs:=cs).
 - vm_compute;lia.
 - apply RBRGood.
 - apply RBRInv.
 - intros s H;apply RBBorrowEquivalence in H;exact H.
 - intros s H;apply RBBorrowEquivalence;exact H.
 - reflexivity.
 - apply(proj1(RBBuilders cs)).
 - apply(proj2(RBBuilders cs)).
Qed.
Definition RBReturn cs := V293_create_enabled_failure_return 403%positive 11
 (V293_create_enabled_failure_kept 401%positive Vnull Vnull(Vint32(Int.repr 4))
 (Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7))RBR Aemp)(spec_done None)(fun _=>false)nil cs.
Theorem RBCallerCheckedSameSpec : forall sd cs,
 InfRules(RBSpec cs)sd V293_witness_li RBInv(RBReturn cs)Afalse(RBInput cs)
 (sseq(V293_TaskCreateExt_TCB_call 209%Z 500%Z 101%Z 108%Z 205%Z 206%Z 207%Z 208%Z 204%Z)
  (V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z 97%Z 503%Z))Afalse RBTid.
Proof.
 intros sd cs. apply V293_OSTaskCreateExt_enabled_empty_call_suffix
 with(K:=Aemp)(good:=RBRFun).
 - lia.
 - vm_compute;lia.
 - apply RBRGood.
 - exact I.
 - vm_compute;repeat split;discriminate.
 - apply RBRInv.
 - intros s H;apply RBBorrowEquivalence in H;exact H.
 - intros s H;apply RBBorrowEquivalence;exact H.
 - reflexivity.
Qed.
Print Assumptions RBCallerLiteral.
Print Assumptions RBCalleeCheckedSameSpec.
Print Assumptions RBCallerCheckedSameSpec.
