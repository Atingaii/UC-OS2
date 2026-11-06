(* Literal parameters extend the frozen stage115 two-node fixture.
   This audit-only dependency never enters production proofs. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.audit.probes.V293TCBFreePoolProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TCBAllocatedFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFreePool.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Definition AFTop := Vptr(701%positive,Int.zero).
Definition AFBottom := Vptr(702%positive,Int.zero).
Definition AFIdentity := Vint32(Int.repr 11).
Definition AFSize := Vint32(Int.repr 64).
Definition AFOptions := Vint32 Int.zero.
Definition AFInputs := V293_tcb_allocated_inputs 208%positive 201%positive 202%positive 203%positive
 204%positive 205%positive 206%positive 207%positive 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions FPR.
Definition AFArgRows : list V293_record_cell :=
 [((201%positive,0%Z),Tint8,V293_byteval 5);((202%positive,0%Z),Tptr Tint32,AFTop);
 ((203%positive,0%Z),Tptr Tint32,AFBottom);((204%positive,0%Z),Tint16,AFIdentity);
 ((205%positive,0%Z),Tint32,AFSize);((206%positive,0%Z),Tptr Tvoid,Vnull);
 ((207%positive,0%Z),Tint16,AFOptions)].
Definition AFArgs := FPMemory AFArgRows.
Lemma AFValuesValid : V293_tcb_init_values_valid AFTop AFBottom AFIdentity AFSize Vnull AFOptions.
Proof. vm_compute;repeat split;reflexivity. Qed.
Lemma AFBindings : forall ie cs,FPState emp ie cs |=
 V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 208%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive.
Proof.
 intros. unfold V293_tcb_fields_bindings. repeat split;first[
 solve[exists 208%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 201%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 202%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 203%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 204%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 205%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 206%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 207%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]].

Qed.
Ltac AFExpand := unfold FPCaller,FPPc,FPCpu,FPCurrent,FPSentinel,FPSharedTwo,FPHeadMemory,
 FPChainMemory,FPNodeMemory,FPPayloadMemory,FPPayloadRows,V293_tcb_free_payload_cells,FPNextMemory,FPBytes;
 cbn[map FPMemory];FPOutside.
Lemma AFArgsJoin : forall M,
 (forall b off,In b [201%positive;202%positive;203%positive;204%positive;205%positive;206%positive;207%positive] -> get M(b,off)=None) ->
 join AFArgs M(merge AFArgs M).
Proof.
 intros M Missing. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 201%positive)as[E201|E201];[subst b;right;left;apply Missing;cbn;tauto| ].
 destruct(Pos.eq_dec b 202%positive)as[E202|E202];[subst b;right;left;apply Missing;cbn;tauto| ].
 destruct(Pos.eq_dec b 203%positive)as[E203|E203];[subst b;right;left;apply Missing;cbn;tauto| ].
 destruct(Pos.eq_dec b 204%positive)as[E204|E204];[subst b;right;left;apply Missing;cbn;tauto| ].
 destruct(Pos.eq_dec b 205%positive)as[E205|E205];[subst b;right;left;apply Missing;cbn;tauto| ].
 destruct(Pos.eq_dec b 206%positive)as[E206|E206];[subst b;right;left;apply Missing;cbn;tauto| ].
 destruct(Pos.eq_dec b 207%positive)as[E207|E207];[subst b;right;left;apply Missing;cbn;tauto| ].
 left. unfold AFArgs,AFArgRows;cbn[FPMemory];FPOutside.
Qed.
Ltac AFArgSpatial :=
 lazymatch goal with
 | |- FPState(merge(V293_encoded_memory ?b ?off true(encode_val ?tp ?v))?tail)?ie ?cs |= _ =>
 let bytes:=eval cbv in(Z.of_nat(typelen tp))in
 eapply FPStar with(m1:=V293_encoded_memory b off true(encode_val tp v));
 [FPApart b off bytes|split;[apply V293_encoded_memory_mapsto|reflexivity]|AFArgSpatial]
 | |- FPState emp ?ie ?cs |= _ =>apply AFBindings
 end.
Lemma AFArgsSpatial : forall ie cs,FPState AFArgs ie cs |=
 V293_rdy_raw_cells AFArgRows
 (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 208%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive).
Proof.
 intros. unfold AFArgs,AFArgRows. cbn[FPMemory V293_rdy_raw_cells]. AFArgSpatial.
Qed.
Lemma AFWholeJoin : forall pc cpu,
 join AFArgs(merge(FPCaller pc cpu)FPSharedTwo)(merge AFArgs(merge(FPCaller pc cpu)FPSharedTwo)).
Proof.
 intros. apply AFArgsJoin. intros b off Member. cbn in Member.
 repeat destruct Member as[Member|Member];try contradiction;subst b;AFExpand.
Qed.
Definition AFPopInput := merge AFArgs FPPopInput.
Definition AFCritical cs := V293_tcb_free_critical 401%positive 208%positive 209%positive
 FPHead(Vint32 Int.zero)FPHead Aemp AFInputs(spec_done None)(fun _=>false)nil(true::cs).
Theorem AFActualPopInput : forall cs,FPState AFPopInput false(true::cs) |= AFCritical cs.
Proof.
 intro cs. assert(H:FPState AFPopInput false(true::cs) |=
 V293_rdy_raw_cells AFArgRows
 (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 208%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive) **
 V293_tcb_free_critical 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)FPHead Aemp FPR
 (spec_done None)(fun _=>false)nil(true::cs)).
 { eapply FPStar;[apply AFWholeJoin|apply AFArgsSpatial|apply FPActualPopInput]. }
 unfold AFCritical,AFInputs,V293_tcb_allocated_inputs,V293_tcb_free_critical,V293_tcb_enabled_resources in *.
 cbn[AFArgRows V293_rdy_raw_cells]in H|-*. clear -H;sep auto.
Qed.
Theorem AFPopFieldsChecked : forall sd r ri cs,
 InfRules(fun _=>None)sd V293_witness_li FPInv r ri(AFCritical cs)
 (sseq(V293_TCBInit_pop 91%Z 108%Z)(sseq(sprim excrit)
 (V293_TCBInit_fields 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z)))
 (EX next:val,[|(Int.unsigned Int.zero+55<=Int.max_unsigned)%Z /\ rule_type_val_match(Tcom_ptr 410%Z)next=true|] **
 V293_tcb_enabled_state 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)
 (V293_tcb_allocated_initialized 501%positive Int.zero next 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions ** AFInputs)
 (spec_done None)(fun _=>false)nil cs)FPTid.
Proof.
 intros. apply V293_tcb_free_pop_fields;[lia|apply FPRGood|apply AFValuesValid|apply FPRCurLINV| ].
 intros s H. apply FPBorrowEquivalence. unfold FPCore. clear -H;sep auto.
Qed.
Definition AFPrivateBase := merge(FPCaller FPHead(Vint32 Int.zero))(FPNodeMemory 501%positive FPNext).
Definition AFFieldsInput := merge AFArgs AFPrivateBase.
Lemma AFPrivateJoin : join AFArgs AFPrivateBase AFFieldsInput.
Proof.
 apply AFArgsJoin. intros b off Member. cbn in Member.
 repeat destruct Member as[Member|Member];try contradiction;subst b;unfold AFPrivateBase;AFExpand.
Qed.
Lemma AFCallerNodeJoin : join(FPCaller FPHead(Vint32 Int.zero))(FPNodeMemory 501%positive FPNext)AFPrivateBase.
Proof.
 apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 501%positive);[subst b;left|right;left];AFExpand.
Qed.
Theorem AFPrivateFieldsSpatial : forall cs,FPState AFFieldsInput true cs |=
 V293_tcb_enabled_state 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)
 (V293_tcb_free_node 501%positive Int.zero FPNext ** AFInputs)(spec_done None)(fun _=>false)nil cs.
Proof.
 intro cs. assert(B:FPState AFPrivateBase true cs |=
 V293_tcb_enabled_resources 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)FPR **
 V293_tcb_free_node 501%positive Int.zero FPNext).
 { eapply FPStar;[apply AFCallerNodeJoin|apply FPCallerSpatial|apply FPNodeSpatial]. }
 assert(H:FPState AFFieldsInput true cs |=
 V293_rdy_raw_cells AFArgRows
 (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 208%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive) **
 (V293_tcb_enabled_resources 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)FPR **
 V293_tcb_free_node 501%positive Int.zero FPNext)).
 { eapply FPStar;[apply AFPrivateJoin|apply AFArgsSpatial|exact B]. }
 assert(O:FPState AFFieldsInput true cs |=
 Aisr(fun _=>false) ** Aie true ** Ais nil ** Acs cs **
 (V293_rdy_raw_cells AFArgRows
 (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 208%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive) **
 (V293_tcb_enabled_resources 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)FPR **
 V293_tcb_free_node 501%positive Int.zero FPNext))).
 { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
   apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[ |reflexivity]. exact H. }
 unfold V293_tcb_enabled_state. apply astar_l_aop'_intro;[ |reflexivity].
 unfold AFInputs,V293_tcb_allocated_inputs,V293_tcb_enabled_resources in *.
 cbn[AFArgRows V293_rdy_raw_cells]in O|-*. clear -O;sep auto.
Qed.

Definition AFEnabledCaller := merge AFArgs(FPCaller Vundef(Vint32(Int.repr 99))).
Lemma AFCallerNoShared : forall b off,
 b=401%positive \/ b=501%positive \/ b=502%positive -> get AFEnabledCaller(b,off)=None.
Proof.
 intros b off B. assert(N:get AFArgs(b,off)=None).
 { destruct B as[E|[E|E]];subst b;unfold AFArgs,AFArgRows;cbn[FPMemory];FPOutside. }
 unfold AFEnabledCaller. rewrite map_merge_semp by reflexivity. rewrite N.
 rewrite FPCallerNoShared by exact B. reflexivity.
Qed.
Theorem AFWholeEnabledLiteral : forall cs,
 FPState(merge AFArgs(merge(FPCaller Vundef(Vint32(Int.repr 99)))FPSharedTwo))true cs |=
 V293_tcb_enabled_state 401%positive 208%positive 209%positive Vundef(Vint32(Int.repr 99))AFInputs
 (spec_done None)(fun _=>false)nil cs ** invlth_isr FPInv 0 INUM.
Proof.
 intro cs. assert(H:FPState(merge AFArgs(merge(FPCaller Vundef(Vint32(Int.repr 99)))FPSharedTwo))true cs |=
 V293_rdy_raw_cells AFArgRows
 (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 208%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive) **
 (V293_tcb_enabled_state 401%positive 208%positive 209%positive Vundef(Vint32(Int.repr 99))FPR
 (spec_done None)(fun _=>false)nil cs ** invlth_isr FPInv 0 INUM)).
 { eapply FPStar;[apply AFWholeJoin|apply AFArgsSpatial|apply FPWholeEnabledLiteral with(present:=true)]. }
 unfold AFInputs,V293_tcb_allocated_inputs,V293_tcb_enabled_state,V293_tcb_enabled_resources in *.
 cbn[AFArgRows V293_rdy_raw_cells]in H|-*. clear -H;sep auto.
Qed.
Theorem AFPrivateNoSharedHead : forall off,get AFFieldsInput(401%positive,off)=None.
Proof.
 intro off. unfold AFFieldsInput,AFPrivateBase,AFArgs,AFArgRows;cbn[FPMemory];AFExpand.
Qed.

(* Known literal bytes, rather than existential storage, witness old priority 0. *)
Ltac AFRawPayload :=
 lazymatch goal with
 | |- FPState(merge(V293_encoded_memory ?b ?off true(encode_val ?tp ?v))?tail)?ie ?cs |= _ =>
 let bytes:=eval cbv in(Z.of_nat(typelen tp))in
 eapply FPStar with(m1:=V293_encoded_memory b off true(encode_val tp v));
 [FPApart b off bytes|split;[apply V293_encoded_memory_mapsto|reflexivity]|AFRawPayload]
 | |- FPState emp _ _ |= Aemp =>split;reflexivity
 end.
Lemma AFPayloadRawSpatial : forall b ie cs,
 FPState(FPPayloadMemory b)ie cs |= V293_rdy_raw_cells(FPPayloadRows b)Aemp.
Proof.
 intros. unfold FPPayloadMemory,FPPayloadRows,V293_tcb_free_payload_cells.
 cbn[map FPMemory V293_rdy_raw_cells]. AFRawPayload.
Qed.
Lemma AFNodeRawSpatial : forall b next ie cs,
 FPState(FPNodeMemory b next)ie cs |=
 V293_rdy_raw_cells(FPPayloadRows b)Aemp ** Amapsto(b,20%Z)(Tcom_ptr 410%Z)true next.
Proof.
 intros. unfold FPNodeMemory. eapply FPStar with(m1:=FPPayloadMemory b)(m2:=FPNextMemory b next).
 - unfold FPNextMemory,FPPayloadMemory,FPPayloadRows,V293_tcb_free_payload_cells.
   cbn[map FPMemory]. apply map_join_merge;apply map_disjoint;intros[other off].
   destruct(Pos.eq_dec other b)as[B|B];[subst other|left;FPOutside].
   destruct(Z_lt_dec off 20)as[Low|Low];[right;left;FPOutside| ].
   destruct(Z_lt_dec off 24)as[Inside|Outside];[left;FPOutside|right;left;FPOutside].
 - apply AFPayloadRawSpatial.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma AFKnownPrioritySpatial :
 FPState AFFieldsInput true nil |= Amapsto(501%positive,50%Z)Tint8 true(V293_byteval 0) ** Atrue.
Proof.
 assert(B:FPState AFPrivateBase true nil |=
 V293_tcb_enabled_resources 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)FPR **
 (V293_rdy_raw_cells(FPPayloadRows 501%positive)Aemp ** Amapsto(501%positive,20%Z)(Tcom_ptr 410%Z)true FPNext)).
 { eapply FPStar;[apply AFCallerNodeJoin|apply FPCallerSpatial|apply AFNodeRawSpatial]. }
 assert(H:FPState AFFieldsInput true nil |=
 V293_rdy_raw_cells AFArgRows
 (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 208%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive) **
 (V293_tcb_enabled_resources 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)FPR **
 (V293_rdy_raw_cells(FPPayloadRows 501%positive)Aemp ** Amapsto(501%positive,20%Z)(Tcom_ptr 410%Z)true FPNext))).
 { eapply FPStar;[apply AFPrivateJoin|apply AFArgsSpatial|exact B]. }
 unfold FPPayloadRows,V293_tcb_free_payload_cells in H.
 cbn[map FPDefault V293_rdy_raw_cells]in H. change(V293_byteval 0)with(Vint32 Int.zero).
 clear -H;sep auto.
Qed.
Lemma AFPrioritySplit : exists M1 M2,
 mapstoval(501%positive,50%Z)Tint8 true(V293_byteval 0)M1 /\ join M1 M2 AFFieldsInput.
Proof.
 pose proof AFKnownPrioritySpatial as H. apply sat_split in H.
 destruct H as(m1&m2&o1&o2&JM&JO&HM&HQ). exists m1. exists m2.
 split;[exact(proj1 HM)|exact JM].
Qed.
Lemma AFActualPriorityRead : load Tint8 AFFieldsInput(501%positive,50%Z)=Some(V293_byteval 0).
Proof.
 destruct AFPrioritySplit as(m1&m2&HM&J).
 eapply FPLoadJoin;[exact J|eapply mapstoval_load;[reflexivity|exact HM]].
Qed.
Lemma AFInputPriorityRead : load Tint8 AFFieldsInput(201%positive,0%Z)=Some(V293_byteval 5).
Proof.
 assert(H:FPState AFFieldsInput true nil |= Amapsto(201%positive,0%Z)Tint8 true(V293_byteval 5) ** Atrue).
 { pose proof(AFPrivateFieldsSpatial nil)as H.
   unfold V293_tcb_enabled_state,V293_tcb_enabled_resources,AFInputs,V293_tcb_allocated_inputs in H.
   cbn[V293_rdy_raw_cells]in H. clear -H;sep auto. }
 apply sat_split in H. destruct H as(m1&m2&o1&o2&JM&JO&HM&HQ).
 eapply FPLoadJoin;[exact JM|eapply mapstoval_load;[reflexivity|exact(proj1 HM)]].
Qed.
Definition AFPriorityWrite := store Tint8 AFFieldsInput(501%positive,50%Z)(V293_byteval 5).
Lemma AFWrittenPriorityRead :
 (match AFPriorityWrite with Some M=>load Tint8 M(501%positive,50%Z)|None=>None end)=Some(V293_byteval 5).
Proof.
 destruct AFPrioritySplit as(m1&m2&HM&J).
 destruct(@store_exist_join' (501%positive,50%Z)Tint8(V293_byteval 0)(V293_byteval 5)m1 m2 AFFieldsInput HM J)as(M'&S).
 unfold AFPriorityWrite. rewrite S.
 destruct(@store_mapstoval_frame1 m1 m2 AFFieldsInput M' (501%positive,50%Z)Tint8
 (V293_byteval 0)(V293_byteval 5)HM J S)as(m1'&HM'&S'&J').
 eapply FPLoadJoin;[exact J'|eapply mapstoval_load;[reflexivity|exact HM']].
Qed.
Theorem AFOmittedPriorityDiffers : load Tint8 AFFieldsInput(501%positive,50%Z)<>Some(V293_byteval 5).
Proof. rewrite AFActualPriorityRead. discriminate. Qed.
Print Assumptions AFPopFieldsChecked.
Print Assumptions AFPrivateFieldsSpatial.
Print Assumptions AFWholeEnabledLiteral.
Print Assumptions AFOmittedPriorityDiffers.
