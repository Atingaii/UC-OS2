(* Audit-only nonempty full-view fixture. Global92 really exists; all seven
   parameters, both locals, initialized node and a caller sentinel are bytes. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.audit.probes.V293TCBFreePoolProbe.
Require Import CertiOS.audit.probes.V293TCBAllocatedFieldsProbe.
Require Import CertiOS.audit.probes.V293TCBEnabledHookProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFullPriority.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TCBOwnedPriority.
Require Import CertiOS.certiucos.v293.proofs.V293TCBAllocatedFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReservationOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Definition TFGE : env := set FPGE 92%Z(403%positive,Tarray(Tptr V293_tcb_type)13).
Definition TFState M ie cs : RstateOP :=
 (TFGE,FPLE,M,(fun _=>false),(ie,[],cs),(emp:osabst),spec_done None).
Definition TFLocalRows := AFArgRows ++
 [((208%positive,0%Z),Tptr V293_tcb_type,FPHead);((209%positive,0%Z),Tint32,Vint32 Int.zero)].
Definition TFLocals := FPMemory TFLocalRows.
Definition TFRMemory := merge FPCurrent FPSentinel.
Definition TFPrivate := merge EHNode TFRMemory.
Definition TFInput := merge TFLocals TFPrivate.
Definition TFNode := V293_tcb_allocated_initialized 501%positive Int.zero FPNext 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions.
Definition TFFull R cs :=
 V293_tcb_enabled_state 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)
 (TFNode ** V293_tcb_allocated_inputs 208%positive 201%positive 202%positive 203%positive
 204%positive 205%positive 206%positive 207%positive 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions
 (V293_tcb_table_binding 403%positive ** R))(spec_done None)(fun _=>false)nil cs.
Definition TFPriority R cs :=
 V293_tcb_priority_state 403%positive 201%positive 208%positive 5 FPHead
 (TFNode ** (R ** V293_tcb_priority_caller_frame 401%positive 208%positive 209%positive
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive
 (Vint32 Int.zero)AFTop AFBottom AFIdentity AFSize Vnull AFOptions))(spec_done None)(fun _=>false)true nil cs.
Lemma TFStar : forall m1 m2 m ie cs p q,
 join m1 m2 m -> TFState m1 ie cs |= p -> TFState m2 ie cs |= q -> TFState m ie cs |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2. exists(emp:osabst). exists(emp:osabst).
 split;[exact H| ]. split;[apply map_join_emp| ]. split;assumption.
Qed.
Ltac TFRaw :=
 lazymatch goal with
 | |- TFState(merge(V293_encoded_memory ?b ?off true(encode_val ?tp ?v))?tail)?ie ?cs |= _ =>
 let bytes:=eval cbv in(Z.of_nat(typelen tp))in
 eapply TFStar with(m1:=V293_encoded_memory b off true(encode_val tp v));
 [FPApart b off bytes|split;[apply V293_encoded_memory_mapsto|reflexivity]|TFRaw]
 | |- TFState emp _ _ |= Aemp =>split;reflexivity
 end.
Lemma TFLocalSpatial : forall ie cs,TFState TFLocals ie cs |= V293_rdy_raw_cells TFLocalRows Aemp.
Proof. intros. unfold TFLocals,TFLocalRows,AFArgRows. cbn[app FPMemory V293_rdy_raw_cells]. TFRaw. Qed.
Lemma TFNodeSpatial : forall ie cs,TFState EHNode ie cs |= TFNode.
Proof.
 intros. assert(H:TFState EHNode ie cs |= V293_rdy_raw_cells EHRows Aemp).
 { unfold EHNode,EHRows,V293_tcb_init_final_fields,EHExtraRows. cbn[app FPMemory V293_rdy_raw_cells]. TFRaw. }
 unfold TFNode,V293_tcb_allocated_initialized,V293_tcb_allocated_remainder,V293_tcb_allocated_spares,EHRows,EHExtraRows in *.
 rewrite V293_raw_cells_append in H. eapply V293_raw_cells_mono;[ |exact H]. intros s HS.
 cbn[V293_rdy_raw_cells V293_storage V293_storage_cell]in HS|-*.
 unfold V293_storage_cell. sep normal. exists Vnull. exists(Vint32 Int.zero). exists(Vint32 Int.zero). exists(Vint32 Int.zero).
 clear -HS;sep auto.
Qed.
Lemma TFRSpatial : forall ie cs,TFState TFRMemory ie cs |= FPR.
Proof.
 intros. unfold TFRMemory,FPR.
 eapply TFStar with(m1:=FPCurrent)(m2:=FPSentinel).
 - FPRapart 402%positive.
 - exists Tvoid. exists 402%positive. eapply TFStar with(m1:=emp)(m2:=FPCurrent).
   + apply map_join_comm;apply map_join_emp.
   + exists 402%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply TFStar with(m1:=emp)(m2:=FPSentinel);[apply map_join_comm;apply map_join_emp| | ].
   + unfold LINV. apply astar_comm. apply astar_l_apure_intro;[split;reflexivity|apply V293_witness_li_good].
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Definition TFBindings :=
 V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 208%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive **
 V293_tcb_empty_bindings 401%positive 208%positive 209%positive ** V293_tcb_table_binding 403%positive.
Ltac TFLocalBinding := repeat split;first[
 solve[exists 208%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 201%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 202%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 203%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 204%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 205%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 206%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 207%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]].
Lemma TFBindingsSpatial : forall ie cs,TFState emp ie cs |= TFBindings.
Proof.
 intros. unfold TFBindings. eapply TFStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 - unfold V293_tcb_fields_bindings;TFLocalBinding.
 - eapply TFStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
   + unfold V293_tcb_empty_bindings. split.
     * exists 208%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
     * split.
       -- exists 209%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
       -- split.
          ++ exists 401%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
          ++ split;[intros[v H];vm_compute in H;discriminate|split;reflexivity].
   + unfold V293_tcb_table_binding. split.
     * exists 403%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
     * split;[intros[v H];vm_compute in H;discriminate|split;reflexivity].
Qed.
Ltac TFExpand := unfold TFInput,TFLocals,TFLocalRows,AFArgRows,TFPrivate,TFRMemory,EHNode,EHRows,EHExtraRows,V293_tcb_init_final_fields;
 cbn[app FPMemory];AFExpand.
Lemma TFPrivateJoin : join EHNode TFRMemory TFPrivate.
Proof.
 apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 501%positive);[subst b;right;left|left];TFExpand.
Qed.
Lemma TFInputJoin : join TFLocals TFPrivate TFInput.
Proof.
 apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 501%positive);[subst b;left| ].
 - TFExpand.
 - destruct(Pos.eq_dec b 402%positive);[subst b;left| ].
   + TFExpand.
   + destruct(Pos.eq_dec b 601%positive);[subst b;left|right;left];TFExpand.
Qed.
Lemma TFLiteralFull : forall cs,TFState TFInput true cs |= TFFull FPR cs.
Proof.
 intro cs. assert(B:TFState TFPrivate true cs |= TFNode ** FPR).
 { eapply TFStar;[apply TFPrivateJoin|apply TFNodeSpatial|apply TFRSpatial]. }
 assert(C:TFState TFInput true cs |= V293_rdy_raw_cells TFLocalRows Aemp **(TFNode ** FPR)).
 { eapply TFStar;[apply TFInputJoin|apply TFLocalSpatial|exact B]. }
 assert(D:TFState TFInput true cs |= TFBindings ** (V293_rdy_raw_cells TFLocalRows Aemp **(TFNode ** FPR))).
 { eapply TFStar with(m1:=emp)(m2:=TFInput);[apply map_join_comm;apply map_join_emp|apply TFBindingsSpatial|exact C]. }
 apply astar_l_aop'_intro with(aop:=spec_done None)in D;[ |reflexivity].
 apply astar_l_aisr_intro with(i:=fun _=>false)in D;[ |reflexivity].
 apply astar_l_aie_intro with(i:=true)in D;[ |reflexivity].
 apply astar_l_ais_intro with(i:=nil)in D;[ |reflexivity].
 apply astar_l_acs_intro with(i:=cs)in D;[ |reflexivity].
 unfold TFFull,V293_tcb_enabled_state,V293_tcb_enabled_resources,V293_tcb_allocated_inputs,TFBindings in *.
 cbn[TFLocalRows AFArgRows app V293_rdy_raw_cells]in *;clear -D;sep auto.
Qed.
Theorem TFLiteralPriority : forall cs,TFState TFInput true cs |= TFPriority FPR cs.
Proof. intro cs. apply V293_tcb_full_priority_view. apply TFLiteralFull. Qed.
Theorem TFLiteralRestore : forall cs,TFState TFInput true cs |= TFFull FPR cs.
Proof. intro cs. apply V293_tcb_full_priority_restore. apply TFLiteralPriority. Qed.
Theorem TFActualArgument : forall cs,TFState TFInput true cs |=
 Rvl[evar 108%Z] @ [Tptr V293_tcb_type] == [FPHead].
Proof. intro cs. eapply V293_tcb_priority_argument. apply TFLiteralPriority. Qed.
Theorem TFFixtureFresh : forall cs,TFState TFInput true cs |= TFFull FPR cs ->
 (501%positive,Int.zero)<>(405%positive,Int.zero).
Proof. intros;discriminate. Qed.
Lemma TFActualPriorityRead : load Tint8 TFInput(201%positive,0%Z)=Some(V293_byteval 5).
Proof.
 change(load Tint8(getmem(TFState TFInput true nil))(201%positive,0%Z)=Some(V293_byteval 5)).
 pose proof(TFLiteralPriority nil)as H. unfold TFPriority,V293_tcb_priority_state in H.
 eapply V293_star_load_r;[ |exact H]. intros st HS.
 eapply V293_star_load_r;[ |exact HS]. intros st1 H1.
 unfold V293_tcb_priority_resources in H1.
 destruct st1 as [[[[[[ge le] M] irq] aux] O] op].
 V293_tcb_init_read H1 0%nat Load. exact Load.
Qed.
Definition TFObserve (shadow:bool) := evaladdr(earrayelem(evar 92%Z)(evar 101%Z))
 (TFGE,(if shadow then set FPLE 92%Z(777%positive,Tint8)else FPLE),TFInput).
Theorem TFGlobalAddress : TFObserve false=Some(Vptr(403%positive,Int.repr 20)).
Proof.
 exact(proj2(V293_rekey_array_address TFGE FPLE TFInput 92%Z 101%Z V293_tcb_type
 403%positive 201%positive 5 ltac:(vm_compute;reflexivity)ltac:(vm_compute;reflexivity)
 ltac:(vm_compute;reflexivity)TFActualPriorityRead ltac:(lia))).
Qed.
Theorem TFShadowAddress : TFObserve true=None.
Proof.
 cbn[TFObserve evaladdr evaltype evalval get_lenv get_genv get_mem]. reflexivity.
Qed.
Theorem TFShadowDiffers : TFObserve true<>TFObserve false.
Proof. rewrite TFGlobalAddress,TFShadowAddress;discriminate. Qed.

Definition TFReserved : addrval := (405%positive,Int.zero).
Definition TFShareMemory := V293_encoded_memory 403%positive 20 false
 (encode_val(Tptr V293_tcb_type)(Vptr TFReserved)).
Definition TFOwnedInput := merge TFInput TFShareMemory.
Lemma TFShareJoin : join TFInput TFShareMemory TFOwnedInput.
Proof.
 apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 403%positive);[subst b;left;TFExpand|right;left].
 unfold TFShareMemory;apply V293_encoded_memory_outside;left;congruence.
Qed.
Theorem TFOwnedLiteral : forall cs,TFState TFOwnedInput true cs |=
 TFFull(V293_create_owned_share 403%positive TFReserved 5 ** FPR)cs.
Proof.
 intro cs. assert(H:TFState TFOwnedInput true cs |= TFFull FPR cs ** V293_create_owned_share 403%positive TFReserved 5).
 { eapply TFStar;[apply TFShareJoin|apply TFLiteralFull| ].
   unfold V293_create_owned_share,V293_reservation_owner,TFShareMemory.
   split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 unfold TFFull,V293_tcb_enabled_state,V293_tcb_enabled_resources,V293_tcb_allocated_inputs in *.
 cbn[V293_rdy_raw_cells]in *;clear -H;sep auto.
Qed.
Theorem TFOwnedPriorityLiteral : forall cs,TFState TFOwnedInput true cs |=
 TFPriority(V293_create_owned_share 403%positive TFReserved 5 ** FPR)cs.
Proof. intro cs. apply V293_tcb_full_priority_view;apply TFOwnedLiteral. Qed.
Theorem TFOwnedRestore : forall cs,TFState TFOwnedInput true cs |=
 TFFull(V293_create_owned_share 403%positive TFReserved 5 ** FPR)cs.
Proof. intro cs. apply V293_tcb_full_priority_restore;apply TFOwnedPriorityLiteral. Qed.
