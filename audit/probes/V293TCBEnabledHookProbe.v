(* Audit fixtures only. Same frozen FPInv, real caller locals and private node. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.audit.probes.V293TCBFreePoolProbe.
Require Import CertiOS.audit.probes.V293TCBAllocatedFieldsProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEnabledHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBAllocatedFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFreePool.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Lemma EHGoodR : GoodFunAsrt FPR.
Proof. cbn[FPR CurTid LINV V293_witness_li GoodFunAsrt]. repeat split;exact I. Qed.
Definition EHPre cs := V293_tcb_enabled_hook_fpre 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions
 FPR(spec_done None)(fun _=>false)nil cs FPTid EHGoodR.
Definition EHPost cs := V293_tcb_enabled_hook_fpost 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions
 FPR(spec_done None)(fun _=>false)nil cs FPTid EHGoodR.
Definition EHSpec cs : funspec := fun f=>if Z.eq_dec f 990%Z then
 Some(EHPre cs,EHPost cs,(Tvoid,[Tptr V293_tcb_type]))else None.
Definition EHState b off next cs :=
 V293_tcb_enabled_state 401%positive 208%positive 209%positive(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_initialized b off next 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions ** AFInputs)
 (spec_done None)(fun _=>false)nil cs.
Lemma EHLookup : forall cs,EHSpec cs 990%Z=Some(EHPre cs,EHPost cs,(Tvoid,[Tptr V293_tcb_type])).
Proof. intro;reflexivity. Qed.
Theorem EHCallChecked : forall sd r ri b off next cs,
 InfRules(EHSpec cs)sd V293_witness_li FPInv r ri(EHState b off next cs)
 (scall 990%Z[evar 108%Z])(EHState b off next cs)FPTid.
Proof. intros. apply V293_tcb_enabled_hook_call with(good:=EHGoodR);[apply FPRCurLINV|apply EHLookup]. Qed.
Theorem EHFieldsCallChecked : forall sd r ri cs,
 InfRules(EHSpec cs)sd V293_witness_li FPInv r ri
 (V293_tcb_enabled_state 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)
 (V293_tcb_free_node 501%positive Int.zero FPNext ** AFInputs)(spec_done None)(fun _=>false)nil cs)
 (sseq(V293_TCBInit_fields 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z)(scall 990%Z[evar 108%Z]))
 (EHState 501%positive Int.zero FPNext cs)FPTid.
Proof.
 intros. apply V293_tcb_allocated_fields_first_hook with(good:=EHGoodR);
 [lia|vm_compute;discriminate|apply AFValuesValid|apply FPRCurLINV|apply EHLookup].
Qed.
Theorem EHFieldsCallLiteralInput : forall cs,FPState AFFieldsInput true cs |=
 V293_tcb_enabled_state 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)
 (V293_tcb_free_node 501%positive Int.zero FPNext ** AFInputs)(spec_done None)(fun _=>false)nil cs.
Proof. apply AFPrivateFieldsSpatial. Qed.
Definition EHExtraRows :=
 [((501%positive,24%Z),Tcom_ptr 410%Z,Vnull);((501%positive,40%Z),Tint16,Vint32 Int.zero);
 ((501%positive,42%Z),Tint8,Vint32 Int.zero);((501%positive,43%Z),Tint8,Vint32 Int.zero);
 ((501%positive,20%Z),Tcom_ptr 410%Z,FPNext)].
Definition EHRows := V293_tcb_init_final_fields 501%positive 0 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions ++ EHExtraRows.
Definition EHNode := FPMemory EHRows.
Lemma EHNodeRaw : forall ie cs,FPState EHNode ie cs |= V293_rdy_raw_cells EHRows Aemp.
Proof.
 intros. unfold EHNode,EHRows,V293_tcb_init_final_fields,EHExtraRows.
 cbn[app FPMemory V293_rdy_raw_cells]. AFRawPayload.
Qed.
Lemma EHNodeSpatial : forall ie cs,FPState EHNode ie cs |=
 V293_tcb_allocated_initialized 501%positive Int.zero FPNext 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions.
Proof.
 intros. pose proof(EHNodeRaw ie cs)as H.
 unfold V293_tcb_allocated_initialized,V293_tcb_allocated_remainder,V293_tcb_allocated_spares,EHRows,EHExtraRows in *.
 rewrite V293_raw_cells_append in H.
 eapply V293_raw_cells_mono;[ |exact H]. intros s HS.
 cbn[V293_rdy_raw_cells V293_storage V293_storage_cell]in HS|-*.
 unfold V293_storage_cell. sep normal. exists Vnull. exists(Vint32 Int.zero). exists(Vint32 Int.zero). exists(Vint32 Int.zero).
 clear -HS;sep auto.
Qed.
Definition EHPrivate := merge(FPCaller FPHead(Vint32 Int.zero))EHNode.
Definition EHInput := merge AFArgs EHPrivate.
Ltac EHExpand := unfold EHPrivate,EHNode,EHRows,EHExtraRows,V293_tcb_init_final_fields;
 cbn[app FPMemory];AFExpand.
Lemma EHCallerNodeJoin : join(FPCaller FPHead(Vint32 Int.zero))EHNode EHPrivate.
Proof.
 apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 501%positive);[subst b;left|right;left];EHExpand.
Qed.
Lemma EHArgsJoin : join AFArgs EHPrivate EHInput.
Proof.
 apply AFArgsJoin. intros b off Member. cbn in Member.
 repeat destruct Member as[Member|Member];try contradiction;subst b;EHExpand.
Qed.
Theorem EHLiteralHookInput : forall cs,FPState EHInput true cs |= EHState 501%positive Int.zero FPNext cs.
Proof.
 intro cs. assert(B:FPState EHPrivate true cs |=
 V293_tcb_enabled_resources 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)FPR **
 V293_tcb_allocated_initialized 501%positive Int.zero FPNext 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions).
 { eapply FPStar;[apply EHCallerNodeJoin|apply FPCallerSpatial|apply EHNodeSpatial]. }
 assert(H:FPState EHInput true cs |=
 V293_rdy_raw_cells AFArgRows
 (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 208%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive) **
 (V293_tcb_enabled_resources 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)FPR **
 V293_tcb_allocated_initialized 501%positive Int.zero FPNext 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions)).
 { eapply FPStar;[apply EHArgsJoin|apply AFArgsSpatial|exact B]. }
 assert(O:FPState EHInput true cs |= Aisr(fun _=>false) ** Aie true ** Ais nil ** Acs cs **
 (V293_rdy_raw_cells AFArgRows
 (V293_tcb_fields_bindings 108%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 107%Z
 208%positive 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive) **
 (V293_tcb_enabled_resources 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)FPR **
 V293_tcb_allocated_initialized 501%positive Int.zero FPNext 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions))).
 { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
   apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[ |reflexivity]. exact H. }
 unfold EHState,V293_tcb_enabled_state. apply astar_l_aop'_intro;[ |reflexivity].
 unfold AFInputs,V293_tcb_allocated_inputs,V293_tcb_enabled_resources in *.
 cbn[AFArgRows V293_rdy_raw_cells]in O|-*. clear -O;sep auto.
Qed.
Theorem EHActualArgument : forall cs,FPState EHInput true cs |=
 Rvl[evar 108%Z] @ [Tptr V293_tcb_type] == [FPHead].
Proof. intro cs. eapply V293_tcb_enabled_hook_argument with(bf:=401%positive)(bc:=209%positive)
 (R:=V293_tcb_allocated_initialized 501%positive Int.zero FPNext 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions ** AFInputs).
 apply EHLiteralHookInput. Qed.
Theorem EHSeparatedCallInput : forall cs,FPState EHInput true cs |=
 getasrt(EHPre cs ([FPHead]) ([logic_val FPHead;logic_val FPNext]) FPTid) **
 V293_tcb_enabled_hook_frame 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive
 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions.
Proof.
 intro cs. pose proof(EHLiteralHookInput cs)as H.
 apply V293_tcb_enabled_hook_view in H.
 cbn[EHPre V293_tcb_enabled_hook_fpre FPHead V293_hook_fpre getasrt]. clear -H;sep auto.
Qed.
Theorem EHPrivateNoShared : forall b off,b=401%positive \/ b=502%positive -> get EHInput(b,off)=None.
Proof.
 intros b off[B|B];subst b;unfold EHInput,AFArgs,AFArgRows;cbn[FPMemory];EHExpand.
Qed.
Lemma EHJoinTail : join EHInput FPSharedOne(merge EHInput FPSharedOne).
Proof.
 apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 401%positive);[subst b;left;apply EHPrivateNoShared;auto| ].
 destruct(Pos.eq_dec b 502%positive);[subst b;left;apply EHPrivateNoShared;auto| ].
 right;left. unfold FPSharedOne,FPHeadMemory;AFExpand.
Qed.
Theorem EHLiteralSameInvariantTail : forall cs,
 FPState(merge EHInput FPSharedOne)true cs |= EHState 501%positive Int.zero FPNext cs ** invlth_isr FPInv 0 INUM.
Proof.
 intro cs. eapply FPStar;[apply EHJoinTail|apply EHLiteralHookInput| ].
 apply FPSameInvariantChangedTail.
Qed.

(* Exact contract discrimination on the SAME satisfiable physical input.
   These are boundary checks, not execution or implementation of a CPU Hook. *)
Definition EHAdmits vl result owner : Prop := FPState EHInput true nil |=
 getasrt(EHPost nil vl result ([logic_val FPHead;logic_val FPNext]) owner) ** Atrue.
Theorem EHAdmitsExact : forall vl result owner,
 EHAdmits vl result owner <-> vl=[FPHead] /\ owner=FPTid /\ result=None.
Proof.
 intros vl result owner. unfold EHAdmits. cbn[EHPost V293_tcb_enabled_hook_fpost FPHead V293_hook_fpost getasrt].
 split;intro H.
 - assert(P:FPState EHInput true nil |= [|vl=[Vptr(501%positive,Int.zero)] /\ owner=FPTid /\ result=None|] ** Atrue)
   by(clear -H;sep auto).
   apply astar_l_apure_elim in P. exact(proj1 P).
 - pose proof(EHLiteralHookInput nil)as S. apply V293_tcb_enabled_hook_view in S.
   clear -S H;sep auto.
Qed.
Theorem EHAdmitsNone : EHAdmits ([FPHead]) None FPTid.
Proof. apply EHAdmitsExact. auto. Qed.
Theorem EHWrongPointerRejected : ~EHAdmits ([FPNext]) None FPTid.
Proof. intro H;apply EHAdmitsExact in H. destruct H as[H _]. discriminate H. Qed.
Theorem EHWrongOwnerRejected : ~EHAdmits ([FPHead]) None(302%positive,Int.zero).
Proof. intro H;apply EHAdmitsExact in H. destruct H as[_[H _]]. discriminate H. Qed.
Theorem EHWrongResultRejected : ~EHAdmits ([FPHead])(Some(Vint32 Int.zero))FPTid.
Proof. intro H;apply EHAdmitsExact in H. destruct H as[_[_ H]]. discriminate H. Qed.
Theorem EHMalformedLogicRejected : forall s,
 ~s |= getasrt(EHPre nil ([FPHead]) [] FPTid).
Proof. intros s H;exact H. Qed.
Print Assumptions EHLiteralSameInvariantTail.
Print Assumptions EHFieldsCallChecked.
Print Assumptions EHAdmitsExact.
