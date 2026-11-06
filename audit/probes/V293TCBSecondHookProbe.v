(* Audit-only second-call and allocator-freshness boundary fixtures. *)
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
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Require Import CertiOS.audit.probes.V293TCBFullPriorityProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSecondHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEnabledHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.

Definition TSShareMemory token := V293_encoded_memory 403%positive 20 false
 (encode_val(Tptr V293_tcb_type)(Vptr token)).
Definition TSOwnedInput token := merge TFInput(TSShareMemory token).
Lemma TSShareJoin : forall token,join TFInput(TSShareMemory token)(TSOwnedInput token).
Proof.
 intro token. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 403%positive);[subst b;left;TFExpand|right;left].
 unfold TSShareMemory;apply V293_encoded_memory_outside;left;congruence.
Qed.
Theorem TSOwnedLiteral : forall token cs,TFState(TSOwnedInput token)true cs |=
 TFFull(V293_create_owned_share 403%positive token 5 ** FPR)cs.
Proof.
 intros token cs. assert(H:TFState(TSOwnedInput token)true cs |= TFFull FPR cs ** V293_create_owned_share 403%positive token 5).
 { eapply TFStar;[apply TSShareJoin|apply TFLiteralFull| ].
   unfold V293_create_owned_share,V293_reservation_owner,TSShareMemory.
   split;[apply V293_encoded_memory_mapsto|reflexivity]. }
 unfold TFFull,V293_tcb_enabled_state,V293_tcb_enabled_resources,V293_tcb_allocated_inputs in *.
 cbn[V293_rdy_raw_cells]in *;clear -H;sep auto.
Qed.
Lemma TSOwnerRead : forall token,
 load(Tptr V293_tcb_type)(TSOwnedInput token)(403%positive,20%Z)=Some(Vptr token).
Proof.
 intro token. assert(P:mapstoval(403%positive,20%Z)(Tptr V293_tcb_type)false(Vptr token)(TSShareMemory token)).
 { apply V293_encoded_memory_mapsto. }
 assert(T:rule_type_val_match(Tptr V293_tcb_type)(Vptr token)=true)by reflexivity.
 pose proof(@mapstoval_load _ _ _ _ _ T P)as L.
 rewrite <- L. eapply load_mono;[apply map_join_comm;apply TSShareJoin|exact L].
Qed.
Definition TSAlias : addrval := (501%positive,Int.zero).
Theorem TSAliasPhysical : forall cs,TFState(TSOwnedInput TSAlias)true cs |=
 TFFull(V293_create_owned_share 403%positive TSAlias 5 ** FPR)cs.
Proof. apply TSOwnedLiteral. Qed.
Theorem TSAliasFreshnessCounterexample : ~ (forall s,
 s |= TFFull(V293_create_owned_share 403%positive TSAlias 5 ** FPR)nil ->
 (501%positive,Int.zero)<>TSAlias).
Proof. intro H. exact(H _ (TSAliasPhysical nil) eq_refl). Qed.

Lemma TSGoodOwned : forall token,GoodFunAsrt(V293_create_owned_share 403%positive token 5 ** FPR).
Proof. intro token. split;[exact I|apply EHGoodR]. Qed.
Definition TSFirstPre token cs := V293_tcb_enabled_hook_fpre 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions
 (V293_create_owned_share 403%positive token 5 ** FPR)(spec_done None)(fun _=>false)nil cs FPTid(TSGoodOwned token).
Definition TSFirstPost token cs := V293_tcb_enabled_hook_fpost 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions
 (V293_create_owned_share 403%positive token 5 ** FPR)(spec_done None)(fun _=>false)nil cs FPTid(TSGoodOwned token).
Definition TSSpec token cs : funspec := fun f=>if Z.eq_dec f 990%Z then
 Some(TSFirstPre token cs,TSFirstPost token cs,(Tvoid,[Tptr V293_tcb_type]))else if Z.eq_dec f 991%Z then
 Some(EHPre cs,EHPost cs,(Tvoid,[Tptr V293_tcb_type]))else None.
Lemma TSFirstLookup : forall token cs,TSSpec token cs 990%Z=
 Some(TSFirstPre token cs,TSFirstPost token cs,(Tvoid,[Tptr V293_tcb_type])).
Proof. intros;reflexivity. Qed.
Lemma TSSecondLookup : forall token cs,TSSpec token cs 991%Z=
 Some(EHPre cs,EHPost cs,(Tvoid,[Tptr V293_tcb_type])).
Proof. intros;reflexivity. Qed.
Definition TSFull b off next R cs :=
 V293_tcb_enabled_state 401%positive 208%positive 209%positive(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_initialized b off next 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions **
 V293_tcb_allocated_inputs 208%positive 201%positive 202%positive 203%positive
 204%positive 205%positive 206%positive 207%positive 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions
 (V293_tcb_table_binding 403%positive ** R))(spec_done None)(fun _=>false)nil cs.
Theorem TSSecondCallChecked : forall sd r ri token b off next cs,
 InfRules(TSSpec token cs)sd V293_witness_li FPInv r ri(TSFull b off next FPR cs)
 (scall 991%Z[evar 108%Z])(TSFull b off next FPR cs)FPTid.
Proof. intros. apply V293_tcb_second_hook with(good:=EHGoodR);[apply FPRCurLINV|apply TSSecondLookup]. Qed.
Theorem TSSecondLiteralInput : forall cs,TFState TFInput true cs |= TSFull 501%positive Int.zero FPNext FPR cs.
Proof. apply TFLiteralFull. Qed.
Theorem TSSecondActualArgument : forall cs,TFState TFInput true cs |= Rvl[evar 108%Z] @ [Tptr V293_tcb_type] == [FPHead].
Proof. apply TFActualArgument. Qed.
Theorem TSFirstCallChecked : forall sd r ri token b off next cs,
 InfRules(TSSpec token cs)sd V293_witness_li FPInv r ri
 (TSFull b off next(V293_create_owned_share 403%positive token 5 ** FPR)cs)
 (scall 990%Z[evar 108%Z])
 (TSFull b off next(V293_create_owned_share 403%positive token 5 ** FPR)cs)FPTid.
Proof.
 intros. apply V293_tcb_second_hook with(good:=TSGoodOwned token).
 - eapply V293_star_CurLINV_r. apply FPRCurLINV.
 - apply TSFirstLookup.
Qed.
Definition TSAdmits vl result owner : Prop := TFState TFInput true nil |=
 getasrt(EHPost nil vl result ([logic_val FPHead;logic_val FPNext]) owner) ** Atrue.
Theorem TSAdmitsExact : forall vl result owner,
 TSAdmits vl result owner <-> vl=[FPHead] /\ owner=FPTid /\ result=None.
Proof.
 intros vl result owner. unfold TSAdmits. cbn[EHPost V293_tcb_enabled_hook_fpost FPHead V293_hook_fpost getasrt].
 split;intro H.
 - assert(P:TFState TFInput true nil |= [|vl=[Vptr(501%positive,Int.zero)] /\ owner=FPTid /\ result=None|] ** Atrue)
   by(clear -H;sep auto).
   apply astar_l_apure_elim in P. exact(proj1 P).
 - pose proof(TFLiteralFull nil)as S. unfold TFFull in S. apply V293_tcb_enabled_hook_view in S.
   unfold V293_tcb_enabled_hook_resource in *. clear -S H;sep auto.
Qed.
Theorem TSAdmitsNone : TSAdmits ([FPHead]) None FPTid.
Proof. apply TSAdmitsExact. auto. Qed.
Theorem TSWrongPointerRejected : ~TSAdmits ([FPNext]) None FPTid.
Proof. intro H;apply TSAdmitsExact in H. destruct H as[H _]. discriminate H. Qed.
Theorem TSWrongOwnerRejected : ~TSAdmits ([FPHead]) None(302%positive,Int.zero).
Proof. intro H;apply TSAdmitsExact in H. destruct H as[_[H _]]. discriminate H. Qed.
Theorem TSWrongResultRejected : ~TSAdmits ([FPHead])(Some(Vint32 Int.zero))FPTid.
Proof. intro H;apply TSAdmitsExact in H. destruct H as[_[_ H]]. discriminate H. Qed.
Print Assumptions TSSecondCallChecked.
Print Assumptions TSAliasFreshnessCounterexample.
