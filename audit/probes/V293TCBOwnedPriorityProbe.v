(* Literal reservation owner/shared coexistence and real priority store control.
   Only the local between-Hook bracket is instantiated; production allocation
   freshness and the full nonempty API remain separate open obligations. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.audit.probes.V293TaskCreateReservationOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TCBOwnedPriority.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReservationOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Definition OPLE : env := set(sig 101%Z(201%positive,Tint8))108%Z(208%positive,Tptr V293_tcb_type).
Definition OPNode : addrval := (501%positive,Int.zero).
Definition OPPrio := ROBytes 201%positive true Tint8(V293_byteval 11).
Definition OPPtr := ROBytes 208%positive true(Tptr V293_tcb_type)(Vptr OPNode).
Definition OPLocals := merge OPPrio OPPtr.
Definition OPBase := merge OPLocals ROOuter.
Definition OPShared := merge ROFree(merge ROCounter ROFullReserved).
Definition OPWhole := merge OPBase OPShared.
Definition OPInput := V293_tcb_priority_state 403%positive 201%positive 208%positive 11(Vptr OPNode)
 (V293_create_owned_share 403%positive ROReserved 11 ** ROR)(spec_done None)(fun _=>false)true nil nil.
Definition OPOutput := V293_tcb_priority_state 403%positive 201%positive 208%positive 11(Vptr OPNode)
 ROR(spec_done None)(fun _=>false)true nil nil.
Definition OPK := Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull **
 Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0).
Ltac OPExpand := unfold OPBase,OPLocals,OPPrio,OPPtr,OPShared,ROOuter,ROCurrent,ROSentinel,ROFree,ROCounter,ROFullReserved,ROBytes;
 repeat first[rewrite map_merge_semp by reflexivity|rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Lemma OPBindings : forall cs, ROState OPLE emp cs |= V293_tcb_priority_bindings 403%positive 201%positive 208%positive.
Proof.
 intro cs. unfold V293_tcb_priority_bindings.
 eapply ROStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 - split.
   + exists 201%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + exists 208%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - split.
   + exists 403%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[ |split;reflexivity]. intros[v H]. vm_compute in H;discriminate.
Qed.
Lemma OPLocalsSpatial : forall cs, ROState OPLE OPLocals cs |=
 V293_tcb_priority_resources 403%positive 201%positive 208%positive 11(Vptr OPNode)Aemp.
Proof.
 intro cs. unfold V293_tcb_priority_resources. cbn[V293_tcb_priority_locals V293_rdy_raw_cells].
 eapply ROStar with(m1:=OPPrio)(m2:=OPPtr).
 - apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 201%positive);[subst b;right;left|left];
   unfold OPPrio,OPPtr,ROBytes;apply V293_encoded_memory_outside;left;congruence.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply ROStar with(m1:=OPPtr)(m2:=emp);[apply map_join_emp| | ].
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
   + apply astar_r_aemp_intro;apply OPBindings.
Qed.
Lemma OPBaseSpatial : forall cs, ROState OPLE OPBase cs |=
 V293_tcb_priority_resources 403%positive 201%positive 208%positive 11(Vptr OPNode)ROR.
Proof.
 intro cs. assert(H:ROState OPLE OPBase cs |=
 V293_tcb_priority_resources 403%positive 201%positive 208%positive 11(Vptr OPNode)Aemp ** ROR).
 { eapply ROStar with(m1:=OPLocals)(m2:=ROOuter).
   - apply map_join_merge;apply map_disjoint;intros[b off].
     destruct(Pos.eq_dec b 201%positive);[subst b;right;left| ].
     + OPExpand.
     + destruct(Pos.eq_dec b 208%positive);[subst b;right;left|left];OPExpand.
   - apply OPLocalsSpatial.
   - apply RORSpatial. }
 unfold V293_tcb_priority_resources in *;cbn[V293_tcb_priority_locals V293_rdy_raw_cells]in *;clear -H;sep auto.
Qed.
Lemma OPWholeJoin : join OPBase OPShared OPWhole.
Proof.
 apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 401%positive);[subst b;left| ].
 - OPExpand.
 - destruct(Pos.eq_dec b 403%positive);[subst b;left| ].
   + OPExpand.
   + destruct(Pos.eq_dec b 404%positive);[subst b;left|right;left];OPExpand.
Qed.
Lemma OPSharedSpatial : forall cs, ROState OPLE OPShared cs |=
 Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull **
 Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0) **
 Amapsto(403%positive,44%Z)(Tptr V293_tcb_type)true(Vptr ROReserved).
Proof.
 intro cs. eapply ROStar with(m1:=ROFree).
 - apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 401%positive);[subst b;right;left|left];OPExpand.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply ROStar with(m1:=ROCounter).
   + apply map_join_merge;apply map_disjoint;intros[b off].
     destruct(Pos.eq_dec b 404%positive);[subst b;right;left|left];OPExpand.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Theorem OPWholeLiteral : ROState OPLE OPWhole nil |= OPInput ** invlth_isr ROInv 0 INUM.
Proof.
 assert(H:ROState OPLE OPWhole nil |=
 V293_tcb_priority_resources 403%positive 201%positive 208%positive 11(Vptr OPNode)ROR **
 (Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull **
 Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0) **
 Amapsto(403%positive,44%Z)(Tptr V293_tcb_type)true(Vptr ROReserved))).
 { eapply ROStar;[apply OPWholeJoin|apply OPBaseSpatial|apply OPSharedSpatial]. }
 assert(S:ROState OPLE OPWhole nil |= Amapsto(403%positive,44%Z)(Tptr V293_tcb_type)true(Vptr ROReserved) **
 (V293_tcb_priority_resources 403%positive 201%positive 208%positive 11(Vptr OPNode)ROR **
 Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull ** Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0)))by(clear -H;sep auto).
 eapply astar_mono in S;[ |apply V293_reservation_publish|intros st HS;exact HS].
 assert(B:ROState OPLE OPWhole nil |=
 V293_tcb_priority_resources 403%positive 201%positive 208%positive 11(Vptr OPNode)
 (V293_create_owned_share 403%positive ROReserved 11 ** ROR) ** ROCore).
 { unfold V293_tcb_priority_resources,V293_create_owned_share,ROCore,V293_tcb_empty_pool,V293_create_owned_pool in *;
   cbn[V293_tcb_priority_locals V293_rdy_raw_cells]in *;clear -S;sep auto. }
 assert(C:ROState OPLE OPWhole nil |=
 V293_tcb_priority_resources 403%positive 201%positive 208%positive 11(Vptr OPNode)
 (V293_create_owned_share 403%positive ROReserved 11 ** ROR) ** (Aisr(fun _=>false) ** ROCore)).
 { apply astar_l_aisr_intro with(i:=(fun _=>false))in B;[clear -B;sep auto|reflexivity]. }
 eapply astar_mono in C;[ |intros st HS;exact HS|intros st HS;apply (ROBorrowEquivalence INUM);exact HS].
 apply astar_l_aop'_intro with(aop:=spec_done None)in C;[ |reflexivity].
 apply astar_l_aie_intro with(i:=true)in C;[ |reflexivity].
 apply astar_l_ais_intro with(i:=nil)in C;[ |reflexivity].
 apply astar_l_acs_intro with(i:=nil)in C;[ |reflexivity].
 unfold OPInput,V293_tcb_priority_state;clear -C;sep auto.
Qed.

Theorem OPActualArgument : ROState OPLE OPWhole nil |=
 Rvl [evar 108%Z] @ [Tptr V293_tcb_type] == [Vptr OPNode].
Proof.
 pose proof OPWholeLiteral as H.
 assert(C:ROState OPLE OPWhole nil |= V293_tcb_priority_state 403%positive 201%positive 208%positive 11(Vptr OPNode)
 ((V293_create_owned_share 403%positive ROReserved 11 ** ROR) ** invlth_isr ROInv 0 INUM)
 (spec_done None)(fun _=>false)true nil nil).
 { unfold OPInput,V293_tcb_priority_state,V293_tcb_priority_resources in *;
   cbn[V293_tcb_priority_locals V293_rdy_raw_cells]in *;clear -H;sep auto. }
 eapply V293_tcb_priority_argument;exact C.
Qed.
Theorem OPBracketChecked : forall sd r ri,
 InfRules(fun _=>None)sd V293_witness_li ROInv r ri OPInput
 (sseq(sprim encrit)(sseq(sassign(earrayelem(evar 92%Z)(evar 101%Z))(evar 108%Z))(sprim excrit)))
 OPOutput ROTid.
Proof.
 intros sd r ri. unfold OPInput,OPOutput,OPNode.
 eapply seq_rule.
 - apply V293_tcb_priority_enter with(reserved:=ROReserved)(K:=OPK).
   + vm_compute;lia.
   + apply RORGood.
   + intros s H;apply ROOwnedBorrowEquivalence in H;exact H.
 - eapply seq_rule.
   + apply V293_tcb_priority_store;[lia|apply V293_star_CurLINV_r;apply RORInv].
   + apply V293_tcb_priority_exit with(reserved:=ROReserved)(K:=OPK).
     * discriminate.
     * apply RORGood.
     * apply RORInv.
     * intros s H;apply ROOwnedBorrowEquivalence;exact H.
Qed.
Theorem OPSameInvariantBeforeAfter : forall le cs,
 ROState le(merge ROFree(merge(ROSlot(Vptr ROReserved))ROCounter))cs |= invlth_isr ROInv 0 INUM /\
 ROState le(merge ROFree(merge(ROSlot(Vptr OPNode))ROCounter))cs |= invlth_isr ROInv 0 INUM.
Proof. intros;split;apply ROSharedLiteral;reflexivity. Qed.

Lemma OPFullSlotSplit : exists m1 m2,
 mapstoval(403%positive,44%Z)(Tptr V293_tcb_type)true(Vptr ROReserved)m1 /\ join m1 m2 OPWhole.
Proof.
 assert(H:ROState OPLE OPWhole nil |=
 V293_tcb_priority_resources 403%positive 201%positive 208%positive 11(Vptr OPNode)ROR **
 (Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)false Vnull **
 Amapsto(404%positive,0%Z)Tint8 true(V293_byteval 0) **
 Amapsto(403%positive,44%Z)(Tptr V293_tcb_type)true(Vptr ROReserved))).
 { eapply ROStar;[apply OPWholeJoin|apply OPBaseSpatial|apply OPSharedSpatial]. }
 assert(C:ROState OPLE OPWhole nil |= Amapsto(403%positive,44%Z)(Tptr V293_tcb_type)true(Vptr ROReserved) ** Atrue)by(clear -H;sep auto).
 apply sat_split in C. destruct C as(m1&m2&o1&o2&JM&JO&HM&HQ).
 exists m1. exists m2. split;[exact(proj1 HM)|exact JM].
Qed.
Lemma OPLoadJoin : forall tp v a m1 m2 m,
 rule_type_val_match tp v=true -> mapstoval a tp true v m1 -> join m1 m2 m -> load tp m a=Some v.
Proof. intros. eapply load_local;[exact H1|eapply mapstoval_load;eassumption]. Qed.
Theorem OPActualReservedRead : load(Tptr V293_tcb_type)OPWhole(403%positive,44%Z)=Some(Vptr ROReserved).
Proof. destruct OPFullSlotSplit as(m1&m2&HM&J). eapply OPLoadJoin;[reflexivity|exact HM|exact J]. Qed.
Definition OPObserve (write:bool) :=
 match (if write then store(Tptr V293_tcb_type)OPWhole(403%positive,44%Z)(Vptr OPNode)else Some OPWhole)with
 |Some M=>load(Tptr V293_tcb_type)M(403%positive,44%Z)|None=>None end.
Theorem OPWrittenSlotRead : OPObserve true=Some(Vptr OPNode).
Proof.
 destruct OPFullSlotSplit as(m1&m2&HM&J).
 destruct(@store_exist_join' (403%positive,44%Z)(Tptr V293_tcb_type)(Vptr ROReserved)(Vptr OPNode)m1 m2 OPWhole HM J)as(M'&S).
 unfold OPObserve. rewrite S.
 destruct(@store_mapstoval_frame1 m1 m2 OPWhole M' (403%positive,44%Z)(Tptr V293_tcb_type)
 (Vptr ROReserved)(Vptr OPNode)HM J S)as(m1'&HM'&S'&J').
 eapply OPLoadJoin;[reflexivity|exact HM'|exact J'].
Qed.
Theorem OPOmittedSlotRead : OPObserve false=Some(Vptr ROReserved).
Proof. exact OPActualReservedRead. Qed.
Theorem OPOmittedSlotDiffers : OPObserve false<>Some(Vptr OPNode).
Proof. rewrite OPOmittedSlotRead;discriminate. Qed.
Theorem OPNoEvaluatorOracle : exists s,s |= OPInput ** invlth_isr ROInv 0 INUM /\
 s |= Rvl [evar 108%Z] @ [Tptr V293_tcb_type] == [Vptr OPNode].
Proof. exists(ROState OPLE OPWhole nil);split;[apply OPWholeLiteral|apply OPActualArgument]. Qed.
Print Assumptions OPBracketChecked.
Print Assumptions OPWholeLiteral.
Print Assumptions OPWrittenSlotRead.
Print Assumptions OPOmittedSlotDiffers.
