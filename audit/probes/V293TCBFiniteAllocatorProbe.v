(* Physical fixed-table allocator fixtures and single-factor refinement ablation. *)
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInit.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.hoareforward.init_spec.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFreePool.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.audit.probes.V293TCBFreePoolProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteAllocator.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteSites.
Definition FAPayloadRows b base := map(fun '(a,tp)=>(a,tp,FPDefault tp))(V293_tcb_free_payload_cells b base).
Definition FAPayloadMemory b base := FPMemory(FAPayloadRows b base).
Definition FANextMemory b base next := V293_encoded_memory b (base+20)%Z true(encode_val(Tcom_ptr 410%Z)next).
Definition FANodeMemory b base next := merge(FAPayloadMemory b base)(FANextMemory b base next).
Ltac FPOutside :=
 repeat first[rewrite V293_encoded_memory_outside by
 (first[left;congruence|right;rewrite ?encode_val_length;cbn[FPDefault length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia])
 |rewrite map_merge_semp by reflexivity];reflexivity.
Ltac FPApart b start count :=
 apply map_join_merge;apply map_disjoint;intros[other off];
 destruct(Pos.eq_dec other b)as[B|B];
 [subst other;destruct(Z_lt_dec off start)as[Low|Low];
 [left;apply V293_encoded_memory_outside;right;left;exact Low|
 destruct(Z_lt_dec off(start+count))as[Inside|Outside];
 [right;left;FPOutside|left;apply V293_encoded_memory_outside;right;right;
 rewrite ?encode_val_length;cbn[FPDefault length encode_val typelen list_repeat inj_pointer inj_bytes encode_int List.map];lia]]|
 left;apply V293_encoded_memory_outside;left;exact B].
Ltac FAPayloadTactic :=
 lazymatch goal with
 | |- FPState(merge(V293_encoded_memory ?b ?off true(encode_val ?tp ?v))?tail)?ie ?cs |= _ =>
   let bytes:=eval cbv in(Z.of_nat(typelen tp))in
   eapply FPStar with(m1:=V293_encoded_memory b off true(encode_val tp v));
   [FPApart b off bytes|exists v;apply astar_l_apure_intro;[split;[apply V293_encoded_memory_mapsto|reflexivity]|reflexivity]|FAPayloadTactic]
 | |- FPState emp _ _ |= Aemp =>split;reflexivity
 end.
Lemma FAPayloadSpatial : forall b base ie cs,
 FPState(FAPayloadMemory b base)ie cs |= V293_tcb_free_payload b base.
Proof.
 intros b base ie cs. unfold FAPayloadMemory,FAPayloadRows,V293_tcb_free_payload,V293_tcb_free_payload_cells.
 cbn[map FPMemory V293_storage]. FAPayloadTactic.
Qed.
Lemma FANodeSpatial : forall b base next ie cs,
 FPState(FANodeMemory b base next)ie cs |= V293_tcb_free_payload b base ** Amapsto(b,(base+20)%Z)(Tcom_ptr 410%Z)true next.
Proof.
 intros b base next ie cs. unfold FANodeMemory,V293_tcb_free_node.
 change(FPState(merge(FAPayloadMemory b base)(FANextMemory b base next))ie cs |=
 V293_tcb_free_payload b base ** Amapsto(b,(base+20)%Z)(Tcom_ptr 410%Z)true next).
 eapply FPStar with(m1:=FAPayloadMemory b base)(m2:=FANextMemory b base next).
 - unfold FANextMemory,FAPayloadMemory,FAPayloadRows,V293_tcb_free_payload_cells.
   cbn[map FPMemory]. apply map_join_merge;apply map_disjoint;intros[other off].
   destruct(Pos.eq_dec other b)as[B|B];[subst other|left;FPOutside].
   destruct(Z_lt_dec off(base+20)%Z)as[Low|Low];[right;left;FPOutside| ].
   destruct(Z_lt_dec off(base+24)%Z)as[Inside|Outside];[left;FPOutside|right;left;FPOutside].
 - apply FAPayloadSpatial.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.

Definition FAHead := Vptr(501%positive,Int.zero).
Definition FANext := Vptr(501%positive,Int.repr 56).
Definition FAChainMemory := merge(FANodeMemory 501%positive 0 FANext)(FANodeMemory 501%positive 56 Vnull).
Definition FASharedTwo := merge(FPHeadMemory FAHead)FAChainMemory.
Definition FASharedOne := merge(FPHeadMemory FANext)(FANodeMemory 501%positive 56 Vnull).
Lemma FAMembers : In(501%positive,Int.zero)(V293_tcb_table_sites 501%positive) /\
 In(501%positive,Int.repr 56)(V293_tcb_table_sites 501%positive).
Proof. unfold V293_tcb_table_sites;cbn[seq map];simpl;split;intuition congruence. Qed.
Lemma FAOneChain : forall n ie cs,
 FPState(FANodeMemory 501%positive 56 Vnull)ie cs |=
 V293_tcb_site_free_chain(V293_tcb_table_sites 501%positive)(S n)FANext.
Proof.
 intros n ie cs. cbn[FANext V293_tcb_site_free_chain].
 rewrite Int.unsigned_repr by(vm_compute;intuition congruence).
 apply astar_l_apure_intro;[ |split;[change(111<=4294967295)%Z;lia|apply FAMembers]].
 pose proof(FANodeSpatial 501%positive 56 Vnull ie cs)as H.
 eapply astar_mono;[intros st HS;exact HS| |exact H].
 intros st HS. exists Vnull. apply astar_l_apure_intro;[ |reflexivity].
 destruct n;cbn[V293_tcb_site_free_chain];apply astar_r_aemp_intro;exact HS.
Qed.
Lemma FAChainSpatial : forall ie cs,
 FPState FAChainMemory ie cs |= V293_tcb_site_free_chain(V293_tcb_table_sites 501%positive)13 FAHead.
Proof.
 intros ie cs. unfold FAChainMemory. cbn[FAHead V293_tcb_site_free_chain].
 apply astar_l_apure_intro;[ |split;[change(55<=4294967295)%Z;lia|apply FAMembers]].
 assert(S:FPState(merge(FANodeMemory 501%positive 0 FANext)(FANodeMemory 501%positive 56 Vnull))ie cs |=
 (V293_tcb_free_payload 501%positive 0 ** Amapsto(501%positive,20%Z)(Tcom_ptr 410%Z)true FANext) **
 V293_tcb_site_free_chain(V293_tcb_table_sites 501%positive)12 FANext).
 { eapply FPStar;[ |apply FANodeSpatial|apply FAOneChain].
   unfold FANodeMemory,FAPayloadMemory,FAPayloadRows,V293_tcb_free_payload_cells,FANextMemory.
   cbn[map FPMemory]. apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 501%positive);[subst b|left;FPOutside].
   destruct(Z_lt_dec off 56);[right;left;FPOutside|left;FPOutside]. }
 clear -S;unfold FANext in *;sep auto.
Qed.
Lemma FATwoRaw : forall ie cs,FPState FASharedTwo ie cs |=
 Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)true FAHead **
 V293_tcb_site_free_chain(V293_tcb_table_sites 501%positive)13 FAHead.
Proof.
 intros ie cs. eapply FPStar with(m1:=FPHeadMemory FAHead)(m2:=FAChainMemory).
 - apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 401%positive);[subst b;right;left|left];
   unfold FPHeadMemory,FAChainMemory,FANodeMemory,FAPayloadMemory,FAPayloadRows,V293_tcb_free_payload_cells,FANextMemory,FPBytes;
   cbn[map FPMemory];FPOutside.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - apply FAChainSpatial.
Qed.
Lemma FATwoPool : forall ie cs,
 FPState FASharedTwo ie cs |= V293_tcb_site_free_pool 501%positive 401%positive.
Proof. intros. exists FAHead. apply astar_l_apure_intro;[apply FATwoRaw|reflexivity]. Qed.
Lemma FAOnePool : forall ie cs,
 FPState FASharedOne ie cs |= V293_tcb_site_free_pool 501%positive 401%positive.
Proof.
 intros ie cs. exists FANext. apply astar_l_apure_intro;[ |reflexivity].
 eapply FPStar with(m1:=FPHeadMemory FANext)(m2:=FANodeMemory 501%positive 56 Vnull).
 - apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 401%positive);[subst b;right;left|left];
   unfold FPHeadMemory,FANodeMemory,FAPayloadMemory,FAPayloadRows,V293_tcb_free_payload_cells,FANextMemory,FPBytes;
   cbn[map FPMemory];FPOutside.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - apply FAOneChain.
Qed.
Definition FACore := V293_tcb_site_free_pool 501%positive 401%positive.
Lemma FACoreGood : GoodInvAsrt FACore.
Proof. apply V293_tcb_site_free_pool_good. Qed.
Lemma FACorePrecise : precise FACore.
Proof. apply V293_tcb_site_free_pool_precise. Qed.
Lemma FACoreISR : assertion.inv_isr_prop FACore.
Proof. apply V293_tcb_site_free_pool_isr. Qed.
Definition FAInv : Inv := fun i=>match i with
 | O=>mkinvasrt FACoreGood(conj FACorePrecise FACoreISR)
 | S j=>V293_shared_inv(S j) end.
Lemma FANoisrTail : forall n i,starinv_noisr FAInv(S i)n <==> Aemp.
Proof.
 induction n;intros i s;cbn[starinv_noisr];[reflexivity| ].
 change(s |= Aemp ** starinv_noisr FAInv(S(S i))n <-> s |= Aemp).
 split;intro H.
 - apply astar_l_aemp_elim in H. apply IHn in H;exact H.
 - apply astar_l_aemp_intro. apply IHn;exact H.
Qed.
Lemma FANoisrCore : forall n,starinv_noisr FAInv 0 n <==> FACore.
Proof.
 intros[ |n]s;[reflexivity| ].
 change(s |= FACore ** starinv_noisr FAInv 1 n <-> s |= FACore).
 split;intro H.
 - apply astar_r_aemp_elim. eapply astar_mono;[intros st HS;exact HS|intros st HS;apply FANoisrTail in HS;exact HS|exact H].
 - eapply astar_mono;[intros st HS;exact HS|intros st HS;apply FANoisrTail;exact HS| ]. apply astar_r_aemp_intro;exact H.
Qed.
Theorem FABorrowEquivalence : forall n,
 Aisr(fun _=>false) ** invlth_isr FAInv 0 n <==> Aisr(fun _=>false) ** FACore.
Proof.
 intros n s. destruct s as [[[[[[ge le] M] ir] aux] O] op]. split;intro H.
 all: (apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&H1&H2);
 destruct H1 as[E Empty];cbn in E;subst ir;
 apply sat_split';exists m1;exists m2;exists o1;exists o2;
 split;[exact JM| ];split;[exact JO| ];split;[split;[reflexivity|exact Empty]| ]).
 - unfold invlth_isr in H2. rewrite Nat.sub_0_r in H2.
   apply FANoisrCore with(n:=n). eapply invisr_imply_noisr';[ |exact H2]. reflexivity.
 - unfold invlth_isr. rewrite Nat.sub_0_r.
   apply V293_shared_clear_noisr_close;[reflexivity| ]. apply FANoisrCore;exact H2.
Qed.


Theorem FASameInvariantTwoOne : forall ie cs,
 FPState FASharedOne ie cs |= invlth_isr FAInv 0 INUM /\
 FPState FASharedTwo ie cs |= invlth_isr FAInv 0 INUM.
Proof.
 intros ie cs. split;unfold invlth_isr;rewrite Nat.sub_0_r;
 apply V293_shared_clear_noisr_close;[reflexivity| |reflexivity| ];apply FANoisrCore.
 - apply FAOnePool.
 - apply FATwoPool.
Qed.
Lemma FAWholePartition : forall pc cpu,
 join(FPCaller pc cpu)FASharedTwo(merge(FPCaller pc cpu)FASharedTwo).
Proof.
 intros pc cpu. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 401%positive)as[B|B];[left;apply FPCallerNoShared;auto| ].
 destruct(Pos.eq_dec b 501%positive)as[C|C];[left;apply FPCallerNoShared;auto| ].
 right;left. unfold FASharedTwo,FPHeadMemory,FAChainMemory,FANodeMemory,FAPayloadMemory,FAPayloadRows,V293_tcb_free_payload_cells,FANextMemory,FPBytes;
 cbn[map FPMemory];FPOutside.
Qed.
Theorem FAActualPopInput : forall cs,
 FPState(merge(FPCaller FAHead(Vint32 Int.zero))FASharedTwo)false(true::cs) |=
 V293_tcb_site_free_critical 501%positive 401%positive 208%positive 209%positive FAHead(Vint32 Int.zero)FAHead Aemp FPR
 (spec_done None)(fun _=>false)nil(true::cs).
Proof.
 intro cs. assert(H:FPState(merge(FPCaller FAHead(Vint32 Int.zero))FASharedTwo)false(true::cs) |=
 V293_tcb_enabled_resources 401%positive 208%positive 209%positive FAHead(Vint32 Int.zero)FPR **
 (Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)true FAHead ** V293_tcb_site_free_chain(V293_tcb_table_sites 501%positive)13 FAHead)).
 { eapply FPStar;[apply FAWholePartition|apply FPCallerSpatial|apply FATwoRaw]. }
 assert(B:FPState(merge(FPCaller FAHead(Vint32 Int.zero))FASharedTwo)false(true::cs) |=
 Aisr(fun _=>false) ** Aie false ** Ais nil ** Acs(true::cs) **
 (V293_tcb_enabled_resources 401%positive 208%positive 209%positive FAHead(Vint32 Int.zero)FPR **
 (Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)true FAHead ** V293_tcb_site_free_chain(V293_tcb_table_sites 501%positive)13 FAHead))).
 { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
   apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[ |reflexivity]. exact H. }
 unfold V293_tcb_site_free_critical,V293_tcb_enabled_resources in *.
 apply astar_l_aop'_intro;[ |reflexivity]. clear -B;sep auto.
Qed.
Theorem FAPopTransferChecked : forall sd r ri cs,
 InfRules(fun _=>None)sd V293_witness_li FAInv r ri
 (V293_tcb_site_free_critical 501%positive 401%positive 208%positive 209%positive FAHead(Vint32 Int.zero)FAHead Aemp FPR
 (spec_done None)(fun _=>false)nil(true::cs))
 (sseq(V293_TCBInit_pop 91%Z 108%Z)(sprim excrit))
 (EX next:val,[|((Int.unsigned Int.zero+55<=Int.max_unsigned)%Z /\ In(501%positive,Int.zero)(V293_tcb_table_sites 501%positive)) /\ rule_type_val_match(Tcom_ptr 410%Z)next=true|] **
 V293_tcb_enabled_state 401%positive 208%positive 209%positive FAHead(Vint32 Int.zero)
 (V293_tcb_free_node 501%positive Int.zero next ** FPR)(spec_done None)(fun _=>false)nil cs)FPTid.
Proof.
 intros. apply V293_OS_TCBInit_site_free_pop_transfer;[apply FPRGood|apply FPRCurLINV| ].
 intros s H. apply FABorrowEquivalence. unfold FACore.
 clear -H. sep auto.
Qed.


(* Same actual heap, same 13-step fuel and 56-byte node. Only membership
   refinement is removed; the old predicate admits a node in block 502. *)
Lemma FAOutsideHeadRead :
 load(Tptr V293_tcb_type)FPSharedOne(401%positive,0%Z)=Some FPNext.
Proof.
 assert(H:FPState FPSharedOne true nil |=
 Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)true FPNext ** V293_tcb_free_node 502%positive Int.zero Vnull).
 { eapply FPStar with(m1:=FPHeadMemory FPNext)(m2:=FPNodeMemory 502%positive Vnull).
   - apply map_join_merge;apply map_disjoint;intros[b off].
     destruct(Pos.eq_dec b 401%positive);[subst b;right;left|left];
     unfold FPHeadMemory,FPNodeMemory,FPPayloadMemory,FPPayloadRows,V293_tcb_free_payload_cells,FPNextMemory,FPBytes;
     cbn[map FPMemory];FPOutside.
   - split;[apply V293_encoded_memory_mapsto|reflexivity].
   - apply FPNodeSpatial. }
 change(load(Tptr V293_tcb_type)(getmem(FPState FPSharedOne true nil))(401%positive,0%Z)=Some FPNext).
 eapply V293_star_load_l;[ |exact H].
 intros st[HM _]. eapply mapstoval_load;[reflexivity|exact HM].
Qed.
Theorem FAWithoutMembershipPhysicalCounterexample : forall ie cs,
 FPState FPSharedOne ie cs |= V293_tcb_free_pool 401%positive /\
 ~(FPState FPSharedOne ie cs |= V293_tcb_site_free_pool 501%positive 401%positive).
Proof.
 intros ie cs. split;[apply FPOnePool| ]. intros[head H].
 apply astar_l_apure_elim in H. destruct H as[Typed H].
 assert(L:load(Tptr V293_tcb_type)FPSharedOne(401%positive,0%Z)=Some head).
 { change(load(Tptr V293_tcb_type)(getmem(FPState FPSharedOne ie cs))(401%positive,0%Z)=Some head).
   eapply V293_star_load_l;[ |exact H].
   intros st[HM _]. eapply mapstoval_load;[exact Typed|exact HM]. }
 rewrite FAOutsideHeadRead in L. inversion L;subst head.
 cbn[FPNext V293_tcb_site_free_chain]in H. sep normal in H. sep destruct H.
 assert(P:FPState FPSharedOne ie cs |=
 [|In(502%positive,Int.zero)(V293_tcb_table_sites 501%positive)|] ** Atrue).
 { clear -H;sep auto;tauto. }
 apply astar_l_apure_elim in P. destruct P as[Member _].
 clear -Member. unfold V293_tcb_table_sites in Member. cbn[seq map]in Member. simpl in Member. intuition congruence.
Qed.
Print Assumptions FAActualPopInput.
Print Assumptions FAPopTransferChecked.
Print Assumptions FASameInvariantTwoOne.
Print Assumptions FAWithoutMembershipPhysicalCounterexample.
Print Assumptions V293_OS_TCBInit_site_allocated_finite_published.
