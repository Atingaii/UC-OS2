(* Same invariant, literal empty / two-node heaps, actual extraction.
   Empty local invariant and bounded capacity are fixtures, not kernel initialization. *)
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
Definition FPGE : env := set (sig 91%Z (401%positive,Tptr V293_tcb_type))
 OSTCBCur (402%positive,Tptr Tvoid).
Definition FPLE : env := set (set (set (set (set (set (set (set
 (sig 107%Z (207%positive,Tint16)) 106%Z (206%positive,Tptr Tvoid))
 105%Z (205%positive,Tint32)) 104%Z (204%positive,Tint16))
 103%Z (203%positive,Tptr Tint32)) 102%Z (202%positive,Tptr Tint32))
 101%Z (201%positive,Tint8)) 108%Z (208%positive,Tptr V293_tcb_type))
 109%Z (209%positive,Tint32).
Definition FPTid : tid := (301%positive,Int.repr 8).
Definition FPBytes b permission tp v := V293_encoded_memory b 0 permission (encode_val tp v).
Definition FPCurrent := FPBytes 402%positive false (Tptr Tvoid) (Vptr FPTid).
Definition FPSentinel := FPBytes 601%positive true Tint8 (Vint32(Int.repr 77)).
Definition FPState M ie cs : RstateOP :=
 (FPGE,FPLE,M,(fun _=>false),(ie,[],cs),(emp:osabst),spec_done None).
Definition FPR := CurTid FPTid ** LINV V293_witness_li FPTid [] **
 Amapsto (601%positive,0%Z) Tint8 true (Vint32(Int.repr 77)).

Lemma FPStar : forall m1 m2 m ie cs p q,
 join m1 m2 m -> FPState m1 ie cs |= p -> FPState m2 ie cs |= q ->
 FPState m ie cs |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2.
 exists(emp:osabst). exists(emp:osabst).
 split;[exact H | ]. split;[apply map_join_emp | ]. split;assumption.
Qed.
Lemma FPCurrentSpatial : forall ie cs, FPState FPCurrent ie cs |= CurTid FPTid.
Proof.
 intros ie cs. exists Tvoid. exists 402%positive.
 eapply FPStar with (m1:=emp) (m2:=FPCurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 402%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma FPLInvSpatial : forall ie cs, FPState emp ie cs |= LINV V293_witness_li FPTid [].
Proof.
 intros ie cs. unfold LINV. apply astar_comm. apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Ltac FPRapart b :=
 apply map_join_merge;apply map_disjoint;intros [other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold FPCurrent,FPSentinel,FPBytes;
 repeat first [rewrite map_merge_semp by reflexivity |
 rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity.
Lemma FPRSpatial : forall ie cs,
 FPState (merge FPCurrent FPSentinel) ie cs |= FPR.
Proof.
 intros ie cs. unfold FPR.
 eapply FPStar with (m1:=FPCurrent) (m2:=FPSentinel).
 - FPRapart 402%positive.
 - apply FPCurrentSpatial.
 - eapply FPStar with (m1:=emp) (m2:=FPSentinel).
   + apply map_join_comm;apply map_join_emp.
   + apply FPLInvSpatial.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma FPRGood : GoodFrm FPR.
Proof. cbn [FPR CurTid LINV V293_witness_li GoodFrm]. repeat split;exact I. Qed.
Lemma FPRCurLINV : FPR ==> CurLINV V293_witness_li FPTid.
Proof.
 intros s HS. unfold CurLINV. exists([]:list logicvar).
 unfold FPR in HS. clear -HS. sep auto.
Qed.


Definition FPDefault tp := match tp with Tint8|Tint16|Tint32=>Vint32 Int.zero|_=>Vnull end.
Fixpoint FPMemory (cells:list(addr*type*val)) : mem :=
 match cells with nil=>emp | ((b,i),tp,v)::rest=>
 merge(V293_encoded_memory b i true(encode_val tp v))(FPMemory rest) end.
Definition FPPayloadRows b := map(fun '(a,tp)=>(a,tp,FPDefault tp))(V293_tcb_free_payload_cells b 0).
Definition FPPayloadMemory b := FPMemory(FPPayloadRows b).
Definition FPNextMemory b next := V293_encoded_memory b 20 true(encode_val(Tcom_ptr 410%Z)next).
Definition FPNodeMemory b next := merge(FPPayloadMemory b)(FPNextMemory b next).
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
Ltac FPPayloadTactic :=
 lazymatch goal with
 | |- FPState(merge(V293_encoded_memory ?b ?off true(encode_val ?tp ?v))?tail)?ie ?cs |= _ =>
   let bytes:=eval cbv in(Z.of_nat(typelen tp))in
   eapply FPStar with(m1:=V293_encoded_memory b off true(encode_val tp v));
   [FPApart b off bytes|exists v;apply astar_l_apure_intro;[split;[apply V293_encoded_memory_mapsto|reflexivity]|reflexivity]|FPPayloadTactic]
 | |- FPState emp _ _ |= Aemp =>split;reflexivity
 end.
Lemma FPPayloadSpatial : forall b ie cs,
 FPState(FPPayloadMemory b)ie cs |= V293_tcb_free_payload b 0.
Proof.
 intros b ie cs. unfold FPPayloadMemory,FPPayloadRows,V293_tcb_free_payload,V293_tcb_free_payload_cells.
 cbn[map FPMemory V293_storage]. FPPayloadTactic.
Qed.
Lemma FPNodeSpatial : forall b next ie cs,
 FPState(FPNodeMemory b next)ie cs |= V293_tcb_free_node b Int.zero next.
Proof.
 intros b next ie cs. unfold FPNodeMemory,V293_tcb_free_node.
 change(FPState(merge(FPPayloadMemory b)(FPNextMemory b next))ie cs |=
 V293_tcb_free_payload b 0 ** Amapsto(b,20%Z)(Tcom_ptr 410%Z)true next).
 eapply FPStar with(m1:=FPPayloadMemory b)(m2:=FPNextMemory b next).
 - unfold FPNextMemory,FPPayloadMemory,FPPayloadRows,V293_tcb_free_payload_cells.
   cbn[map FPMemory]. apply map_join_merge;apply map_disjoint;intros[other off].
   destruct(Pos.eq_dec other b)as[B|B];[subst other|left;FPOutside].
   destruct(Z_lt_dec off 20)as[Low|Low];[right;left;FPOutside| ].
   destruct(Z_lt_dec off 24)as[Inside|Outside];[left;FPOutside|right;left;FPOutside].
 - apply FPPayloadSpatial.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Definition FPHead := Vptr(501%positive,Int.zero).
Definition FPNext := Vptr(502%positive,Int.zero).
Definition FPChainMemory := merge(FPNodeMemory 501%positive FPNext)(FPNodeMemory 502%positive Vnull).
Definition FPHeadMemory head := FPBytes 401%positive true(Tptr V293_tcb_type)head.
Definition FPSharedEmpty := FPHeadMemory Vnull.
Definition FPSharedTwo := merge(FPHeadMemory FPHead)FPChainMemory.
Lemma FPChainSpatial : forall ie cs,
 FPState FPChainMemory ie cs |= V293_tcb_free_chain 13 FPHead.
Proof.
 intros ie cs. unfold FPChainMemory. cbn[FPHead V293_tcb_free_chain].
 apply astar_l_apure_intro;[ |change(55<=4294967295)%Z;lia].
 assert(T:FPState(FPNodeMemory 502%positive Vnull)ie cs |= V293_tcb_free_chain 12 FPNext).
 { cbn[FPNext V293_tcb_free_chain]. apply astar_l_apure_intro;[ |change(55<=4294967295)%Z;lia].
   unfold V293_tcb_free_node in *. pose proof(FPNodeSpatial 502%positive Vnull ie cs)as H.
   cbn[Int.unsigned]in H. eapply astar_mono;[intros st HS;exact HS| |exact H].
   intros st HS. exists Vnull. apply astar_l_apure_intro;[ |reflexivity].
   cbn[V293_tcb_free_chain]. apply astar_r_aemp_intro;exact HS. }
 assert(S:FPState(merge(FPNodeMemory 501%positive FPNext)(FPNodeMemory 502%positive Vnull))ie cs |=
 V293_tcb_free_node 501%positive Int.zero FPNext ** V293_tcb_free_chain 12 FPNext).
 { eapply FPStar;[ |apply FPNodeSpatial|exact T].
   unfold FPNodeMemory,FPPayloadMemory,FPPayloadRows,V293_tcb_free_payload_cells,FPNextMemory.
   cbn[map FPMemory]. apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 501%positive);[subst b;right;left|left];FPOutside. }
 unfold V293_tcb_free_node in S. cbn[Int.unsigned]in S. clear -S;sep auto.
Qed.
Lemma FPEmptyPool : forall ie cs,FPState FPSharedEmpty ie cs |= V293_tcb_free_pool 401%positive.
Proof.
 intros ie cs. exists Vnull. apply astar_l_apure_intro;[ |reflexivity].
 cbn[V293_tcb_free_chain]. apply astar_r_aemp_intro. split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma FPTwoRaw : forall ie cs,FPState FPSharedTwo ie cs |=
 Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)true FPHead ** V293_tcb_free_chain 13 FPHead.
Proof.
 intros ie cs.
 eapply FPStar with(m1:=FPHeadMemory FPHead)(m2:=FPChainMemory).
 - apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 401%positive);[subst b;right;left|left];
   unfold FPHeadMemory,FPChainMemory,FPNodeMemory,FPPayloadMemory,FPPayloadRows,V293_tcb_free_payload_cells,FPNextMemory,FPBytes;
   cbn[map FPMemory];FPOutside.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - apply FPChainSpatial.
Qed.

Lemma FPTwoPool : forall ie cs,FPState FPSharedTwo ie cs |= V293_tcb_free_pool 401%positive.
Proof. intros. exists FPHead. apply astar_l_apure_intro;[apply FPTwoRaw|reflexivity]. Qed.
Definition FPCore := V293_tcb_free_pool 401%positive.
Lemma FPCoreGood : GoodInvAsrt FPCore.
Proof. apply V293_tcb_free_pool_good. Qed.
Lemma FPCorePrecise : precise FPCore.
Proof. apply V293_tcb_free_pool_precise. Qed.
Lemma FPCoreISR : assertion.inv_isr_prop FPCore.
Proof. apply V293_tcb_free_pool_isr. Qed.
Definition FPInv : Inv := fun i=>match i with
 | O=>mkinvasrt FPCoreGood(conj FPCorePrecise FPCoreISR)
 | S j=>V293_shared_inv(S j) end.
Lemma FPNoisrTail : forall n i,starinv_noisr FPInv(S i)n <==> Aemp.
Proof.
 induction n;intros i s;cbn[starinv_noisr];[reflexivity| ].
 change(s |= Aemp ** starinv_noisr FPInv(S(S i))n <-> s |= Aemp).
 split;intro H.
 - apply astar_l_aemp_elim in H. apply IHn in H;exact H.
 - apply astar_l_aemp_intro. apply IHn;exact H.
Qed.
Lemma FPNoisrCore : forall n,starinv_noisr FPInv 0 n <==> FPCore.
Proof.
 intros[ |n]s;[reflexivity| ].
 change(s |= FPCore ** starinv_noisr FPInv 1 n <-> s |= FPCore).
 split;intro H.
 - apply astar_r_aemp_elim. eapply astar_mono;[intros st HS;exact HS|intros st HS;apply FPNoisrTail in HS;exact HS|exact H].
 - eapply astar_mono;[intros st HS;exact HS|intros st HS;apply FPNoisrTail;exact HS| ]. apply astar_r_aemp_intro;exact H.
Qed.
Theorem FPBorrowEquivalence : forall n,
 Aisr(fun _=>false) ** invlth_isr FPInv 0 n <==> Aisr(fun _=>false) ** FPCore.
Proof.
 intros n s. destruct s as [[[[[[ge le] M] ir] aux] O] op]. split;intro H.
 all: (apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&H1&H2);
 destruct H1 as[E Empty];cbn in E;subst ir;
 apply sat_split';exists m1;exists m2;exists o1;exists o2;
 split;[exact JM| ];split;[exact JO| ];split;[split;[reflexivity|exact Empty]| ]).
 - unfold invlth_isr in H2. rewrite Nat.sub_0_r in H2.
   apply FPNoisrCore with(n:=n). eapply invisr_imply_noisr';[ |exact H2]. reflexivity.
 - unfold invlth_isr. rewrite Nat.sub_0_r.
   apply V293_shared_clear_noisr_close;[reflexivity| ]. apply FPNoisrCore;exact H2.
Qed.


Theorem FPSameInvariantEmptyTwo : forall ie cs,
 FPState FPSharedEmpty ie cs |= invlth_isr FPInv 0 INUM /\
 FPState FPSharedTwo ie cs |= invlth_isr FPInv 0 INUM.
Proof.
 intros ie cs. split;unfold invlth_isr;rewrite Nat.sub_0_r;
 apply V293_shared_clear_noisr_close;[reflexivity| |reflexivity| ];apply FPNoisrCore.
 - apply FPEmptyPool.
 - apply FPTwoPool.
Qed.
Definition FPPc pc := FPBytes 208%positive true(Tptr V293_tcb_type)pc.
Definition FPCpu cpu := FPBytes 209%positive true Tint32 cpu.
Definition FPCaller pc cpu := merge(FPPc pc)(merge(FPCpu cpu)(merge FPCurrent FPSentinel)).
Lemma FPBindings : forall ie cs,
 FPState emp ie cs |= V293_tcb_empty_bindings 401%positive 208%positive 209%positive.
Proof.
 intros ie cs. unfold V293_tcb_empty_bindings. repeat split.
 - exists 208%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - exists 209%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - exists 401%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - intros[v H]. vm_compute in H;discriminate.
Qed.
Lemma FPCallerSpatial : forall pc cpu ie cs,
 FPState(FPCaller pc cpu)ie cs |= V293_tcb_enabled_resources 401%positive 208%positive 209%positive pc cpu FPR.
Proof.
 intros pc cpu ie cs. unfold V293_tcb_enabled_resources.
 eapply FPStar with(m1:=emp)(m2:=FPCaller pc cpu);[apply map_join_comm;apply map_join_emp|apply FPBindings| ].
 unfold FPCaller. eapply FPStar with(m1:=FPPc pc).
 - unfold FPPc,FPCpu,FPCurrent,FPSentinel,FPBytes. FPApart 208%positive 0%Z 4%Z.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply FPStar with(m1:=FPCpu cpu).
   + unfold FPCpu,FPCurrent,FPSentinel,FPBytes. FPApart 209%positive 0%Z 4%Z.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
   + apply FPRSpatial.
Qed.
Lemma FPCallerNoShared : forall pc cpu b off,
 b=401%positive \/ b=501%positive \/ b=502%positive -> get(FPCaller pc cpu)(b,off)=None.
Proof.
 intros pc cpu b off B. destruct B as [E | [E | E]];subst b;
 unfold FPCaller,FPPc,FPCpu,FPCurrent,FPSentinel,FPBytes;FPOutside.
Qed.
Lemma FPWholePartition : forall pc cpu (present:bool),
 join(FPCaller pc cpu)(if present then FPSharedTwo else FPSharedEmpty)
 (merge(FPCaller pc cpu)(if present then FPSharedTwo else FPSharedEmpty)).
Proof.
 intros pc cpu present. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 401%positive)as[B|B];[left;apply FPCallerNoShared;auto| ].
 destruct(Pos.eq_dec b 501%positive)as[C|C];[left;apply FPCallerNoShared;auto| ].
 destruct(Pos.eq_dec b 502%positive)as[D|D];[left;apply FPCallerNoShared;auto| ].
 right;left. destruct present;
 unfold FPSharedTwo,FPSharedEmpty,FPHeadMemory,FPChainMemory,FPNodeMemory,FPPayloadMemory,FPPayloadRows,V293_tcb_free_payload_cells,FPNextMemory,FPBytes;
 cbn[map FPMemory];FPOutside.
Qed.
Theorem FPWholeEnabledLiteral : forall (present:bool) cs,
 FPState(merge(FPCaller Vundef(Vint32(Int.repr 99)))(if present then FPSharedTwo else FPSharedEmpty))true cs |=
 V293_tcb_enabled_state 401%positive 208%positive 209%positive Vundef(Vint32(Int.repr 99))FPR
 (spec_done None)(fun _=>false)nil cs ** invlth_isr FPInv 0 INUM.
Proof.
 intros present cs. eapply FPStar;[apply FPWholePartition| | ].
 - unfold V293_tcb_enabled_state. apply astar_l_aop'_intro;[ |reflexivity].
   assert(H:FPState(FPCaller Vundef(Vint32(Int.repr 99)))true cs |=
   Aisr(fun _=>false) ** Aie true ** Ais nil ** Acs cs **
   V293_tcb_enabled_resources 401%positive 208%positive 209%positive Vundef(Vint32(Int.repr 99))FPR).
   { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
     apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[ |reflexivity]. apply FPCallerSpatial. }
   clear -H;sep auto.
 - destruct present;apply FPSameInvariantEmptyTwo.
Qed.
Theorem FPActualPopInput : forall cs,
 FPState(merge(FPCaller FPHead(Vint32 Int.zero))FPSharedTwo)false(true::cs) |=
 V293_tcb_free_critical 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)FPHead Aemp FPR
 (spec_done None)(fun _=>false)nil(true::cs).
Proof.
 intro cs. assert(H:FPState(merge(FPCaller FPHead(Vint32 Int.zero))FPSharedTwo)false(true::cs) |=
 V293_tcb_enabled_resources 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)FPR **
 (Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)true FPHead ** V293_tcb_free_chain 13 FPHead)).
 { eapply FPStar;[apply FPWholePartition with(present:=true)|apply FPCallerSpatial|apply FPTwoRaw]. }
 assert(B:FPState(merge(FPCaller FPHead(Vint32 Int.zero))FPSharedTwo)false(true::cs) |=
 Aisr(fun _=>false) ** Aie false ** Ais nil ** Acs(true::cs) **
 (V293_tcb_enabled_resources 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)FPR **
 (Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)true FPHead ** V293_tcb_free_chain 13 FPHead))).
 { apply astar_l_aisr_intro;[ |reflexivity]. apply astar_l_aie_intro;[ |reflexivity].
   apply astar_l_ais_intro;[ |reflexivity]. apply astar_l_acs_intro;[ |reflexivity]. exact H. }
 unfold V293_tcb_free_critical,V293_tcb_enabled_resources in *.
 apply astar_l_aop'_intro;[ |reflexivity]. clear -B;sep auto.
Qed.
Theorem FPPopTransferChecked : forall sd r ri cs,
 InfRules(fun _=>None)sd V293_witness_li FPInv r ri
 (V293_tcb_free_critical 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)FPHead Aemp FPR
 (spec_done None)(fun _=>false)nil(true::cs))
 (sseq(V293_TCBInit_pop 91%Z 108%Z)(sprim excrit))
 (EX next:val,[|(Int.unsigned Int.zero+55<=Int.max_unsigned)%Z /\ rule_type_val_match(Tcom_ptr 410%Z)next=true|] **
 V293_tcb_enabled_state 401%positive 208%positive 209%positive FPHead(Vint32 Int.zero)
 (V293_tcb_free_node 501%positive Int.zero next ** FPR)(spec_done None)(fun _=>false)nil cs)FPTid.
Proof.
 intros. apply V293_OS_TCBInit_free_pop_transfer;[apply FPRGood|apply FPRCurLINV| ].
 intros s H. apply FPBorrowEquivalence. unfold FPCore.
 clear -H. sep auto.
Qed.

(* The same invariant also accepts the changed one-node shared tail. *)
Definition FPSharedOne := merge(FPHeadMemory FPNext)(FPNodeMemory 502%positive Vnull).
Lemma FPOneChainSpatial : forall n ie cs,
 FPState(FPNodeMemory 502%positive Vnull)ie cs |= V293_tcb_free_chain(S n)FPNext.
Proof.
 intros n ie cs. cbn[FPNext V293_tcb_free_chain].
 apply astar_l_apure_intro;[ |change(55<=4294967295)%Z;lia].
 pose proof(FPNodeSpatial 502%positive Vnull ie cs)as H.
 unfold V293_tcb_free_node in H. cbn[Int.unsigned]in H.
 eapply astar_mono;[intros st HS;exact HS| |exact H].
 intros st HS. exists Vnull. apply astar_l_apure_intro;[ |reflexivity].
 destruct n;cbn[V293_tcb_free_chain];apply astar_r_aemp_intro;exact HS.
Qed.
Lemma FPOnePool : forall ie cs,FPState FPSharedOne ie cs |= V293_tcb_free_pool 401%positive.
Proof.
 intros ie cs. exists FPNext. apply astar_l_apure_intro;[ |reflexivity].
 eapply FPStar with(m1:=FPHeadMemory FPNext)(m2:=FPNodeMemory 502%positive Vnull).
 - apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 401%positive);[subst b;right;left|left];
   unfold FPHeadMemory,FPNodeMemory,FPPayloadMemory,FPPayloadRows,V293_tcb_free_payload_cells,FPNextMemory,FPBytes;
   cbn[map FPMemory];FPOutside.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - apply FPOneChainSpatial.
Qed.
Theorem FPSameInvariantChangedTail : forall ie cs,
 FPState FPSharedOne ie cs |= invlth_isr FPInv 0 INUM.
Proof.
 intros. unfold invlth_isr;rewrite Nat.sub_0_r.
 apply V293_shared_clear_noisr_close;[reflexivity| ].
 apply FPNoisrCore. apply FPOnePool.
Qed.
Lemma FPLoadJoin : forall tp M1 M2 M a v,
 join M1 M2 M -> load tp M1 a=Some v -> load tp M a=Some v.
Proof. intros. rewrite(@load_mono M1 M2 M tp a v H H0). exact H0. Qed.
Definition FPPopInput := merge(FPCaller FPHead(Vint32 Int.zero))FPSharedTwo.
Lemma FPHeadSplit : exists M1 M2,
 mapstoval(401%positive,0%Z)(Tptr V293_tcb_type)true FPHead M1 /\ join M1 M2 FPPopInput.
Proof.
 assert(H:FPState FPPopInput false[true] |=
 Amapsto(401%positive,0%Z)(Tptr V293_tcb_type)true FPHead ** Atrue).
 { pose proof(FPActualPopInput nil)as H. unfold V293_tcb_free_critical,V293_tcb_enabled_resources in H.
   clear -H;sep auto. }
 apply sat_split in H. destruct H as(m1&m2&o1&o2&JM&JO&HM&HQ).
 exists m1. exists m2. split;[exact(proj1 HM)|exact JM].
Qed.
Lemma FPActualHeadRead : load(Tptr V293_tcb_type)FPPopInput(401%positive,0%Z)=Some FPHead.
Proof.
 destruct FPHeadSplit as(m1&m2&HM&J).
 eapply FPLoadJoin;[exact J|eapply mapstoval_load;[reflexivity|exact HM]].
Qed.
Lemma FPActualNextRead : load(Tcom_ptr 410%Z)FPPopInput(501%positive,20%Z)=Some FPNext.
Proof.
 assert(L:load(Tcom_ptr 410%Z)(FPNodeMemory 501%positive FPNext)(501%positive,20%Z)=Some FPNext).
 { pose proof(FPNodeSpatial 501%positive FPNext false nil)as H.
   unfold V293_tcb_free_node in H.
   refine(@V293_star_load_l (Amapsto(501%positive,20%Z)(Tcom_ptr 410%Z)true FPNext)Atrue
     (Tcom_ptr 410%Z)(501%positive,20%Z)FPNext _ (FPState(FPNodeMemory 501%positive FPNext)false nil) _).
   - intros st[HM _]. eapply mapstoval_load;[reflexivity|exact HM].
   - clear -H;sep auto. }
 assert(J1:join(FPNodeMemory 501%positive FPNext)(FPNodeMemory 502%positive Vnull)FPChainMemory).
 { apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 501%positive);[subst b;right;left|left];
   unfold FPNodeMemory,FPPayloadMemory,FPPayloadRows,V293_tcb_free_payload_cells,FPNextMemory;
   cbn[map FPMemory];FPOutside. }
 assert(J2:join(FPHeadMemory FPHead)FPChainMemory FPSharedTwo).
 { apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 401%positive);[subst b;right;left|left];
   unfold FPHeadMemory,FPChainMemory,FPNodeMemory,FPPayloadMemory,FPPayloadRows,V293_tcb_free_payload_cells,FPNextMemory,FPBytes;
   cbn[map FPMemory];FPOutside. }
 assert(L1:load(Tcom_ptr 410%Z)FPChainMemory(501%positive,20%Z)=Some FPNext).
 { eapply FPLoadJoin;[exact J1|exact L]. }
 assert(L2:load(Tcom_ptr 410%Z)FPSharedTwo(501%positive,20%Z)=Some FPNext).
 { eapply FPLoadJoin;[apply map_join_comm;exact J2|exact L1]. }
 eapply FPLoadJoin;[apply map_join_comm;apply FPWholePartition with(present:=true)|exact L2].
Qed.
Definition FPHeadWrite := store(Tptr V293_tcb_type)FPPopInput(401%positive,0%Z)FPNext.
Lemma FPWrittenHeadRead :
 (match FPHeadWrite with Some M=>load(Tptr V293_tcb_type)M(401%positive,0%Z)|None=>None end)=Some FPNext.
Proof.
 destruct FPHeadSplit as(m1&m2&HM&J).
 destruct(@store_exist_join' (401%positive,0%Z)(Tptr V293_tcb_type)FPHead FPNext m1 m2 FPPopInput HM J)as(M'&S).
 unfold FPHeadWrite. rewrite S.
 destruct(@store_mapstoval_frame1 m1 m2 FPPopInput M' (401%positive,0%Z)(Tptr V293_tcb_type)FPHead FPNext HM J S)as(m1'&HM'&S'&J').
 eapply FPLoadJoin;[exact J'|eapply mapstoval_load;[reflexivity|exact HM']].
Qed.
Theorem FPTailNoPoppedBytes : forall off,get FPSharedOne(501%positive,off)=None.
Proof.
 intro off. unfold FPSharedOne,FPHeadMemory,FPNodeMemory,FPPayloadMemory,FPPayloadRows,V293_tcb_free_payload_cells,FPNextMemory,FPBytes.
 cbn[map FPMemory];FPOutside.
Qed.
Theorem FPOmittedWriteDiffers :
 load(Tptr V293_tcb_type)FPPopInput(401%positive,0%Z)<>Some FPNext.
Proof. rewrite FPActualHeadRead. discriminate. Qed.
Print Assumptions FPPopTransferChecked.
Print Assumptions FPSameInvariantChangedTail.
