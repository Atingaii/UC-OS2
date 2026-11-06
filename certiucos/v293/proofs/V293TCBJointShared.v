(* One physical ownership boundary for all three OS_TCBInit borrows.
   This is not yet the semantic/task-map kernel invariant. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteAllocator.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBFinitePool.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitChain.
Require Import CertiOS.certiucos.v293.proofs.V293InitMisc.
Require Import CertiOS.certiucos.v293.code.V293OSInitChain.
Require Import CertiOS.certiucos.v293.code.V293OSInitRdyList.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBCall.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TCBAllocatedFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEnabledHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFullPriority.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteSites.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublicationPool.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEnabledPublication.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFreePool.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReservationOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Coq.Sorting.Permutation Lia.
Import ListNotations.
Local Open Scope nat_scope.

Fixpoint V293_priority_slots table reserved (indices:list nat) : asrt :=
 match indices with
 | []=>Aemp
 | p::rest=>V293_reservation_pool(table,(4*Z.of_nat p)%Z)reserved **
             V293_priority_slots table reserved rest
 end.
Definition V293_priority_table table reserved :=
 V293_priority_slots table reserved(seq 0 13).
Definition V293_priority_rest table reserved p :=
 V293_priority_slots table reserved(firstn p(seq 0 13)++skipn(S p)(seq 0 13)).
Lemma V293_priority_slots_precise : forall indices table reserved,
 precise(V293_priority_slots table reserved indices).
Proof.
 induction indices;intros;cbn[V293_priority_slots].
 - exact(V293_storage_precise nil).
 - apply precise_star;[apply V293_reservation_pool_precise|apply IHindices].
Qed.
Lemma V293_priority_slots_good : forall indices table reserved,
 GoodInvAsrt(V293_priority_slots table reserved indices).
Proof. induction indices;intros;cbn[V293_priority_slots GoodInvAsrt];auto using V293_reservation_pool_good. Qed.
Lemma V293_priority_slots_aux_stable : forall indices table reserved ge le M ir aux O op ir' aux',
 (ge,le,M,ir,aux,O,op) |= V293_priority_slots table reserved indices ->
 (ge,le,M,ir',aux',O,op) |= V293_priority_slots table reserved indices.
Proof.
 induction indices;intros;cbn[V293_priority_slots]in H|-*;[exact H| ].
 apply sat_split in H. destruct H as(m1&m2&o1&o2&JM&JO&HP&HR).
 apply sat_split'. exists m1. exists m2. exists o1. exists o2. split;[exact JM| ]. split;[exact JO| ].
 split;[exact HP|eapply IHindices;exact HR].
Qed.
Lemma V293_priority_select_list : forall indices n p table reserved,
 nth_error indices n=Some p ->
 V293_priority_slots table reserved indices <==>
 V293_reservation_pool(table,(4*Z.of_nat p)%Z)reserved **
 V293_priority_slots table reserved(firstn n indices++skipn(S n)indices).
Proof.
 induction indices as[ |a indices IH];intros[ |n]p table reserved E s;try discriminate.
 - cbn in E;inversion E;subst p. reflexivity.
 - cbn[nth_error]in E. specialize(IH n p table reserved E).
   cbn[V293_priority_slots firstn skipn app]. split;intro H.
   + eapply astar_mono in H;[ |intros st HS;exact HS|intros st HS;exact(proj1(IH st)HS)]. clear -H;sep auto.
   + assert(K:s |= V293_reservation_pool(table,(4*Z.of_nat a)%Z)reserved **
       (V293_reservation_pool(table,(4*Z.of_nat p)%Z)reserved **
        V293_priority_slots table reserved(firstn n indices++skipn(S n)indices)))by(clear -H;sep auto).
     eapply astar_mono;[intros st HS;exact HS|intros st HS;exact(proj2(IH st)HS)|exact K].
Qed.
Theorem V293_priority_table_select : forall table reserved p,
 p<13 -> V293_priority_table table reserved <==>
 V293_reservation_pool(table,(4*Z.of_nat p)%Z)reserved ** V293_priority_rest table reserved p.
Proof.
 intros table reserved p Bound. unfold V293_priority_table,V293_priority_rest.
 apply V293_priority_select_list.
 rewrite <- (@seq_nth 13 0 p 0 Bound) at 2.
 apply nth_error_nth';rewrite seq_length;exact Bound.
Qed.

(* The count and head are read from common physical memory when comparing
   fragments. Existential chain lengths cannot be chosen independently. *)
Lemma V293_tcb_active_chain_precise : forall n prev head,
 precise(V293_tcb_active_chain n prev head).
Proof.
 induction n as[ |n IH];intros prev head.
 - intros s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
   destruct s as [[[[[[ge le] mem] ir] aux] o] op].
   change(head=Vnull /\ M1=emp /\ O1=emp)in H1.
   change(head=Vnull /\ M2=emp /\ O2=emp)in H2. intuition congruence.
 - destruct head;try(intros s M1 M2 O1 O2 H;contradiction). destruct a.
   cbn[V293_tcb_active_chain]. apply V293_tcb_pure_precise.
   apply precise_star;[apply V293_storage_precise| ].
   apply V293_tcb_value_tail_precise. intro next.
   apply precise_star;[apply V293_tcb_mapsto_precise|apply IH].
Qed.
Lemma V293_byteval_injective_bounded : forall n m,
 n<256 -> m<256 -> V293_byteval n=V293_byteval m -> n=m.
Proof.
 intros n m N M E. unfold V293_byteval in E. inversion E as[Bits].
 change(Int.unsigned(Int.repr(Z.of_nat n))=Int.unsigned(Int.repr(Z.of_nat m)))in Bits.
 repeat rewrite Int.unsigned_repr in Bits by(unfold Int.max_unsigned,Int.modulus,Int.wordsize;simpl;lia).
 lia.
Qed.
Lemma V293_count_tail_precise : forall a (tail:nat->asrt),
 (forall n,precise(tail n)) ->
 precise(EX n:nat,[|n<256|] ** (Amapsto a Tint8 true(V293_byteval n) ** tail n)).
Proof.
 intros a tail Prec s M1 M2 O1 O2 [n H1][m H2] M O HM1 HM2 HO1 HO2.
 apply astar_l_apure_elim in H1. destruct H1 as[N H1].
 apply astar_l_apure_elim in H2. destruct H2 as[B H2].
 destruct s as [[[[[[ge le] mem] ir] aux] o] op].
 assert(L1:load Tint8 M1 a=Some(V293_byteval n)).
 { refine(@V293_star_load_l _ _ Tint8 a _ _ (substmo(ge,le,mem,ir,aux,o,op)M1 O1)H1).
   intros st[H _]. eapply mapstoval_load;[apply V293_byte_type;exact N|exact H]. }
 assert(L2:load Tint8 M2 a=Some(V293_byteval m)).
 { refine(@V293_star_load_l _ _ Tint8 a _ _ (substmo(ge,le,mem,ir,aux,o,op)M2 O2)H2).
   intros st[H _]. eapply mapstoval_load;[apply V293_byte_type;exact B|exact H]. }
 pose proof(@load_mem_mono _ _ _ _ _ L1 HM1)as LM1.
 pose proof(@load_mem_mono _ _ _ _ _ L2 HM2)as LM2.
 assert(n=m)by(eapply V293_byteval_injective_bounded;[exact N|exact B|congruence]). subst m.
 eapply(precise_star _ _ (V293_tcb_mapsto_precise a Tint8(V293_byteval n))(Prec n));eauto.
Qed.
Definition V293_publication_envelope bh bg br bn y :=
 EX n:nat,[|n<256|] **
 (Amapsto(bn,0%Z)Tint8 true(V293_byteval n) **
 (EX head:val,[|rule_type_val_match(Tptr V293_tcb_type)head=true|] **
 (Amapsto(bh,0%Z)(Tptr V293_tcb_type)true head **
 (V293_storage ([((bg,0%Z),Tint8);((br,Z.of_nat y),Tint8);((br,Z.of_nat(1-y)),Tint8)]) **
 V293_tcb_active_chain n Vnull head)))).
Lemma V293_publication_envelope_precise : forall bh bg br bn y,
 precise(V293_publication_envelope bh bg br bn y).
Proof.
 intros. apply V293_count_tail_precise. intro n.
 apply V293_tcb_value_tail_precise. intro head.
 apply precise_star;[apply V293_storage_precise|apply V293_tcb_active_chain_precise].
Qed.
Lemma V293_publication_shared_envelope : forall bh bg br bn y,
 V293_tcb_publication_shared bh bg br bn y ==> V293_publication_envelope bh bg br bn y.
Proof.
 intros bh bg br bn y s(present&k&bo&obase&g&row&other&H).
 apply astar_l_apure_elim in H. destruct H as[[Base[Bound[G[Row[Other Count]]]]]H].
 unfold V293_publication_envelope. exists(if present then S k else 0).
 apply astar_l_apure_intro;[ |exact Count].
 assert(T:rule_type_val_match(Tptr V293_tcb_type)(V293_pub_old_head present bo obase)=true)
 by(destruct present;reflexivity).
 pose proof(V293_byte_type g G)as Tg. pose proof(V293_byte_type row Row)as Tr.
 pose proof(V293_byte_type other Other)as To.
 unfold V293_tcb_publication_pool in H. unfold V293_storage,V293_storage_cell.
 sep normal. exists(V293_pub_old_head present bo obase). exists(V293_byteval g). exists(V293_byteval row). exists(V293_byteval other).
 clear -H T Tg Tr To;sep auto.
Qed.
Theorem V293_tcb_finite_shared_precise : forall bt bh bg br bn y,
 precise(V293_tcb_finite_shared bt bh bg br bn y).
Proof.
 intros bt bh bg br bn y s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 apply V293_tcb_finite_shared_forget in H1,H2.
 apply V293_publication_shared_envelope in H1,H2.
 eapply V293_publication_envelope_precise;eauto.
Qed.
Lemma V293_indexed_chain_good : forall nodes prev head,
 GoodInvAsrt(V293_tcb_indexed_chain nodes prev head).
Proof.
 induction nodes as[ |[b off]nodes IH];intros;cbn[V293_tcb_indexed_chain GoodInvAsrt];[exact I| ].
 split;[exact I| ]. split;[apply V293_storage_good| ]. intro next.
 split;[exact I| ]. split;[exact I| ]. split;[exact I|apply IH].
Qed.
Lemma V293_tcb_finite_shared_good : forall bt bh bg br bn y,
 GoodInvAsrt(V293_tcb_finite_shared bt bh bg br bn y).
Proof.
 intros. unfold V293_tcb_finite_shared. intros present tail bo obase g row other.
 cbn[GoodInvAsrt]. split;[exact I| ]. unfold V293_tcb_indexed_pool.
 cbn[GoodInvAsrt]. repeat split;try exact I. apply V293_indexed_chain_good.
Qed.
Lemma V293_indexed_chain_aux_stable : forall nodes prev head ge le M ir aux O op ir' aux',
 (ge,le,M,ir,aux,O,op) |= V293_tcb_indexed_chain nodes prev head ->
 (ge,le,M,ir',aux',O,op) |= V293_tcb_indexed_chain nodes prev head.
Proof.
 induction nodes as[ |[b off]nodes IH];intros;cbn[V293_tcb_indexed_chain]in H|-*;[exact H| ].
 apply astar_l_apure_elim in H. destruct H as[Bound H].
 apply astar_l_apure_intro;[ |exact Bound].
 apply sat_split in H. destruct H as(m1&m2&o1&o2&JM&JO&HP&next&HN).
 apply sat_split'. exists m1. exists m2. exists o1. exists o2. split;[exact JM| ]. split;[exact JO| ]. split.
 - eapply V293_storage_aux_stable;exact HP.
 - exists next. apply astar_l_apure_elim in HN. destruct HN as[Typed HN].
   apply astar_l_apure_intro;[ |exact Typed].
   apply sat_split in HN. destruct HN as(m3&m4&o3&o4&JM2&JO2&HN&HR).
   apply sat_split'. exists m3. exists m4. exists o3. exists o4. split;[exact JM2| ]. split;[exact JO2| ]. split;[exact HN| ].
   apply sat_split in HR. destruct HR as(m5&m6&o5&o6&JM3&JO3&HPrev&HT).
   apply sat_split'. exists m5. exists m6. exists o5. exists o6. split;[exact JM3| ]. split;[exact JO3| ]. split;[exact HPrev|eapply IH;exact HT].
Qed.
Lemma V293_indexed_pool_aux_stable : forall bh bg br bn y nodes head g row other ge le M ir aux O op ir' aux',
 (ge,le,M,ir,aux,O,op) |= V293_tcb_indexed_pool bh bg br bn y nodes head g row other ->
 (ge,le,M,ir',aux',O,op) |= V293_tcb_indexed_pool bh bg br bn y nodes head g row other.
Proof.
 intros. unfold V293_tcb_indexed_pool in H|-*.
 do 5(let m1:=fresh "m1" in let m2:=fresh "m2" in
  let o1:=fresh "o1" in let o2:=fresh "o2" in
  let JM:=fresh "JM" in let JO:=fresh "JO" in let HP:=fresh "HP" in
  apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&HP&H);
  apply sat_split';exists m1;exists m2;exists o1;exists o2;
  split;[exact JM| ];split;[exact JO| ];split;[exact HP| ]).
 eapply V293_indexed_chain_aux_stable;exact H.
Qed.
Lemma V293_tcb_finite_shared_aux_stable : forall bt bh bg br bn y ge le M ir aux O op ir' aux',
 (ge,le,M,ir,aux,O,op) |= V293_tcb_finite_shared bt bh bg br bn y ->
 (ge,le,M,ir',aux',O,op) |= V293_tcb_finite_shared bt bh bg br bn y.
Proof.
 intros bt bh bg br bn y ge le M ir aux O op ir' aux'(present&tail&bo&obase&g&row&other&H).
 exists present. exists tail. exists bo. exists obase. exists g. exists row. exists other.
 apply astar_l_apure_elim in H. destruct H as[Bound H]. apply astar_l_apure_intro;[ |exact Bound].
 eapply V293_indexed_pool_aux_stable;exact H.
Qed.
Lemma V293_tcb_finite_shared_isr : forall bt bh bg br bn y,
 assertion.inv_isr_prop(V293_tcb_finite_shared bt bh bg br bn y).
Proof.
 intros. unfold assertion.inv_isr_prop. repeat split;intros;
 destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];
 eapply V293_tcb_finite_shared_aux_stable;exact H.
Qed.
Lemma V293_tcb_finite_shared_row_swap : forall bt bh bg br bn,
 V293_tcb_finite_shared bt bh bg br bn 0 <==> V293_tcb_finite_shared bt bh bg br bn 1.
Proof.
 intros bt bh bg br bn s. split;intros(present&tail&bo&obase&g&row&other&H);
 exists present;exists tail;exists bo;exists obase;exists g;exists other;exists row;
 unfold V293_tcb_indexed_pool in *;cbn[Nat.sub Z.of_nat]in *;clear -H;sep auto;tauto.
Qed.
Lemma V293_tcb_finite_shared_row : forall bt bh bg br bn y,
 y<2 -> V293_tcb_finite_shared bt bh bg br bn 0 <==> V293_tcb_finite_shared bt bh bg br bn y.
Proof. intros bt bh bg br bn[ |[ |y]]Bound;try lia;[reflexivity|apply V293_tcb_finite_shared_row_swap]. Qed.

Section JointShared.
Variables(bt bf table bh bg br bn:block)(reserved:addrval).
Definition V293_tcb_joint_core :=
 V293_tcb_site_free_pool bt bf **
 (V293_priority_table table reserved ** V293_tcb_finite_shared bt bh bg br bn 0).
Definition V293_tcb_joint_free_rest :=
 V293_priority_table table reserved ** V293_tcb_finite_shared bt bh bg br bn 0.
Definition V293_tcb_joint_priority_rest p :=
 V293_tcb_site_free_pool bt bf **
 (V293_priority_rest table reserved p ** V293_tcb_finite_shared bt bh bg br bn 0).
Definition V293_tcb_joint_publication_rest :=
 V293_tcb_site_free_pool bt bf ** V293_priority_table table reserved.
Lemma V293_tcb_joint_core_good : GoodInvAsrt V293_tcb_joint_core.
Proof.
 unfold V293_tcb_joint_core. cbn[GoodInvAsrt]. split;[apply V293_tcb_site_free_pool_good| ].
 split;[apply V293_priority_slots_good|apply V293_tcb_finite_shared_good].
Qed.
Lemma V293_tcb_joint_core_precise : precise V293_tcb_joint_core.
Proof.
 unfold V293_tcb_joint_core. apply precise_star;[apply V293_tcb_site_free_pool_precise| ].
 apply precise_star;[apply V293_priority_slots_precise|apply V293_tcb_finite_shared_precise].
Qed.
Lemma V293_tcb_joint_core_aux_stable : forall ge le M ir aux O op ir' aux',
 (ge,le,M,ir,aux,O,op) |= V293_tcb_joint_core ->
 (ge,le,M,ir',aux',O,op) |= V293_tcb_joint_core.
Proof.
 intros. apply sat_split in H. destruct H as(m1&m2&o1&o2&JM&JO&HF&HR).
 apply sat_split'. exists m1. exists m2. exists o1. exists o2. split;[exact JM| ]. split;[exact JO| ]. split.
 - eapply V293_tcb_site_free_pool_aux_stable;exact HF.
 - apply sat_split in HR. destruct HR as(m3&m4&o3&o4&JM2&JO2&HP&HA).
   apply sat_split'. exists m3. exists m4. exists o3. exists o4. split;[exact JM2| ]. split;[exact JO2| ]. split.
   + eapply V293_priority_slots_aux_stable;exact HP.
   + eapply V293_tcb_finite_shared_aux_stable;exact HA.
Qed.
Lemma V293_tcb_joint_core_isr : assertion.inv_isr_prop V293_tcb_joint_core.
Proof.
 unfold assertion.inv_isr_prop. repeat split;intros;
 destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];
 eapply V293_tcb_joint_core_aux_stable;exact H.
Qed.
Definition V293_tcb_joint_inv : Inv := fun i=>match i with
 | O=>mkinvasrt V293_tcb_joint_core_good(conj V293_tcb_joint_core_precise V293_tcb_joint_core_isr)
 | S j=>V293_shared_inv(S j) end.
Lemma V293_tcb_joint_noisr_tail : forall n i,
 starinv_noisr V293_tcb_joint_inv(S i)n <==> Aemp.
Proof.
 induction n;intros i s;cbn[starinv_noisr];[reflexivity| ].
 change(s |= Aemp ** starinv_noisr V293_tcb_joint_inv(S(S i))n <-> s |= Aemp).
 split;intro H.
 - apply astar_l_aemp_elim in H. apply IHn in H;exact H.
 - apply astar_l_aemp_intro. apply IHn;exact H.
Qed.
Lemma V293_tcb_joint_noisr_core : forall n,
 starinv_noisr V293_tcb_joint_inv 0 n <==> V293_tcb_joint_core.
Proof.
 intros[ |n]s;[reflexivity| ].
 change(s |= V293_tcb_joint_core ** starinv_noisr V293_tcb_joint_inv 1 n <-> s |= V293_tcb_joint_core).
 split;intro H.
 - apply astar_r_aemp_elim. eapply astar_mono;[intros st HS;exact HS|intros st HS;apply V293_tcb_joint_noisr_tail in HS;exact HS|exact H].
 - eapply astar_mono;[intros st HS;exact HS|intros st HS;apply V293_tcb_joint_noisr_tail;exact HS| ]. apply astar_r_aemp_intro;exact H.
Qed.
Theorem V293_tcb_joint_borrow : forall n,
 Aisr(fun _=>false) ** invlth_isr V293_tcb_joint_inv 0 n <==>
 Aisr(fun _=>false) ** V293_tcb_joint_core.
Proof.
 intros n s. destruct s as [[[[[[ge le] M] ir] aux] O] op]. split;intro H.
 all: (apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&H1&H2);
 destruct H1 as[E Empty];cbn in E;subst ir;
 apply sat_split';exists m1;exists m2;exists o1;exists o2;
 split;[exact JM| ];split;[exact JO| ];split;[split;[reflexivity|exact Empty]| ]).
 - unfold invlth_isr in H2. rewrite Nat.sub_0_r in H2.
   apply V293_tcb_joint_noisr_core with(n:=n). eapply invisr_imply_noisr';[ |exact H2]. reflexivity.
 - unfold invlth_isr. rewrite Nat.sub_0_r.
   apply V293_shared_clear_noisr_close;[reflexivity| ]. apply V293_tcb_joint_noisr_core;exact H2.
Qed.
Theorem V293_tcb_joint_borrow_free : forall n,
 Aisr(fun _=>false) ** invlth_isr V293_tcb_joint_inv 0 n <==>
 Aisr(fun _=>false) ** (V293_tcb_site_free_pool bt bf ** V293_tcb_joint_free_rest).
Proof. apply V293_tcb_joint_borrow. Qed.
Theorem V293_tcb_joint_priority_view : forall p,p<13 ->
 V293_tcb_joint_core <==> V293_create_owned_pool table reserved p(V293_tcb_joint_priority_rest p).
Proof.
 intros p Bound s. pose proof(V293_priority_table_select table reserved p Bound)as Select.
 unfold V293_tcb_joint_core,V293_create_owned_pool,V293_tcb_joint_priority_rest. split;intro H.
 - assert(K:s |= V293_priority_table table reserved **
     (V293_tcb_site_free_pool bt bf ** V293_tcb_finite_shared bt bh bg br bn 0))by(clear -H;sep auto).
   eapply astar_mono in K;[ |intros st HS;exact(proj1(Select st)HS)|intros st HS;exact HS]. clear -K;sep auto.
 - assert(K:s |= (V293_reservation_pool(table,(4*Z.of_nat p)%Z)reserved ** V293_priority_rest table reserved p) **
     (V293_tcb_site_free_pool bt bf ** V293_tcb_finite_shared bt bh bg br bn 0))by(clear -H;sep auto).
   eapply astar_mono in K;[ |intros st HS;exact(proj2(Select st)HS)|intros st HS;exact HS]. clear -K;sep auto.
Qed.
Theorem V293_tcb_joint_borrow_priority : forall n p,p<13 ->
 Aisr(fun _=>false) ** invlth_isr V293_tcb_joint_inv 0 n <==>
 Aisr(fun _=>false) ** V293_create_owned_pool table reserved p(V293_tcb_joint_priority_rest p).
Proof.
 intros n p Bound s. pose proof(V293_tcb_joint_borrow n s)as Borrow.
 pose proof(V293_tcb_joint_priority_view p Bound)as View. split;intro H.
 - apply Borrow in H. eapply astar_mono;[intros st HS;exact HS|intros st HS;exact(proj1(View st)HS)|exact H].
 - apply Borrow. eapply astar_mono;[intros st HS;exact HS|intros st HS;exact(proj2(View st)HS)|exact H].
Qed.
Theorem V293_tcb_joint_publication_view : forall y,y<2 ->
 V293_tcb_joint_core <==> V293_tcb_finite_shared bt bh bg br bn y ** V293_tcb_joint_publication_rest.
Proof.
 intros y Bound s. pose proof(V293_tcb_finite_shared_row bt bh bg br bn y Bound)as Row.
 unfold V293_tcb_joint_core,V293_tcb_joint_publication_rest. split;intro H.
 - assert(K:s |= V293_tcb_finite_shared bt bh bg br bn 0 **
     (V293_tcb_site_free_pool bt bf ** V293_priority_table table reserved))by(clear -H;sep auto).
   eapply astar_mono;[intros st HS;exact(proj1(Row st)HS)|intros st HS;exact HS|exact K].
 - eapply astar_mono in H;[ |intros st HS;exact(proj2(Row st)HS)|intros st HS;exact HS]. clear -H;sep auto.
Qed.
Theorem V293_tcb_joint_borrow_publication : forall n y,y<2 ->
 Aisr(fun _=>false) ** invlth_isr V293_tcb_joint_inv 0 n <==>
 Aisr(fun _=>false) ** (V293_tcb_finite_shared bt bh bg br bn y ** V293_tcb_joint_publication_rest).
Proof.
 intros n y Bound s. pose proof(V293_tcb_joint_borrow n s)as Borrow.
 pose proof(V293_tcb_joint_publication_view y Bound)as View. split;intro H.
 - apply Borrow in H. eapply astar_mono;[intros st HS;exact HS|intros st HS;exact(proj1(View st)HS)|exact H].
 - apply Borrow. eapply astar_mono;[intros st HS;exact HS|intros st HS;exact(proj2(View st)HS)|exact H].
Qed.
End JointShared.

Definition V293_tcb_joint_ready_cells bg br bn : list V293_record_cell :=
 [((bg,0%Z),Tint8,V293_byteval 0);((br,0%Z),Tint8,V293_byteval 0);
  ((br,1%Z),Tint8,V293_byteval 0);((bn,0%Z),Tint8,V293_byteval 0)].
Lemma V293_priority_null_slots : forall n start table reserved R,
 V293_rdy_raw_cells(V293_null_pointer_cells table(4*Z.of_nat start)%Z n)R ==>
 V293_priority_slots table reserved(seq start n) ** R.
Proof.
 induction n as[ |n IH];intros start table reserved R s H.
 - cbn[V293_null_pointer_cells V293_rdy_raw_cells seq V293_priority_slots]in *;clear -H;sep auto.
 - cbn[V293_null_pointer_cells V293_rdy_raw_cells seq V293_priority_slots]in *.
   assert(Offset:(4*Z.of_nat start+4=4*Z.of_nat(S start))%Z)by lia. rewrite Offset in H.
   eapply astar_mono in H;[ |apply V293_reservation_pool_null|apply IH]. clear -H;sep auto.
Qed.
Lemma V293_tcb_joint_empty_publication : forall bt bh bg br bn R,
 Amapsto(bh,0%Z)(Tptr V293_tcb_type)true Vnull **
 V293_rdy_raw_cells(V293_tcb_joint_ready_cells bg br bn)R ==>
 V293_tcb_finite_shared bt bh bg br bn 0 ** R.
Proof.
 intros bt bh bg br bn R s H. unfold V293_tcb_finite_shared. sep normal.
 exists false. exists(@nil tid). exists bt. exists 0%Z. exists 0. exists 0. exists 0.
 unfold V293_tcb_indexed_pool,V293_tcb_old_sites,V293_pub_old_head,V293_tcb_indexed_chain,
 V293_tcb_joint_ready_cells,V293_tcb_sites_valid in *.
 cbn[V293_rdy_raw_cells length Z.of_nat Nat.sub]in *.
 clear -H;sep auto. repeat split;try lia;try apply NoDup_nil;try(intros x Bad;contradiction).
 unfold Int.max_unsigned,Int.modulus,Int.wordsize;simpl;lia.
Qed.
Theorem V293_tcb_call_result_joint : forall bt bf table bh bg br bn reserved frame,
 V293_rdy_raw_cells(V293_tcb_call_result bh bf bt table
   (V293_tcb_joint_ready_cells bg br bn++frame))Atrue ==>
 V293_tcb_joint_core bt bf table bh bg br bn reserved ** V293_rdy_raw_cells frame Atrue.
Proof.
 intros bt bf table bh bg br bn reserved frame s H.
 apply V293_tcb_call_result_pool in H. unfold V293_init_tcb_pool_rest in H.
 repeat rewrite V293_raw_cells_append in H.
 assert(Fold:V293_rdy_raw_cells(V293_null_pointer_cells table 0 13)
  (V293_rdy_raw_cells(V293_tcb_joint_ready_cells bg br bn)(V293_rdy_raw_cells frame Atrue)) ==>
  V293_priority_table table reserved **
  V293_rdy_raw_cells(V293_tcb_joint_ready_cells bg br bn)(V293_rdy_raw_cells frame Atrue)).
 { exact(V293_priority_null_slots 13 0 table reserved _). }
 eapply astar_mono in H;[ |intros st HS;exact HS| ].
 2:{ apply astar_mono;[intros st HS;exact HS|exact Fold]. }
 assert(K:s |= V293_priority_table table reserved **
  (V293_tcb_site_free_pool bt bf **
   (Amapsto(bh,0%Z)(Tptr V293_tcb_type)true Vnull **
    V293_rdy_raw_cells(V293_tcb_joint_ready_cells bg br bn)(V293_rdy_raw_cells frame Atrue))))by(clear -H;sep auto).
 eapply astar_mono in K;[ |intros st HS;exact HS| ].
 2:{ apply astar_mono;[intros st HS;exact HS|apply V293_tcb_joint_empty_publication]. }
 unfold V293_tcb_joint_core. clear -K;sep auto.
Qed.

(* Original complete AST, now with all six resource-view premises discharged.
   Hook contracts, token freshness and final return obligations stay explicit. *)
Theorem V293_OS_TCBInit_joint_shared : forall Spec sd li r tid hi hc tcbtable
 table reserved bf bp bc pc cpu bh bg br bn bprio bs bb bi bz be bo p top bottom identity size ext options R aop si ci
 (good:GoodFunAsrt(V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))),
 p<13 -> (gettopis si<=INUM)%nat -> GoodFrm R ->
 V293_tcb_init_values_valid top bottom identity size ext options -> (R ==> CurLINV li tid) ->
 Spec hi=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))aop (fun _=>false) si ci tid good,
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options
 (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))aop (fun _=>false) si ci tid good,(Tvoid,[Tptr V293_tcb_type])) ->
 Spec hc=Some(V293_tcb_enabled_hook_fpre p top bottom identity size ext options (V293_tcb_publication_globals bh bg br bn ** R) aop (fun _=>false) si ci tid (proj2 good),
 V293_tcb_enabled_hook_fpost p top bottom identity size ext options (V293_tcb_publication_globals bh bg br bn ** R) aop (fun _=>false) si ci tid (proj2 good),(Tvoid,[Tptr V293_tcb_type])) ->
 (V293_tcb_enabled_state bf bp bc Vnull(Vint32 Int.zero)
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))))aop (fun _=>false) si ci ==>
 r(Some(Vint32(Int.repr 66)))) ->
 (forall b off next s,
 s |= V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_initialized b off next p top bottom identity size ext options **
 V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))))aop (fun _=>false) si ci ->
 (b,off)<>reserved) ->
 (forall b off,
 V293_tcb_enabled_state bf bp bc(Vptr(b,off))(Vint32 Int.zero)
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_tcb_publication_globals bh bg br bn ** R)))aop (fun _=>false) si ci ==>
 r(Some(Vint32 Int.zero))) ->
 InfRules Spec sd li (V293_tcb_joint_inv tcbtable bf table bh bg br bn reserved) r Afalse
 (V293_tcb_enabled_state bf bp bc pc cpu
 (V293_tcb_allocated_inputs bp bprio bs bb bi bz be bo p top bottom identity size ext options
 (V293_tcb_table_binding table ** (V293_create_owned_share table reserved p ** (V293_tcb_publication_globals bh bg br bn ** R))))aop (fun _=>false) si ci)
 (V293_TCBInit_function_body hi hc)Afalse tid.
Proof.
 intros Spec sd li r tid hi hc tcbtable table reserved bf bp bc pc cpu bh bg br bn bprio bs bb bi bz be bo p top bottom identity size ext options R aop si ci good Range Bound Frame Valid HR FirstLookup SecondLookup Empty Fresh Return.
 assert(Y:V293_prio_row p<2)by(unfold V293_prio_row;destruct(p <? 8);lia).
 eapply V293_OS_TCBInit_site_allocated_finite_published with
 (Kfree:=V293_tcb_joint_free_rest tcbtable table bh bg br bn reserved)
 (Kprio:=V293_tcb_joint_priority_rest tcbtable bf table bh bg br bn reserved p)
 (Kpub:=V293_tcb_joint_publication_rest tcbtable bf table reserved);try eassumption.
 - intros s H. exact(proj1(V293_tcb_joint_borrow_free tcbtable bf table bh bg br bn reserved (gettopis si)s)H).
 - intros s H. exact(proj2(V293_tcb_joint_borrow_free tcbtable bf table bh bg br bn reserved (gettopis si)s)H).
 - intros s H. exact(proj1(V293_tcb_joint_borrow_priority tcbtable bf table bh bg br bn reserved (gettopis si)p Range s)H).
 - intros s H. exact(proj2(V293_tcb_joint_borrow_priority tcbtable bf table bh bg br bn reserved (gettopis si)p Range s)H).
 - intros s H. exact(proj1(V293_tcb_joint_borrow_publication tcbtable bf table bh bg br bn reserved (gettopis si)(V293_prio_row p)Y s)H).
 - intros s H. exact(proj2(V293_tcb_joint_borrow_publication tcbtable bf table bh bg br bn reserved (gettopis si)(V293_prio_row p)Y s)H).
Qed.
Print Assumptions V293_OS_TCBInit_joint_shared.

Lemma V293_init_three_result_joint : forall slots d bt bf table bl bg br bn bpr bh btop bcur reserved frame,
 In d slots -> init_type d=Tint8 -> init_block d=bn ->
 V293_rdy_raw_cells(V293_tcb_call_result bl bf bt table
  (V293_rdy_globals bg br bpr bh btop bcur
   (Vint32 Int.zero)(Vint32 Int.zero)(Vint32 Int.zero)(Vint32 Int.zero)(Vint32 Int.zero)Vnull Vnull++
   V293_misc_zero_cells slots++frame))Atrue ==>
 V293_tcb_joint_core bt bf table bl bg br bn reserved ** V293_rdy_raw_cells frame Atrue.
Proof.
 intros slots d bt bf table bl bg br bn bpr bh btop bcur reserved frame Member Ty Bl s H.
 assert(C:In((bn,0%Z),Tint8,Vint32 Int.zero)(V293_misc_zero_cells slots)).
 { unfold V293_misc_zero_cells. apply in_map_iff. exists d. split;[rewrite Ty,Bl;reflexivity|exact Member]. }
 apply in_split in C. destruct C as(before&after&Order). rewrite Order in H.
 set(extra := ([((bpr,0%Z),Tint8,Vint32 Int.zero);((bh,0%Z),Tint8,Vint32 Int.zero);
   ((btop,0%Z),Tptr V293_tcb_type,Vnull);((bcur,0%Z),Tptr V293_tcb_type,Vnull)] : list V293_record_cell)).
 assert(OrderReady:Permutation
  (V293_rdy_globals bg br bpr bh btop bcur
   (Vint32 Int.zero)(Vint32 Int.zero)(Vint32 Int.zero)(Vint32 Int.zero)(Vint32 Int.zero)Vnull Vnull++
   (before++((bn,0%Z),Tint8,Vint32 Int.zero)::after)++frame)
  (V293_tcb_joint_ready_cells bg br bn++extra++before++after++frame)).
 { unfold V293_rdy_globals,V293_rdy_cells,V293_tcb_joint_ready_cells.
   cbn[firstn app]. apply perm_skip. apply perm_skip. apply perm_skip.
   change(Permutation (extra++(before++((bn,0%Z),Tint8,Vint32 Int.zero)::after)++frame)
    (((bn,0%Z),Tint8,Vint32 Int.zero)::(extra++before++after++frame))).
   replace (extra++(before++((bn,0%Z),Tint8,Vint32 Int.zero)::after)++frame)
    with ((extra++before)++((bn,0%Z),Tint8,Vint32 Int.zero)::(after++frame))
    by(repeat rewrite <-app_assoc;reflexivity).
   replace (extra++before++after++frame) with ((extra++before)++(after++frame))
    by(repeat rewrite <-app_assoc;reflexivity).
   apply Permutation_sym. apply Permutation_middle. }
 assert(OrderAll:Permutation
  (V293_tcb_call_result bl bf bt table
   (V293_rdy_globals bg br bpr bh btop bcur
    (Vint32 Int.zero)(Vint32 Int.zero)(Vint32 Int.zero)(Vint32 Int.zero)(Vint32 Int.zero)Vnull Vnull++
    (before++((bn,0%Z),Tint8,Vint32 Int.zero)::after)++frame))
  (V293_tcb_call_result bl bf bt table
   (V293_tcb_joint_ready_cells bg br bn++(extra++before++after++frame)))).
 { unfold V293_tcb_call_result. repeat apply Permutation_app_head. exact OrderReady. }
 pose proof(V293_raw_cells_permutation _ _ OrderAll Atrue s H)as Reordered.
 apply V293_tcb_call_result_joint with(reserved:=reserved)in Reordered.
 eapply astar_mono;[intros st HS;exact HS| |exact Reordered].
 intros st HS.
 replace (extra++before++after++frame) with ((extra++before++after)++frame) in HS
  by(repeat rewrite <-app_assoc;reflexivity).
 rewrite V293_raw_cells_append in HS.
 apply V293_raw_cells_separate in HS.
 apply V293_raw_cells_absorb in HS. exact HS.
Qed.

Theorem V293_OSInit_three_calls_joint : forall d bcount reserved slots oldtcbs oldprios frame P ks ge caller M ir aux O op
  misc ready tcbs clear dest size group rows prio high top current ri
  bg br bpr bh btop bcur table priorities list_head free_head ix ix_next ptcb1 ptcb2 bt bp bl bf
  vg vlo vhi vp vh vt vc vl vf,
  In d slots -> init_type d=Tint8 -> init_block d=bcount ->
  Forall V293_init_scalar slots ->
  P misc=Some (Tvoid,dnil,dnil,sseq (V293_init_program slots) sret) ->
  P ready=Some (V293_InitRdyList_function group rows prio high top current ri) ->
  P tcbs=Some (V293_InitTCBList_function clear table priorities list_head free_head ix ix_next ptcb1 ptcb2) ->
  P clear=Some (V293_MemClr_function dest size) -> dest<>size ->
  (ix<ix_next)%Z -> (ix_next<ptcb1)%Z -> (ptcb1<ptcb2)%Z ->
  (forall bi, V293_rdy_env ge (V293_rdy_locals ri bi)
    group rows prio high top current ri bg br bpr bh btop bcur bi) ->
  (forall bi bn b1 b2, V293_tcb_link_env ge (V293_tcb_call_locals ix ix_next ptcb1 ptcb2 bi bn b1 b2)
    table list_head free_head ix ix_next ptcb1 ptcb2 bt bl bf bi bn b1 b2) ->
  (forall bi bn b1 b2, get (V293_tcb_call_locals ix ix_next ptcb1 ptcb2 bi bn b1 b2) priorities=None) ->
  get ge priorities=Some (bp,V293_tcb_prio_table_type) ->
  length oldtcbs=728%nat -> length oldprios=52%nat ->
  (ge,emp,M,ir,aux,O,op) |= V293_init_resources slots false
    (V293_rdy_raw_cells
      (V293_rdy_globals bg br bpr bh btop bcur vg vlo vhi vp vh vt vc++
       V293_clr_bytes bt 0 oldtcbs++V293_clr_bytes bp 0 oldprios++V293_tcb_call_heads bl bf vl vf++frame) Atrue) ->
  exists (Mmisc Mrdy Mf:mem)(bri bi bn b1 b2:block),
    cstepstar P (curs (V293_init_three_calls misc ready tcbs),(kenil,ks)) (ge,caller,M)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    cstepstar P (curs (scall misc nil),(kenil,kseq (sseq (scall ready nil) (scall tcbs nil)) ks)) (ge,caller,M)
      (curs (sskip None),(kenil,kseq (sseq (scall ready nil) (scall tcbs nil)) ks)) (ge,caller,Mmisc) /\
    cstepstar P (curs (scall ready nil),(kenil,kseq (scall tcbs nil) ks)) (ge,caller,Mmisc)
      (curs (sskip None),(kenil,kseq (scall tcbs nil) ks)) (ge,caller,Mrdy) /\
    cstepstar P (curs (scall tcbs nil),(kenil,ks)) (ge,caller,Mrdy)
      (curs (sskip None),(kenil,ks)) (ge,caller,Mf) /\
    (ge,caller,Mf,ir,aux,O,op) |=
      V293_tcb_joint_core bt bf bp bl bg br bcount reserved ** V293_rdy_raw_cells frame Atrue /\
    get Mrdy (bri,0%Z)=None /\
    (forall c tp k, In (c,tp) [(bi,Tint8);(bn,Tint8);(b1,Tptr V293_tcb_type);(b2,Tptr V293_tcb_type)] ->
      (k<typelen tp)%nat -> get Mf (c,Z.of_nat k)=None).
Proof.
 intros d bcount reserved slots oldtcbs oldprios frame P ks ge caller M ir aux O op
  misc ready tcbs clear dest size group rows prio high top current ri
  bg br bpr bh btop bcur table priorities list_head free_head ix ix_next ptcb1 ptcb2 bt bp bl bf
  vg vlo vhi vp vh vt vc vl vf Member Ty Bl Scalar Misc Ready TCB Clear DS IX IN PN REnv CEnv NPrio GPrio LT LP Owned.
 destruct(V293_OSInit_three_calls slots oldtcbs oldprios frame P ks ge caller M ir aux O op
  misc ready tcbs clear dest size group rows prio high top current ri
  bg br bpr bh btop bcur table priorities list_head free_head ix ix_next ptcb1 ptcb2 bt bp bl bf
  vg vlo vhi vp vh vt vc vl vf Scalar Misc Ready TCB Clear DS IX IN PN REnv CEnv NPrio GPrio LT LP Owned)
  as(Mmisc&Mrdy&Mf&bri&bi&bn&b1&b2&Exec&EM&ER&ET&Final&FR&FT).
 exists Mmisc. exists Mrdy. exists Mf. exists bri. exists bi. exists bn. exists b1. exists b2.
 repeat split;try assumption.
 eapply V293_init_three_result_joint;[exact Member|exact Ty|exact Bl|exact Final].
Qed.
Print Assumptions V293_OSInit_three_calls_joint.
