(* A physical same-Inv fixture, not a production scheduler invariant.
   Whole enabled suffix still needs the explicitly quantified capacity premise. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.audit.probes.V293TCBPublicationPoolProbe.
Require Import CertiOS.audit.probes.V293TCBFreePoolProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEnabledPublication.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublicationPool.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublishHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFreePool.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Lemma PEChainPrecise : forall n prev head,precise(V293_tcb_active_chain n prev head).
Proof.
 induction n as[ |n IH];intros prev head.
 - intros s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
   destruct s as [[[[[[ge le] mem] ir] aux] o] op].
   change(head=Vnull /\ M1=emp /\ O1=emp)in H1.
   change(head=Vnull /\ M2=emp /\ O2=emp)in H2. intuition congruence.
 - destruct head;try(intros s M1 M2 O1 O2 H1;contradiction).
   destruct a. cbn[V293_tcb_active_chain]. apply V293_tcb_pure_precise.
   apply precise_star;[apply V293_storage_precise| ].
   apply V293_tcb_value_tail_precise. intro next.
   apply precise_star;[apply V293_tcb_mapsto_precise|apply IH].
Qed.
Lemma PEPoolPrecise : forall bh bg br bn y n head g row other,
 precise(V293_tcb_publication_pool bh bg br bn y n head g row other).
Proof.
 intros. unfold V293_tcb_publication_pool.
 repeat apply precise_star;try apply V293_tcb_mapsto_precise. apply PEChainPrecise.
Qed.
Lemma PEByteInjective : forall m n,m<256 -> n<256 -> V293_byteval m=V293_byteval n -> m=n.
Proof.
 intros m n M N E. unfold V293_byteval in E. inversion E as[Eq].
 change(Int.unsigned(Int.repr(Z.of_nat m))=Int.unsigned(Int.repr(Z.of_nat n)))in Eq. assert(B:(255<=Int.max_unsigned)%Z)by(vm_compute;congruence).
 rewrite !Int.unsigned_repr in Eq by lia. lia.
Qed.
Lemma PEPoolLoads : forall bh bg br bn y n head g row other s,
 n<256 -> g<256 -> row<256 -> other<256 -> rule_type_val_match(Tptr V293_tcb_type)head=true ->
 s |= V293_tcb_publication_pool bh bg br bn y n head g row other ->
 load(Tptr V293_tcb_type)(getmem s)(bh,0%Z)=Some head /\
 load Tint8(getmem s)(bg,0%Z)=Some(V293_byteval g) /\
 load Tint8(getmem s)(br,Z.of_nat y)=Some(V293_byteval row) /\
 load Tint8(getmem s)(br,Z.of_nat(1-y))=Some(V293_byteval other) /\
 load Tint8(getmem s)(bn,0%Z)=Some(V293_byteval n).
Proof.
 intros bh bg br bn y n head g row other s N G Row Other Typed H.
 repeat split.
 - eapply V293_star_load_l with(p:=Amapsto(bh,0%Z)(Tptr V293_tcb_type)true head)(q:=Atrue).
   + intros st[HS _]. eapply mapstoval_load;[exact Typed|exact HS].
   + unfold V293_tcb_publication_pool in H;clear -H;sep auto.
 - eapply V293_star_load_l with(p:=Amapsto(bg,0%Z)Tint8 true(V293_byteval g))(q:=Atrue).
   + intros st[HS _]. eapply mapstoval_load;[apply V293_byte_type;exact G|exact HS].
   + unfold V293_tcb_publication_pool in H;clear -H;sep auto.
 - eapply V293_star_load_l with(p:=Amapsto(br,Z.of_nat y)Tint8 true(V293_byteval row))(q:=Atrue).
   + intros st[HS _]. eapply mapstoval_load;[apply V293_byte_type;exact Row|exact HS].
   + unfold V293_tcb_publication_pool in H;clear -H;sep auto.
 - eapply V293_star_load_l with(p:=Amapsto(br,Z.of_nat(1-y))Tint8 true(V293_byteval other))(q:=Atrue).
   + intros st[HS _]. eapply mapstoval_load;[apply V293_byte_type;exact Other|exact HS].
   + unfold V293_tcb_publication_pool in H;clear -H;sep auto.
 - eapply V293_star_load_l with(p:=Amapsto(bn,0%Z)Tint8 true(V293_byteval n))(q:=Atrue).
   + intros st[HS _]. eapply mapstoval_load;[apply V293_byte_type;exact N|exact HS].
   + unfold V293_tcb_publication_pool in H;clear -H;sep auto.
Qed.
Lemma PESharedPrecise : forall bh bg br bn y,precise(V293_tcb_publication_shared bh bg br bn y).
Proof.
 intros bh bg br bn y s M1 M2 O1 O2
 (p1&k1&b1&base1&g1&r1&t1&H1)(p2&k2&b2&base2&g2&r2&t2&H2) M O HM1 HM2 HO1 HO2.
 destruct s as [[[[[[ge le] mem] irq] aux] abs] op].
 apply astar_l_apure_elim in H1. destruct H1 as[[B1[Bound1[G1[R1[T1 N1]]]]]H1].
 apply astar_l_apure_elim in H2. destruct H2 as[[B2[Bound2[G2[R2[T2 N2]]]]]H2].
 assert(Typed1:rule_type_val_match(Tptr V293_tcb_type)(V293_pub_old_head p1 b1 base1)=true)by(destruct p1;reflexivity).
 assert(Typed2:rule_type_val_match(Tptr V293_tcb_type)(V293_pub_old_head p2 b2 base2)=true)by(destruct p2;reflexivity).
 destruct(PEPoolLoads _ _ _ _ _ _ _ _ _ _ _ N1 G1 R1 T1 Typed1 H1)as[Lh1[Lg1[Lr1[Lt1 Ln1]]]].
 destruct(PEPoolLoads _ _ _ _ _ _ _ _ _ _ _ N2 G2 R2 T2 Typed2 H2)as[Lh2[Lg2[Lr2[Lt2 Ln2]]]].
 cbn[getmem get_smem get_mem substmo]in Lh1,Lg1,Lr1,Lt1,Ln1,Lh2,Lg2,Lr2,Lt2,Ln2.
 pose proof(@load_mem_mono _ _ _ _ _ Lh1 HM1)as HH1.
 pose proof(@load_mem_mono _ _ _ _ _ Lh2 HM2)as HH2.
 assert(Head:V293_pub_old_head p1 b1 base1=V293_pub_old_head p2 b2 base2)by congruence.
 pose proof(@load_mem_mono _ _ _ _ _ Lg1 HM1)as GG1.
 pose proof(@load_mem_mono _ _ _ _ _ Lg2 HM2)as GG2.
 assert(G:g1=g2)by(apply PEByteInjective;try assumption;congruence).
 pose proof(@load_mem_mono _ _ _ _ _ Lr1 HM1)as RR1.
 pose proof(@load_mem_mono _ _ _ _ _ Lr2 HM2)as RR2.
 assert(R:r1=r2)by(apply PEByteInjective;try assumption;congruence).
 pose proof(@load_mem_mono _ _ _ _ _ Lt1 HM1)as TT1.
 pose proof(@load_mem_mono _ _ _ _ _ Lt2 HM2)as TT2.
 assert(T:t1=t2)by(apply PEByteInjective;try assumption;congruence).
 pose proof(@load_mem_mono _ _ _ _ _ Ln1 HM1)as NN1.
 pose proof(@load_mem_mono _ _ _ _ _ Ln2 HM2)as NN2.
 assert(N:(if p1 then S k1 else 0)=(if p2 then S k2 else 0))by(apply PEByteInjective;try assumption;congruence).
 rewrite Head,G,R,T,N in H1.
 eapply PEPoolPrecise;[exact H1|exact H2|exact HM1|exact HM2|exact HO1|exact HO2].
Qed.
Lemma PEChainGood : forall n prev head,GoodInvAsrt(V293_tcb_active_chain n prev head).
Proof.
 induction n as[ |n IH];intros prev head;destruct head;try exact I;destruct a;cbn[V293_tcb_active_chain GoodInvAsrt];
 split;[exact I|split;[apply V293_storage_good| ]];intro next;
 split;[exact I|split;[exact I|split;[exact I|apply IH]]].
Qed.
Lemma PESharedGood : forall bh bg br bn y,GoodInvAsrt(V293_tcb_publication_shared bh bg br bn y).
Proof.
 intros. unfold V293_tcb_publication_shared. intros present k b base g row other.
 cbn[V293_tcb_publication_pool GoodInvAsrt]. repeat split;try exact I. apply PEChainGood.
Qed.
Lemma PEChainStable : forall n prev head ge le M ir aux O op ir' aux',
 (ge,le,M,ir,aux,O,op) |= V293_tcb_active_chain n prev head ->
 (ge,le,M,ir',aux',O,op) |= V293_tcb_active_chain n prev head.
Proof.
 induction n as[ |n IH];intros prev head ge le M ir aux O op ir' aux' H;
 destruct head;try destruct a;cbn[V293_tcb_active_chain]in H|-*;try contradiction;try exact H.
 apply astar_l_apure_elim in H. destruct H as[Bound H]. apply astar_l_apure_intro;[ |exact Bound].
 apply sat_split in H. destruct H as(m1&m2&o1&o2&JM&JO&HP&next&HN).
 apply sat_split'. exists m1. exists m2. exists o1. exists o2. split;[exact JM| ]. split;[exact JO| ]. split.
 - eapply V293_storage_aux_stable;exact HP.
 - exists next. apply astar_l_apure_elim in HN. destruct HN as[Typed HN]. apply astar_l_apure_intro;[ |exact Typed].
   apply sat_split in HN. destruct HN as(m3&m4&o3&o4&JM2&JO2&HN&HT).
   apply sat_split'. exists m3. exists m4. exists o3. exists o4. split;[exact JM2| ]. split;[exact JO2| ].
   split;[exact HN| ]. apply sat_split in HT. destruct HT as(m5&m6&o5&o6&JM3&JO3&HPrev&HT).
   apply sat_split'. exists m5. exists m6. exists o5. exists o6. split;[exact JM3| ]. split;[exact JO3| ].
   split;[exact HPrev|eapply IH;exact HT].
Qed.
Lemma PEPoolStable : forall bh bg br bn y n head g row other ge le M ir aux O op ir' aux',
 (ge,le,M,ir,aux,O,op) |= V293_tcb_publication_pool bh bg br bn y n head g row other ->
 (ge,le,M,ir',aux',O,op) |= V293_tcb_publication_pool bh bg br bn y n head g row other.
Proof.
 intros bh bg br bn y n head g row other ge le M ir aux O op ir' aux' H.
 unfold V293_tcb_publication_pool in *.
 do 5 (apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&HP&H);
 apply sat_split';exists m1;exists m2;exists o1;exists o2;
 split;[exact JM| ];split;[exact JO| ];split;[exact HP| ];clear m1 o1 JM JO HP M O;rename m2 into M;rename o2 into O).
 eapply PEChainStable;exact H.
Qed.
Lemma PESharedStable : forall bh bg br bn y ge le M ir aux O op ir' aux',
 (ge,le,M,ir,aux,O,op) |= V293_tcb_publication_shared bh bg br bn y ->
 (ge,le,M,ir',aux',O,op) |= V293_tcb_publication_shared bh bg br bn y.
Proof.
 intros bh bg br bn y ge le M ir aux O op ir' aux'(present&k&b&base&g&row&other&H).
 exists present. exists k. exists b. exists base. exists g. exists row. exists other.
 apply astar_l_apure_elim in H. destruct H as[Ranges H]. apply astar_l_apure_intro;[ |exact Ranges].
 eapply PEPoolStable;exact H.
Qed.
Lemma PESharedISR : forall bh bg br bn y,assertion.inv_isr_prop(V293_tcb_publication_shared bh bg br bn y).
Proof.
 intros. unfold assertion.inv_isr_prop. repeat split;intros;
 destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];eapply PESharedStable;exact H.
Qed.
Definition PECore y := V293_tcb_publication_shared 701%positive 702%positive 703%positive 704%positive y.
Definition PEInv y : Inv := fun i=>match i with
 | O=>mkinvasrt(PESharedGood 701%positive 702%positive 703%positive 704%positive y)
 (conj(PESharedPrecise 701%positive 702%positive 703%positive 704%positive y)
 (PESharedISR 701%positive 702%positive 703%positive 704%positive y))
 | S j=>V293_shared_inv(S j)end.

Lemma PENoisrTail : forall y n i,starinv_noisr (PEInv y)(S i)n <==> Aemp.
Proof.
 intros y n;induction n;intros i s;cbn[starinv_noisr];[reflexivity| ].
 change(s |= Aemp ** starinv_noisr (PEInv y)(S(S i))n <-> s |= Aemp).
 split;intro H.
 - apply astar_l_aemp_elim in H. apply IHn in H;exact H.
 - apply astar_l_aemp_intro. apply IHn;exact H.
Qed.
Lemma PENoisrCore : forall y n,starinv_noisr (PEInv y) 0 n <==> (PECore y).
Proof.
 intros y[ |n]s;[reflexivity| ].
 change(s |= (PECore y) ** starinv_noisr (PEInv y) 1 n <-> s |= (PECore y)).
 split;intro H.
 - apply astar_r_aemp_elim. eapply astar_mono;[intros st HS;exact HS|intros st HS;apply PENoisrTail in HS;exact HS|exact H].
 - eapply astar_mono;[intros st HS;exact HS|intros st HS;apply PENoisrTail;exact HS| ]. apply astar_r_aemp_intro;exact H.
Qed.
Theorem PEBorrowEquivalence : forall y n,
 Aisr(fun _=>false) ** invlth_isr (PEInv y) 0 n <==> Aisr(fun _=>false) ** (PECore y).
Proof.
 intros y n s. destruct s as [[[[[[ge le] M] ir] aux] O] op]. split;intro H.
 all: (apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&H1&H2);
 destruct H1 as[E Empty];cbn in E;subst ir;
 apply sat_split';exists m1;exists m2;exists o1;exists o2;
 split;[exact JM| ];split;[exact JO| ];split;[split;[reflexivity|exact Empty]| ]).
 - unfold invlth_isr in H2. rewrite Nat.sub_0_r in H2.
   apply PENoisrCore with(n:=n). eapply invisr_imply_noisr';[ |exact H2]. reflexivity.
 - unfold invlth_isr. rewrite Nat.sub_0_r.
   apply V293_shared_clear_noisr_close;[reflexivity| ]. apply PENoisrCore;exact H2.
Qed.



Definition PEState M ie cs : RstateOP :=
 (PPGE,FPLE,M,(fun _=>false),(ie,[],cs),(emp:osabst),spec_done None).
Lemma PERawStable : forall cells ge le M ir aux O op ir' aux',
 (ge,le,M,ir,aux,O,op) |= V293_rdy_raw_cells cells Aemp ->
 (ge,le,M,ir',aux',O,op) |= V293_rdy_raw_cells cells Aemp.
Proof.
 induction cells as[ |[[a tp]v]xs IH];intros ge le M ir aux O op ir' aux' H;
 cbn[V293_rdy_raw_cells]in H|-*;[exact H| ].
 apply sat_split in H. destruct H as(m1&m2&o1&o2&JM&JO&HP&HT).
 apply sat_split'. exists m1. exists m2. exists o1. exists o2.
 split;[exact JM| ]. split;[exact JO| ]. split;[exact HP|eapply IH;exact HT].
Qed.
Lemma PEStar : forall m1 m2 m ie cs p q,
 join m1 m2 m -> PEState m1 ie cs |= p -> PEState m2 ie cs |= q -> PEState m ie cs |= p ** q.
Proof.
 intros. apply sat_split'. exists m1. exists m2. exists(emp:osabst). exists(emp:osabst).
 split;[exact H| ]. split;[apply map_join_emp| ]. split;assumption.
Qed.
Lemma PERSpatial : forall ie cs,PEState(merge FPCurrent FPSentinel)ie cs |= FPR.
Proof.
 intros. unfold FPR. eapply PEStar with(m1:=FPCurrent)(m2:=FPSentinel).
 - FPRapart 402%positive.
 - exists Tvoid. exists 402%positive. eapply PEStar with(m1:=emp)(m2:=FPCurrent).
   + apply map_join_comm;apply map_join_emp.
   + exists 402%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
 - eapply PEStar with(m1:=emp)(m2:=FPSentinel);[apply map_join_comm;apply map_join_emp| | ].
   + unfold LINV. apply astar_comm. apply astar_l_apure_intro;[split;reflexivity|apply V293_witness_li_good].
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma PEBindings : forall ie cs,PEState emp ie cs |=
 V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z 208%positive 701%positive 702%positive 703%positive 704%positive.
Proof.
 intros ie cs. unfold V293_pub_bindings. repeat split;first[
 solve[exists 208%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 701%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 702%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 703%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[exists 704%positive;split;[vm_compute;reflexivity|repeat split;reflexivity]]|
 solve[intros[v H];vm_compute in H;discriminate]].
Qed.

Lemma PELiteralRaw : forall (present upper:bool) ie cs,
 PEState(FPMemory(PPInputRows present(if upper then 1 else 0)))ie cs |=
 V293_rdy_raw_cells(PPInputRows present(if upper then 1 else 0))Aemp.
Proof. intros. eapply PERawStable. exact(PPLiteralRaw present upper cs). Qed.
Lemma PEInputRaw : forall (present upper:bool) ie cs,
 PEState(PPInput present(if upper then 1 else 0))ie cs |=
 V293_rdy_raw_cells(PPInputRows present(if upper then 1 else 0))Aemp ** FPR.
Proof.
 intros present upper ie cs. unfold PPInput.
 eapply PEStar;[ |apply PELiteralRaw|apply PERSpatial].
   apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 402%positive);[subst b;left| ];
   try(destruct(Pos.eq_dec b 601%positive);[subst b;left|right;left]);
   unfold PPInputRows,PPPrivateRows,PPSpareRows,PPSharedRows,PPNodeRows,PPDefaults,
   V293_tcb_active_payload_cells,V293_tcb_publication_spare_cells,FPCurrent,FPSentinel,FPBytes;
   destruct present,upper;cbn[app map FPMemory];FPOutside.
Qed.

Lemma PEConcretePool : forall (present:bool) y,
 V293_tcb_publication_pool 701%positive 702%positive 703%positive 704%positive y
 (if present then 2 else 0)(if present then PPOld else Vnull)0 16 99 ==> PECore y.
Proof.
 intros present y s H. unfold PECore,V293_tcb_publication_shared.
 exists present. exists 1. exists 511%positive. exists 0%Z. exists 0. exists 16. exists 99.
 apply astar_l_apure_intro.
 - unfold V293_pub_old_head. destruct present;exact H.
 - assert(B:(55<=Int.max_unsigned)%Z)by(vm_compute;congruence). destruct present;cbn;lia.
Qed.
Definition PEPre y cs :=
 V293_tcb_publication_enabled 108%Z 93%Z 94%Z 95%Z 96%Z
 208%positive 501%positive 0 701%positive 702%positive 703%positive 704%positive y 5
 Vnull Vnull FPR(spec_done None)(fun _=>false)nil cs.
Theorem PELiteralInput : forall (present upper:bool) cs,
 PEState(PPInput present(if upper then 1 else 0))true cs |=
 PEPre(if upper then 1 else 0)cs ** invlth_isr(PEInv(if upper then 1 else 0))0 INUM.
Proof.
 intros present upper cs. pose proof(PEInputRaw present upper true cs)as S. unfold PPInput in S|-*.
 eapply astar_mono in S;[ |apply PPPhysicalView|intros st HS;exact HS].
 assert(C:PEState(merge(FPMemory(PPInputRows present(if upper then 1 else 0)))(merge FPCurrent FPSentinel))true cs |=
 V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z 208%positive 701%positive 702%positive 703%positive 704%positive **
 ((Amapsto(208%positive,0%Z)(Tptr V293_tcb_type)true PPNew **
 (V293_tcb_publication_new 501%positive 0(if upper then 1 else 0)5 Vnull Vnull **
 V293_tcb_publication_pool 701%positive 702%positive 703%positive 704%positive(if upper then 1 else 0)
 (if present then 2 else 0)(if present then PPOld else Vnull)0 16 99)) ** FPR)).
 { eapply PEStar with(m1:=emp);[apply map_join_comm;apply map_join_emp|apply PEBindings|exact S]. }
 assert(D:PEState(merge(FPMemory(PPInputRows present(if upper then 1 else 0)))(merge FPCurrent FPSentinel))true cs |=
 V293_tcb_publication_pool 701%positive 702%positive 703%positive 704%positive(if upper then 1 else 0)
 (if present then 2 else 0)(if present then PPOld else Vnull)0 16 99 **
 V293_tcb_publication_private 108%Z 93%Z 94%Z 95%Z 96%Z 208%positive 501%positive 0
 701%positive 702%positive 703%positive 704%positive(if upper then 1 else 0)5 Vnull Vnull FPR).
 { unfold V293_tcb_publication_private;clear -C;sep auto. }
 eapply astar_mono in D;[ |apply PEConcretePool|intros st HS;exact HS].
 apply astar_l_aisr_intro with(i:=fun _=>false)in D;[ |reflexivity].
 assert(E:PEState(merge(FPMemory(PPInputRows present(if upper then 1 else 0)))(merge FPCurrent FPSentinel))true cs |=
 (Aisr(fun _=>false) ** PECore(if upper then 1 else 0)) **
 V293_tcb_publication_private 108%Z 93%Z 94%Z 95%Z 96%Z 208%positive 501%positive 0
 701%positive 702%positive 703%positive 704%positive(if upper then 1 else 0)5 Vnull Vnull FPR)by(clear -D;sep auto).
 eapply astar_mono in E;[ |intros st HS;apply PEBorrowEquivalence;exact HS|intros st HS;exact HS].
 apply astar_l_aop'_intro with(aop:=spec_done None)in E;[ |reflexivity].
 apply astar_l_aie_intro with(i:=true)in E;[ |reflexivity].
 apply astar_l_ais_intro with(i:=nil)in E;[ |reflexivity].
 apply astar_l_acs_intro with(i:=cs)in E;[ |reflexivity].
 unfold PEPre,V293_tcb_publication_enabled. clear -E;sep auto.
Qed.
Theorem PECommonLocalInput : forall (present upper:bool) cs,
 exists s,s |= PEPre(if upper then 1 else 0)cs.
Proof.
 intros present upper cs. pose proof(PELiteralInput present upper cs)as H.
 apply sat_split in H. destruct H as(m1&m2&o1&o2&JM&JO&HP&HI).
 eexists. exact HP.
Qed.

Lemma PEBorrowOpen : forall y n,
 Aisr(fun _=>false) ** invlth_isr(PEInv y)0 n ==>
 Aisr(fun _=>false) ** (PECore y ** Aemp).
Proof.
 intros y n s H. apply PEBorrowEquivalence in H.
 clear -H;sep auto.
Qed.
Lemma PEBorrowClose : forall y n,
 Aisr(fun _=>false) ** (PECore y ** Aemp) ==>
 Aisr(fun _=>false) ** invlth_isr(PEInv y)0 n.
Proof.
 intros y n s H. apply PEBorrowEquivalence. clear -H;sep auto.
Qed.
Definition PEOpened y cs :=
 EX present:bool,EX k:nat,EX bo:block,EX obase:Z,EX g:nat,EX row:nat,EX other:nat,
 [|(0<=obase)%Z /\ (obase+55<=Int.max_unsigned)%Z /\
 g<256 /\ row<256 /\ other<256 /\ (if present then S k else 0)<256|] **
 V293_tcb_publication_input 108%Z 93%Z 94%Z 95%Z 96%Z
 208%positive 501%positive 0 701%positive 702%positive 703%positive 704%positive y 5
 (if present then S k else 0)(V293_pub_old_head present bo obase)g row other Vnull Vnull(Aemp ** FPR)
 (spec_done None)(fun _=>false)nil(true::cs).
Theorem PEEnterChecked : forall Spec sd r ri y cs,
 InfRules Spec sd V293_witness_li(PEInv y)r ri(PEPre y cs)
 (sprim encrit)(PEOpened y cs)FPTid.
Proof.
 intros. unfold PEPre,PEOpened. apply V293_tcb_publication_enter with(K:=Aemp).
 - vm_compute;lia.
 - apply FPRGood.
 - apply PEBorrowOpen.
Qed.
Definition PEReturned (y:nat) cs :=
 V293_tcb_publication_returned 108%Z 93%Z 94%Z 95%Z 96%Z
 208%positive 501%positive 0 701%positive 702%positive 703%positive 704%positive
 FPR(spec_done None)(fun _=>false)nil cs.
Theorem PEExitChecked : forall Spec sd r ri y n g row other cs,
 n<256 -> g<256 -> row<256 -> other<256 ->
 InfRules Spec sd V293_witness_li(PEInv y)r ri
 (V293_tcb_publication_output 108%Z 93%Z 94%Z 95%Z 96%Z
 208%positive 501%positive 0 701%positive 702%positive 703%positive 704%positive y
 n g row other(Aemp ** FPR)(spec_done None)(fun _=>false)nil(true::cs))
 (sprim excrit)(PEReturned y cs)FPTid.
Proof.
 intros Spec sd r ri y n g row other cs Count G Row Other. unfold PEReturned.
 apply V293_tcb_publication_exit with(y:=y)(n:=n)(g:=g)(row:=row)(other:=other)(K:=Aemp).
 - lia.
 - vm_compute;congruence.
 - exact Count.
 - exact G.
 - exact Row.
 - exact Other.
 - apply FPRGood.
 - apply FPRCurLINV.
 - apply PEBorrowClose.
Qed.
(* Count0/2 is fixed only for this already-disabled suffix. No implication
   from the enabled local assertion to that count is claimed. *)
Theorem PEBodyExitReturnChecked : forall Spec sd (present upper:bool) cs,
 InfRules Spec sd V293_witness_li(PEInv(if upper then 1 else 0))
 (fun _=>PEReturned(if upper then 1 else 0)cs)Afalse
 (PPPre present(if upper then 1 else 0)(true::cs))
 (sseq(V293_TCB_publish_body 108%Z 93%Z 94%Z 95%Z 96%Z)
 (sseq(sprim excrit)(srete(econst32 Int.zero))))Afalse FPTid.
Proof.
 intros. eapply seq_rule;[apply PPBodyChecked| ]. eapply seq_rule.
 - eapply conseq_rule with(p:=
 (V293_tcb_publication_output 108%Z 93%Z 94%Z 95%Z 96%Z
 208%positive 501%positive 0 701%positive 702%positive 703%positive 704%positive(if upper then 1 else 0)
 (S(if present then 2 else 0))(Nat.setbit 0(if upper then 1 else 0))(Nat.setbit 16 5)99
 (Aemp ** FPR)(spec_done None)(fun _=>false)nil(true::cs))).
   + unfold PPPost,V293_tcb_publication_output;intros s H;clear -H;sep auto.
   + intros s H;exact H.
   + apply PEExitChecked;destruct present,upper;vm_compute;lia.
 - apply rete_rule with(v:=Vint32 Int.zero)(t:=Tint32).
   intros s H. split;[exact H| ].
   destruct s as [[[[[[ge le] M] irq] aux] O] op].
   cbn[sat evalval evaltype getsmem get_smem]. repeat split;try reflexivity;discriminate.
Qed.
(* This statement deliberately retains Capacity: PECore permits count255.
   The literal examples do not prove a universal interleaving bound. *)
Theorem PEEnabledSuffixConditional : forall Spec sd y cs,
 y<2 ->
 (forall (present:bool) k bo obase g row other s,
  s |= V293_tcb_publication_input 108%Z 93%Z 94%Z 95%Z 96%Z
   208%positive 501%positive 0 701%positive 702%positive 703%positive 704%positive y 5
   (if present then S k else 0)(V293_pub_old_head present bo obase)g row other
   Vnull Vnull(Aemp ** FPR)(spec_done None)(fun _=>false)nil(true::cs) ->
   (if present then S k else 0)<255) ->
 InfRules Spec sd V293_witness_li(PEInv y)(fun _=>PEReturned y cs)Afalse
 (PEPre y cs)(V293_TCB_publish 108%Z 93%Z 94%Z 95%Z 96%Z)Afalse FPTid.
Proof.
 intros Spec sd y cs Y Capacity. unfold PEPre.
 apply V293_OS_TCBInit_publish_enabled with(K:=Aemp).
 - lia.
 - vm_compute;congruence.
 - exact Y.
 - lia.
 - vm_compute;lia.
 - apply FPRGood.
 - apply FPRCurLINV.
 - apply PEBorrowOpen.
 - apply PEBorrowClose.
 - exact Capacity.
 - intros s H;exact H.
Qed.
Lemma PESharedHeadLoad : forall y s,s |= PECore y ->
 exists v,load(Tptr V293_tcb_type)(getmem s)(701%positive,0%Z)=Some v.
Proof.
 intros y s(p&k&b&base&g&row&other&H). apply astar_l_apure_elim in H.
 destruct H as[[B[Bound[G[Row[Other Count]]]]]H].
 assert(Typed:rule_type_val_match(Tptr V293_tcb_type)(V293_pub_old_head p b base)=true)by(destruct p;reflexivity).
 exists(V293_pub_old_head p b base).
 exact(proj1(PEPoolLoads _ _ _ _ _ _ _ _ _ _ _ Count G Row Other Typed H)).
Qed.
Theorem PEMissingBorrowImpossible :
 ~ (Aisr(fun _=>false) ** Aemp ==>
 Aisr(fun _=>false) ** (PECore 0 ** Aemp)).
Proof.
 intro Open.
 assert(H:PEState emp true nil |= Aisr(fun _=>false) ** Aemp).
 { apply astar_l_aisr_intro;[split;reflexivity|reflexivity]. }
 apply Open in H. apply sat_split in H. destruct H as(m1&m2&o1&o2&JM&JO&HI&HC).
 apply astar_r_aemp_elim in HC. destruct(PESharedHeadLoad _ _ HC)as[v Load].
 cbn[PEState getmem get_smem get_mem substmo]in Load.
 apply map_join_pos in JM. destruct JM as[_ E]. subst m2.
 vm_compute in Load. discriminate.
Qed.
