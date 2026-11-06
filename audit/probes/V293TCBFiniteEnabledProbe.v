(* Concrete same invariant and actual same-block enabled inputs.
   Not the production task/ready invariant or initialized reachability. *)
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
Require Import CertiOS.audit.probes.V293TCBEnabledPublicationProbe.
Require Import CertiOS.audit.probes.V293TCBFiniteSitesProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteSites.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteEnabled.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Lemma FEChainGood : forall nodes prev head,GoodInvAsrt(V293_tcb_indexed_chain nodes prev head).
Proof.
 induction nodes as[ |[b off]nodes IH];intros prev head;cbn[V293_tcb_indexed_chain GoodInvAsrt];[exact I| ].
 split;[exact I|split;[apply V293_storage_good| ]];intro next;
 split;[exact I|split;[exact I|split;[exact I|apply IH]]].
Qed.
Lemma FESharedGood : forall table bh bg br bn y,GoodInvAsrt(V293_tcb_finite_shared table bh bg br bn y).
Proof.
 intros. unfold V293_tcb_finite_shared. intros present tail b base g row other.
 cbn[V293_tcb_indexed_pool GoodInvAsrt]. repeat split;try exact I. apply FEChainGood.
Qed.
Lemma FESharedPrecise : forall table bh bg br bn y,precise(V293_tcb_finite_shared table bh bg br bn y).
Proof.
 intros table bh bg br bn y s M1 M2 O1 O2 H1 H2 M O HM1 HM2 HO1 HO2.
 apply V293_tcb_finite_shared_forget in H1,H2.
 eapply PESharedPrecise;[exact H1|exact H2|exact HM1|exact HM2|exact HO1|exact HO2].
Qed.
Lemma FEChainStable : forall nodes prev head ge le M ir aux O op ir' aux',
 (ge,le,M,ir,aux,O,op) |= V293_tcb_indexed_chain nodes prev head ->
 (ge,le,M,ir',aux',O,op) |= V293_tcb_indexed_chain nodes prev head.
Proof.
 induction nodes as[ |[b off]nodes IH];intros prev head ge le M ir aux O op ir' aux' H;
 cbn[V293_tcb_indexed_chain]in H|-*;[exact H| ].
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
Lemma FEPoolStable : forall bh bg br bn y nodes head g row other ge le M ir aux O op ir' aux',
 (ge,le,M,ir,aux,O,op) |= V293_tcb_indexed_pool bh bg br bn y nodes head g row other ->
 (ge,le,M,ir',aux',O,op) |= V293_tcb_indexed_pool bh bg br bn y nodes head g row other.
Proof.
 intros bh bg br bn y nodes head g row other ge le M ir aux O op ir' aux' H.
 unfold V293_tcb_indexed_pool in *.
 do 5 (apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&HP&H);
 apply sat_split';exists m1;exists m2;exists o1;exists o2;
 split;[exact JM| ];split;[exact JO| ];split;[exact HP| ];clear m1 o1 JM JO HP M O;rename m2 into M;rename o2 into O).
 eapply FEChainStable;exact H.
Qed.
Lemma FESharedStable : forall table bh bg br bn y ge le M ir aux O op ir' aux',
 (ge,le,M,ir,aux,O,op) |= V293_tcb_finite_shared table bh bg br bn y ->
 (ge,le,M,ir',aux',O,op) |= V293_tcb_finite_shared table bh bg br bn y.
Proof.
 intros table bh bg br bn y ge le M ir aux O op ir' aux'(present&tail&b&base&g&row&other&H).
 exists present. exists tail. exists b. exists base. exists g. exists row. exists other.
 apply astar_l_apure_elim in H. destruct H as[Ranges H]. apply astar_l_apure_intro;[ |exact Ranges].
 eapply FEPoolStable;exact H.
Qed.
Lemma FESharedISR : forall table bh bg br bn y,assertion.inv_isr_prop(V293_tcb_finite_shared table bh bg br bn y).
Proof.
 intros. unfold assertion.inv_isr_prop. repeat split;intros;
 destruct s as [[[[[[ge le] M] ir] [[ie si] cs]] O] op];eapply FESharedStable;exact H.
Qed.
Definition FECore y := V293_tcb_finite_shared 501%positive 701%positive 702%positive 703%positive 704%positive y.
Definition FEInv y : Inv := fun i=>match i with
 | O=>mkinvasrt(FESharedGood 501%positive 701%positive 702%positive 703%positive 704%positive y)
 (conj(FESharedPrecise 501%positive 701%positive 702%positive 703%positive 704%positive y)
 (FESharedISR 501%positive 701%positive 702%positive 703%positive 704%positive y))
 | S j=>V293_shared_inv(S j)end.

Lemma FENoisrTail : forall y n i,starinv_noisr (FEInv y)(S i)n <==> Aemp.
Proof.
 intros y n;induction n;intros i s;cbn[starinv_noisr];[reflexivity| ].
 change(s |= Aemp ** starinv_noisr (FEInv y)(S(S i))n <-> s |= Aemp).
 split;intro H.
 - apply astar_l_aemp_elim in H. apply IHn in H;exact H.
 - apply astar_l_aemp_intro. apply IHn;exact H.
Qed.
Lemma FENoisrCore : forall y n,starinv_noisr (FEInv y) 0 n <==> (FECore y).
Proof.
 intros y[ |n]s;[reflexivity| ].
 change(s |= (FECore y) ** starinv_noisr (FEInv y) 1 n <-> s |= (FECore y)).
 split;intro H.
 - apply astar_r_aemp_elim. eapply astar_mono;[intros st HS;exact HS|intros st HS;apply FENoisrTail in HS;exact HS|exact H].
 - eapply astar_mono;[intros st HS;exact HS|intros st HS;apply FENoisrTail;exact HS| ]. apply astar_r_aemp_intro;exact H.
Qed.
Theorem FEBorrowEquivalence : forall y n,
 Aisr(fun _=>false) ** invlth_isr (FEInv y) 0 n <==> Aisr(fun _=>false) ** (FECore y).
Proof.
 intros y n s. destruct s as [[[[[[ge le] M] ir] aux] O] op]. split;intro H.
 all: (apply sat_split in H;destruct H as(m1&m2&o1&o2&JM&JO&H1&H2);
 destruct H1 as[E Empty];cbn in E;subst ir;
 apply sat_split';exists m1;exists m2;exists o1;exists o2;
 split;[exact JM| ];split;[exact JO| ];split;[split;[reflexivity|exact Empty]| ]).
 - unfold invlth_isr in H2. rewrite Nat.sub_0_r in H2.
   apply FENoisrCore with(n:=n). eapply invisr_imply_noisr';[ |exact H2]. reflexivity.
 - unfold invlth_isr. rewrite Nat.sub_0_r.
   apply V293_shared_clear_noisr_close;[reflexivity| ]. apply FENoisrCore;exact H2.
Qed.



Lemma FELiteralRaw : forall (present upper:bool) ie cs,
 PEState(FPMemory(FCInputRows present(if upper then 1 else 0)))ie cs |=
 V293_rdy_raw_cells(FCInputRows present(if upper then 1 else 0))Aemp.
Proof. intros. eapply PERawStable. exact(FCLiteralRaw present upper cs). Qed.
Lemma FEInputRaw : forall (present upper:bool) ie cs,
 PEState(FCInput present(if upper then 1 else 0))ie cs |=
 V293_rdy_raw_cells(FCInputRows present(if upper then 1 else 0))Aemp ** FPR.
Proof.
 intros present upper ie cs. unfold FCInput.
 eapply PEStar;[ |apply FELiteralRaw|apply PERSpatial].
   apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 402%positive);[subst b;left| ];
   try(destruct(Pos.eq_dec b 601%positive);[subst b;left|right;left]);
   unfold FCInputRows,PPPrivateRows,PPSpareRows,FCSharedRows,FCNodeRows,PPDefaults,
   V293_tcb_active_payload_cells,V293_tcb_publication_spare_cells,FPCurrent,FPSentinel,FPBytes;
   destruct present,upper;cbn[app map FPMemory];FPOutside.
Qed.

Lemma FEConcretePool : forall (present:bool) y,
 V293_tcb_indexed_pool 701%positive 702%positive 703%positive 704%positive y
 (FCNodes present)(if present then FCOld else Vnull)0 16 99 ==> FECore y.
Proof.
 intros present y s H. unfold FECore,V293_tcb_finite_shared.
 exists present. exists[(501%positive,Int.repr 112)]. exists 501%positive. exists 56%Z.
 exists 0. exists 16. exists 99. apply astar_l_apure_intro.
 - unfold V293_pub_old_head,FCNodes,FCOld in *;destruct present;exact H.
 - assert(B:(111<=Int.max_unsigned)%Z)by(vm_compute;congruence).
   split;[lia| ]. split;[lia| ]. split;[lia| ]. split;[lia| ]. split;[lia| ].
   exact(FCNodesValid present).
Qed.
Definition FEPre y cs :=
 V293_tcb_publication_enabled 108%Z 93%Z 94%Z 95%Z 96%Z
 208%positive 501%positive 0 701%positive 702%positive 703%positive 704%positive y 5
 Vnull Vnull FPR(spec_done None)(fun _=>false)nil cs.
Theorem FELiteralInput : forall (present upper:bool) cs,
 PEState(FCInput present(if upper then 1 else 0))true cs |=
 FEPre(if upper then 1 else 0)cs ** invlth_isr(FEInv(if upper then 1 else 0))0 INUM.
Proof.
 intros present upper cs. pose proof(FEInputRaw present upper true cs)as S. unfold FCInput in S|-*.
 eapply astar_mono in S;[ |apply FCPhysicalView|intros st HS;exact HS].
 assert(C:PEState(merge(FPMemory(FCInputRows present(if upper then 1 else 0)))(merge FPCurrent FPSentinel))true cs |=
 V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z 208%positive 701%positive 702%positive 703%positive 704%positive **
 ((Amapsto(208%positive,0%Z)(Tptr V293_tcb_type)true PPNew **
 (V293_tcb_publication_new 501%positive 0(if upper then 1 else 0)5 Vnull Vnull **
 V293_tcb_indexed_pool 701%positive 702%positive 703%positive 704%positive(if upper then 1 else 0)
 (FCNodes present)(if present then FCOld else Vnull)0 16 99)) ** FPR)).
 { eapply PEStar with(m1:=emp);[apply map_join_comm;apply map_join_emp|apply PEBindings|exact S]. }
 assert(D:PEState(merge(FPMemory(FCInputRows present(if upper then 1 else 0)))(merge FPCurrent FPSentinel))true cs |=
 V293_tcb_indexed_pool 701%positive 702%positive 703%positive 704%positive(if upper then 1 else 0)
 (FCNodes present)(if present then FCOld else Vnull)0 16 99 **
 V293_tcb_publication_private 108%Z 93%Z 94%Z 95%Z 96%Z 208%positive 501%positive 0
 701%positive 702%positive 703%positive 704%positive(if upper then 1 else 0)5 Vnull Vnull FPR).
 { unfold V293_tcb_publication_private;clear -C;sep auto. }
 eapply astar_mono in D;[ |apply FEConcretePool|intros st HS;exact HS].
 apply astar_l_aisr_intro with(i:=fun _=>false)in D;[ |reflexivity].
 assert(E:PEState(merge(FPMemory(FCInputRows present(if upper then 1 else 0)))(merge FPCurrent FPSentinel))true cs |=
 (Aisr(fun _=>false) ** FECore(if upper then 1 else 0)) **
 V293_tcb_publication_private 108%Z 93%Z 94%Z 95%Z 96%Z 208%positive 501%positive 0
 701%positive 702%positive 703%positive 704%positive(if upper then 1 else 0)5 Vnull Vnull FPR)by(clear -D;sep auto).
 eapply astar_mono in E;[ |intros st HS;apply FEBorrowEquivalence;exact HS|intros st HS;exact HS].
 apply astar_l_aop'_intro with(aop:=spec_done None)in E;[ |reflexivity].
 apply astar_l_aie_intro with(i:=true)in E;[ |reflexivity].
 apply astar_l_ais_intro with(i:=nil)in E;[ |reflexivity].
 apply astar_l_acs_intro with(i:=cs)in E;[ |reflexivity].
 unfold FEPre,V293_tcb_publication_enabled. clear -E;sep auto.
Qed.
Lemma FEBorrowOpen : forall y n,
 Aisr(fun _=>false) ** invlth_isr(FEInv y)0 n ==>
 Aisr(fun _=>false) ** (FECore y ** Aemp).
Proof.
 intros y n s H. apply FEBorrowEquivalence in H.
 clear -H;sep auto.
Qed.
Lemma FEBorrowClose : forall y n,
 Aisr(fun _=>false) ** (FECore y ** Aemp) ==>
 Aisr(fun _=>false) ** invlth_isr(FEInv y)0 n.
Proof.
 intros y n s H. apply FEBorrowEquivalence. clear -H;sep auto.
Qed.
Definition FEReturned (y:nat) cs :=
 V293_tcb_publication_returned 108%Z 93%Z 94%Z 95%Z 96%Z
 208%positive 501%positive 0 701%positive 702%positive 703%positive 704%positive
 FPR(spec_done None)(fun _=>false)nil cs.
(* Whole enabled suffix, not just separate body/exit segments. *)
Theorem FEEnabledSuffixChecked : forall Spec sd y cs,
 y<2 ->
 InfRules Spec sd V293_witness_li(FEInv y)(fun _=>FEReturned y cs)Afalse
 (FEPre y cs)(V293_TCB_publish 108%Z 93%Z 94%Z 95%Z 96%Z)Afalse FPTid.
Proof.
 intros Spec sd y cs Y. unfold FEPre,FEReturned.
 apply V293_OS_TCBInit_publish_finite_enabled with(tcbtable:=501%positive)(K:=Aemp).
 - lia.
 - vm_compute;congruence.
 - exact Y.
 - lia.
 - apply FCNewMember.
 - vm_compute;lia.
 - apply FPRGood.
 - apply FPRCurLINV.
 - apply FEBorrowOpen.
 - apply FEBorrowClose.
 - intros s H;exact H.
Qed.
Print Assumptions FEEnabledSuffixChecked.
Print Assumptions FELiteralInput.
