(* Actual table-site fixtures: all three nodes share one block at 0/56/112.
   Disabled-entry publication only; not the enabled production invariant. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.audit.probes.V293TCBPublicationPoolProbe.
Require Import CertiOS.audit.probes.V293TCBFreePoolProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteSites.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublicationPool.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublishHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.code.V293OSTCBPublish.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition FCOld := Vptr(501%positive,Int.repr 56).
Definition FCTail := Vptr(501%positive,Int.repr 112).
Definition FCNodes (present:bool) := V293_tcb_old_sites present 501%positive 56
 [(501%positive,Int.repr 112)].
Definition FCNodeRows base prev next := PPDefaults(V293_tcb_active_payload_cells 501%positive base) ++
 [((501%positive,(base+20)%Z),Tcom_ptr 410%Z,next);((501%positive,(base+24)%Z),Tcom_ptr 410%Z,prev)].
Definition FCSharedRows (present:bool) y :=
 [((701%positive,0%Z),Tptr V293_tcb_type,if present then FCOld else Vnull);
 ((702%positive,0%Z),Tint8,V293_byteval 0);
 ((703%positive,Z.of_nat y),Tint8,V293_byteval 16);
 ((703%positive,Z.of_nat(1-y)),Tint8,V293_byteval 99);
 ((704%positive,0%Z),Tint8,V293_byteval(if present then 2 else 0))] ++
 if present then FCNodeRows 56 Vnull FCTail ++ FCNodeRows 112 FCOld Vnull else [].
Definition FCInputRows present y := PPPrivateRows y ++ FCSharedRows present y.
Definition FCInput present y := merge(FPMemory(FCInputRows present y))(merge FPCurrent FPSentinel).
Definition FCPre (present:bool) y cs :=
 V293_tcb_indexed_input 108%Z 93%Z 94%Z 95%Z 96%Z
 208%positive 501%positive 0 701%positive 702%positive 703%positive 704%positive y 5
 (FCNodes present)(if present then FCOld else Vnull)0 16 99 Vnull Vnull FPR
 (spec_done None)(fun _=>false)nil cs.
Definition FCPost (present:bool) y cs :=
 [|V293_tcb_sites_valid(V293_tcb_table_sites 501%positive)((501%positive,Int.zero)::FCNodes present)|] **
 V293_tcb_indexed_output 108%Z 93%Z 94%Z 95%Z 96%Z
 208%positive 501%positive 0 701%positive 702%positive 703%positive 704%positive y
 ((501%positive,Int.zero)::FCNodes present)(Nat.setbit 0 y)(Nat.setbit 16 5)99 FPR
 (spec_done None)(fun _=>false)nil cs.
Lemma FCNodeFold : forall base prev next R,
 rule_type_val_match(Tcom_ptr 410%Z)next=true ->
 V293_rdy_raw_cells(FCNodeRows base prev next)R ==>
 V293_tcb_active_payload 501%positive base **
 (Amapsto(501%positive,(base+20)%Z)(Tcom_ptr 410%Z)true next **
 (Amapsto(501%positive,(base+24)%Z)(Tcom_ptr 410%Z)true prev ** R)).
Proof.
 intros base prev next R Typed s H. unfold FCNodeRows in H. rewrite V293_raw_cells_append in H.
 eapply PPDefaultsStorage in H.
 - cbn[V293_rdy_raw_cells]in H. exact H.
 - unfold V293_tcb_active_payload_cells,V293_tcb_publication_spare_cells. cbn[app]. repeat constructor.
Qed.
Lemma FCChainFold : forall (present:bool) R,
 V293_rdy_raw_cells(if present then FCNodeRows 56 Vnull FCTail ++ FCNodeRows 112 FCOld Vnull else [])R ==>
 V293_tcb_indexed_chain(FCNodes present)Vnull(if present then FCOld else Vnull) ** R.
Proof.
 intros present R s H. assert(B:(167<=Int.max_unsigned)%Z)by(vm_compute;congruence). destruct present.
 - rewrite V293_raw_cells_append in H. apply FCNodeFold in H;[ |reflexivity].
   eapply astar_mono in H;[ |intros st HS;exact HS| ].
   2:{ apply astar_mono;[intros st HS;exact HS| ].
       apply astar_mono;[intros st HS;exact HS|apply FCNodeFold;reflexivity]. }
   cbn[FCNodes V293_tcb_old_sites FCOld FCTail V293_tcb_indexed_chain].
   rewrite Int.unsigned_repr by(vm_compute;intuition congruence). sep normal.
   exists FCTail. cbn[FCTail V293_tcb_indexed_chain].
   rewrite Int.unsigned_repr by(vm_compute;intuition congruence). sep normal. exists Vnull.
   cbn[V293_tcb_indexed_chain]. clear -H B;sep auto;lia.
 - cbn[FCNodes V293_tcb_old_sites V293_rdy_raw_cells V293_tcb_indexed_chain]in *. clear -H;sep auto.
Qed.
Lemma FCSharedFold : forall (present:bool) y,
 V293_rdy_raw_cells(FCSharedRows present y)Aemp ==>
 V293_tcb_indexed_pool 701%positive 702%positive 703%positive 704%positive y
 (FCNodes present)(if present then FCOld else Vnull)0 16 99.
Proof.
 intros present y s H. unfold FCSharedRows in H. rewrite V293_raw_cells_append in H.
 eapply V293_raw_cells_mono in H;[ |apply FCChainFold].
 unfold V293_tcb_indexed_pool. destruct present;
 cbn[V293_rdy_raw_cells FCNodes V293_tcb_old_sites length]in *;clear -H;sep auto.
Qed.
Lemma FCPhysicalView : forall (present:bool) y,
 V293_rdy_raw_cells(FCInputRows present y)Aemp ==>
 Amapsto(208%positive,0%Z)(Tptr V293_tcb_type)true PPNew **
 (V293_tcb_publication_new 501%positive 0 y 5 Vnull Vnull **
 V293_tcb_indexed_pool 701%positive 702%positive 703%positive 704%positive y
 (FCNodes present)(if present then FCOld else Vnull)0 16 99).
Proof.
 intros present y s H. unfold FCInputRows in H. rewrite V293_raw_cells_append in H.
 eapply V293_raw_cells_mono in H;[ |apply FCSharedFold]. apply PPPrivateFold in H. exact H.
Qed.
Lemma FCNodesValid : forall present,
 V293_tcb_sites_valid(V293_tcb_table_sites 501%positive)(FCNodes present).
Proof.
 intro present. destruct present;unfold V293_tcb_sites_valid,FCNodes,V293_tcb_old_sites.
 - split.
   + repeat constructor;vm_compute;intuition congruence.
   + intros node[Same|[Same|Impossible]];try contradiction;subst node;
     unfold V293_tcb_table_sites;cbn[seq map];simpl;tauto.
 - split;[constructor|intros node Impossible;contradiction].
Qed.
Lemma FCNewMember : In(501%positive,Int.repr 0)(V293_tcb_table_sites 501%positive).
Proof. unfold V293_tcb_table_sites;cbn[seq map];left;reflexivity. Qed.
Theorem FCBodyChecked : forall Spec sd I r ri (present upper:bool) cs,
 InfRules Spec sd V293_witness_li I r ri(FCPre present(if upper then 1 else 0)cs)
 (V293_TCB_publish_body 108%Z 93%Z 94%Z 95%Z 96%Z)
 (FCPost present(if upper then 1 else 0)cs)FPTid.
Proof.
 intros. unfold FCPre,FCPost.
 change Int.zero with(Int.repr 0).
 change (if present then FCOld else Vnull) with(V293_pub_old_head present 501%positive 56).
 apply V293_OS_TCBInit_publish_finite_body with(table:=501%positive)
 (bo:=501%positive)(obase:=56%Z)(present:=present)(tail:=[(501%positive,Int.repr 112)]);
 try(solve[vm_compute;intuition congruence]);try(solve[destruct upper;lia]);
 try apply FCNodesValid;try apply FCNewMember;try apply FPRCurLINV.
Qed.
(* Single-factor pure cardinality ablation, not a physical heap execution.
   Fixed site count and NoDup stay unchanged; only inclusion is removed. *)
Theorem FCWithoutInclusionCounterexample :
 exists (sites nodes:list nat),length sites=13 /\ NoDup nodes /\ ~(length nodes<255).
Proof.
 exists(seq 0 13). exists(seq 0 255). split;[apply seq_length| ].
 split;[apply seq_NoDup|rewrite seq_length;lia].
Qed.
Print Assumptions FCBodyChecked.
Print Assumptions FCWithoutInclusionCounterexample.
Lemma FCLiteralRaw : forall (present upper:bool) cs,
 PPState(FPMemory(FCInputRows present(if upper then 1 else 0)))cs |=
 V293_rdy_raw_cells(FCInputRows present(if upper then 1 else 0))Aemp.
Proof.
 intros. destruct present,upper;unfold FCInputRows,PPPrivateRows,PPSpareRows,FCSharedRows,FCNodeRows,
 PPDefaults,V293_tcb_active_payload_cells,V293_tcb_publication_spare_cells.
 all:cbn[app map FPMemory V293_rdy_raw_cells];PPRaw.
Qed.
Lemma FCInputRaw : forall (present upper:bool) cs,
 PPState(FCInput present(if upper then 1 else 0))cs |=
 V293_rdy_raw_cells(FCInputRows present(if upper then 1 else 0))Aemp ** FPR.
Proof.
 intros present upper cs. unfold FCInput.
 eapply PPStar;[ |apply FCLiteralRaw|apply PPRSpatial].
   apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 402%positive);[subst b;left| ];
   try(destruct(Pos.eq_dec b 601%positive);[subst b;left|right;left]);
   unfold FCInputRows,PPPrivateRows,PPSpareRows,FCSharedRows,FCNodeRows,PPDefaults,
   V293_tcb_active_payload_cells,V293_tcb_publication_spare_cells,FPCurrent,FPSentinel,FPBytes;
   destruct present,upper;cbn[app map FPMemory];FPOutside.
Qed.
Theorem FCLiteralInput : forall (present upper:bool) cs,
 PPState(FCInput present(if upper then 1 else 0))cs |= FCPre present(if upper then 1 else 0)cs.
Proof.
 intros present upper cs. pose proof(FCInputRaw present upper cs)as S. unfold FCInput in S|-*.
 eapply astar_mono in S;[ |apply FCPhysicalView|intros st HS;exact HS].
 assert(C:PPState(merge(FPMemory(FCInputRows present(if upper then 1 else 0)))(merge FPCurrent FPSentinel))cs |=
 V293_pub_bindings 108%Z 93%Z 94%Z 95%Z 96%Z 208%positive 701%positive 702%positive 703%positive 704%positive **
 ((Amapsto(208%positive,0%Z)(Tptr V293_tcb_type)true PPNew **
 (V293_tcb_publication_new 501%positive 0(if upper then 1 else 0)5 Vnull Vnull **
 V293_tcb_indexed_pool 701%positive 702%positive 703%positive 704%positive(if upper then 1 else 0)
 (FCNodes present)(if present then FCOld else Vnull)0 16 99)) ** FPR)).
 { eapply PPStar with(m1:=emp);[apply map_join_comm;apply map_join_emp|apply PPBindings|exact S]. }
 apply astar_l_aop'_intro with(aop:=spec_done None)in C;[ |reflexivity].
 apply astar_l_aisr_intro with(i:=fun _=>false)in C;[ |reflexivity].
 apply astar_l_aie_intro with(i:=false)in C;[ |reflexivity].
 apply astar_l_ais_intro with(i:=nil)in C;[ |reflexivity].
 apply astar_l_acs_intro with(i:=cs)in C;[ |reflexivity].
 unfold FCPre,V293_tcb_indexed_input. clear -C;sep auto.
Qed.
