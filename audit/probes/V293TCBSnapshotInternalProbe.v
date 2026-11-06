(* Composition tests intentionally reuse frozen Stage93/94 byte fixtures. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSnapshotInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TCBSuccessInternalProbe.
Require Import CertiOS.audit.probes.V293TCBUnifiedInternalProbe.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition SnapshotFpre present cs :=
 V293_tcb_snapshot_fpre SuccessHead (UnifiedEmptyFpre cs)(SuccessInternalFpre present cs).
Definition SnapshotFpost present cs :=
 V293_tcb_snapshot_fpost SuccessHead (UnifiedEmptyFpost cs)(SuccessInternalFpost present cs).
Definition SnapshotSuccessPre present cs saved :=
 V293_tcb_internal_pre_cells (V293_byteval 11) Vnull Vnull (Vint32 Int.zero)
 (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) **
 getasrt(SnapshotFpre present cs SuccessArguments [logic_val saved] SuccessTid) ** V293_tcb_internal_domain.
Definition SnapshotEmptyPre present cs saved :=
 V293_tcb_internal_pre_cells (Vint32(Int.repr 11)) Vnull Vnull
 (Vint32(Int.repr 4)) (Vint32(Int.repr 5)) Vnull (Vint32(Int.repr 7)) **
 getasrt(SnapshotFpre present cs (rev InternalArgs) [logic_val saved] SuccessTid) ** V293_tcb_internal_domain.
Definition SnapshotPost present cs saved result := V293_tcb_internal_post_cells **
 getasrt(SnapshotFpost present cs SuccessArguments result [logic_val saved] SuccessTid) ** V293_tcb_internal_domain.
Theorem SnapshotBuildersBoth : forall present cs,
 Some(SnapshotSuccessPre present cs SuccessHead)=BuildPreI SuccessProgram 900%Z
 (rev SuccessArguments)[logic_val SuccessHead](SnapshotFpre present cs)SuccessTid /\
 Some(SnapshotEmptyPre present cs Vnull)=BuildPreI SuccessProgram 900%Z
 InternalArgs[logic_val Vnull](SnapshotFpre present cs)SuccessTid /\
 Some(SnapshotPost present cs SuccessHead)=BuildRetI SuccessProgram 900%Z
 (rev SuccessArguments)[logic_val SuccessHead](SnapshotFpost present cs)SuccessTid /\
 Some(SnapshotPost present cs Vnull)=BuildRetI SuccessProgram 900%Z
 InternalArgs[logic_val Vnull](SnapshotFpost present cs)SuccessTid.
Proof. intros. repeat split;reflexivity. Qed.
Lemma SnapshotGuardResources : forall A B D (condition:Prop),
 condition -> A ** B ** D ==> A ** ([|condition|] ** B) ** D.
Proof.
 intros A B D condition TrueCondition s H.
 assert(K:s |= [|condition|] ** (A ** B ** D)).
 { apply astar_l_apure_intro;assumption. }
 clear -K. sep auto.
Qed.
Theorem SnapshotLiteralSuccessEntry : forall present cs,
 SuccessState(SuccessWhole false present)cs |= SnapshotSuccessPre present cs SuccessHead.
Proof.
 intros. apply SnapshotGuardResources;[reflexivity|apply SuccessLiteralBuilderEntry].
Qed.
Theorem SnapshotLiteralEmptyEntry : forall present cs,
 InternalState(merge InternalLocalsMemory InternalOuterMemory)cs |= SnapshotEmptyPre present cs Vnull.
Proof. intros. apply InternalLiteralBuilderEntry. Qed.
Theorem SnapshotLiteralSuccessReturn : forall present cs,
 SuccessState(SuccessWhole true present)cs |= SnapshotPost present cs SuccessHead(Some(Vint32 Int.zero)).
Proof.
 intros. apply SnapshotGuardResources;[reflexivity|apply SuccessLiteralBuilderReturn].
Qed.
Theorem SnapshotLiteralEmptyReturn : forall present cs,
 InternalState(merge InternalLocalsMemory InternalOuterMemory)cs |= SnapshotPost present cs Vnull(Some(Vint32(Int.repr 66))).
Proof.
 intros present cs. pose proof(UnifiedLiteralEmptyReturn present cs) as H.
 apply UnifiedPostCases in H. destruct H as [H|H];[exact H| ].
 pose proof(SuccessBuilderPostCode _ _ _ _ H) as Bad. discriminate Bad.
Qed.
Lemma SnapshotSuccessEntryRead : forall present cs saved s,
 s |= SnapshotSuccessPre present cs saved ->
 load(Tptr V293_tcb_type)(getmem s)(210%positive,0%Z)=Some saved.
Proof.
 intros present cs saved s H. unfold SnapshotSuccessPre in H.
 eapply V293_star_load_r;[ |exact H]. intros st H1.
 eapply V293_star_load_l;[ |exact H1]. intros st1 H2.
 eapply V293_tcb_snapshot_pre_load with (allocated:=SuccessHead)
 (empty:=UnifiedEmptyFpre cs) (ready:=SuccessInternalFpre present cs)
 (vl:=SuccessArguments) (lg:=[logic_val saved]) (tid:=SuccessTid);[ | |reflexivity|exact H2].
 - intros args ghosts task branchstate Owned. eapply V293_tcb_empty_pre_head
   with (vl:=args) (lg:=ghosts) (tid:=task) (good:=SuccessRFun);eassumption.
 - intros args ghosts task branchstate Owned. eapply V293_tcb_success_pre_head
   with (vl:=args) (lg:=ghosts) (tid:=task) (good:=SuccessRFun);eassumption.
Qed.
Lemma SnapshotEmptyEntryRead : forall present cs saved s,
 s |= SnapshotEmptyPre present cs saved ->
 load(Tptr V293_tcb_type)(getmem s)(210%positive,0%Z)=Some saved.
Proof.
 intros present cs saved s H. unfold SnapshotEmptyPre in H.
 eapply V293_star_load_r;[ |exact H]. intros st H1.
 eapply V293_star_load_l;[ |exact H1]. intros st1 H2.
 eapply V293_tcb_snapshot_pre_load with (allocated:=SuccessHead)
 (empty:=UnifiedEmptyFpre cs) (ready:=SuccessInternalFpre present cs)
 (vl:=(rev InternalArgs)) (lg:=[logic_val saved]) (tid:=SuccessTid);[ | |reflexivity|exact H2].
 - intros args ghosts task branchstate Owned. eapply V293_tcb_empty_pre_head
   with (vl:=args) (lg:=ghosts) (tid:=task) (good:=SuccessRFun);eassumption.
 - intros args ghosts task branchstate Owned. eapply V293_tcb_success_pre_head
   with (vl:=args) (lg:=ghosts) (tid:=task) (good:=SuccessRFun);eassumption.
Qed.
Lemma SnapshotPostResult : forall present cs saved s result,
 s |= SnapshotPost present cs saved result ->
 (saved=Vnull /\ result=Some(Vint32(Int.repr 66))) \/
 (saved=SuccessHead /\ result=Some(Vint32 Int.zero)).
Proof.
 intros present cs saved s result H. unfold SnapshotPost in H.
 apply astar_prop in H. destruct H as [s1 [s2 [_ H]]].
 apply astar_prop in H. destruct H as [s3 [s4 [Owned _]]].
 eapply V293_tcb_snapshot_post_code with (allocated:=SuccessHead)
 (empty:=UnifiedEmptyFpost cs) (ready:=SuccessInternalFpost present cs)
 (vl:=SuccessArguments) (lg:=[logic_val saved]) (tid:=SuccessTid);[ | |reflexivity|exact Owned].
 - intros args ghosts task st r Branch. eapply V293_tcb_empty_post_code
   with (vl:=args) (lg:=ghosts) (tid:=task) (good:=SuccessRFun);eassumption.
 - intros args ghosts task st r Branch. eapply V293_tcb_success_post_code
   with (vl:=args) (lg:=ghosts) (tid:=task) (good:=SuccessRFun);eassumption.
Qed.
Theorem SnapshotNullCode : forall present cs s result,
 s |= SnapshotPost present cs Vnull result -> result=Some(Vint32(Int.repr 66)).
Proof.
 intros present cs s result H. apply SnapshotPostResult in H.
 destruct H as [[_ Code]|[Bad _]];[exact Code|discriminate Bad].
Qed.
Theorem SnapshotPointerCode : forall present cs s pointer result,
 s |= SnapshotPost present cs (Vptr pointer) result -> result=Some(Vint32 Int.zero).
Proof.
 intros present cs s pointer result H. apply SnapshotPostResult in H.
 destruct H as [[Bad _]|[_ Code]];[discriminate Bad|exact Code].
Qed.
Theorem SnapshotRejectCrossCodes : forall present cs s,
 ~s |= SnapshotPost present cs Vnull(Some(Vint32 Int.zero)) /\
 ~s |= SnapshotPost present cs SuccessHead(Some(Vint32(Int.repr 66))).
Proof.
 intros. split;intro H.
 - apply SnapshotNullCode in H. discriminate H.
 - apply SnapshotPointerCode in H. discriminate H.
Qed.
Theorem SnapshotRejectNone : forall present cs saved s,
 ~s |= SnapshotPost present cs saved None.
Proof. intros present cs saved s H. apply SnapshotPostResult in H. destruct H as [[_ Bad]|[_ Bad]];discriminate Bad. Qed.
Definition SnapshotWrongHead := Vptr(301%positive,Int.repr 129).
Theorem SnapshotRejectWrongPointer : forall present cs s,
 ~s |= SnapshotSuccessPre present cs SnapshotWrongHead.
Proof.
 intros present cs s H. unfold SnapshotSuccessPre in H.
 apply astar_prop in H. destruct H as [s1 [s2 [_ H]]].
 apply astar_prop in H. destruct H as [s3 [s4 [Owned _]]].
 unfold SnapshotFpre,V293_tcb_snapshot_fpre,SnapshotWrongHead,V293_tcb_guard_fpre in Owned.
 cbn [getasrt] in Owned. apply astar_l_apure_elim in Owned.
 destruct Owned as [Equal _]. discriminate Equal.
Qed.
Theorem SnapshotMissingGhostRejected : forall present cs s,
 ~s |= getasrt(SnapshotFpre present cs SuccessArguments [] SuccessTid).
Proof. intros. exact(fun H=>H). Qed.
Theorem SnapshotWrongGhostTypeRejected : forall present cs s,
 ~s |= getasrt(SnapshotFpre present cs SuccessArguments [logic_ie false] SuccessTid).
Proof. intros. exact(fun H=>H). Qed.
Theorem SnapshotIntegerGhostRejected : forall present cs s,
 ~s |= getasrt(SnapshotFpre present cs SuccessArguments [logic_val(Vint32 Int.zero)] SuccessTid).
Proof. intros. exact(fun H=>H). Qed.
Theorem SnapshotMultipleGhostsRejected : forall present cs s,
 ~s |= getasrt(SnapshotFpre present cs SuccessArguments [logic_val Vnull;logic_val SuccessHead] SuccessTid).
Proof. intros. exact(fun H=>H). Qed.
Theorem SnapshotUnionWouldLoseCorrelation : forall present cs,
 SuccessState(SuccessWhole true present)cs |= UnifiedPost present cs(Some(Vint32 Int.zero)) /\
 ~SuccessState(SuccessWhole true present)cs |= SnapshotPost present cs Vnull(Some(Vint32 Int.zero)).
Proof.
 intros. split;[apply UnifiedLiteralSuccessReturn|apply(proj1(SnapshotRejectCrossCodes present cs _))].
Qed.
Theorem SnapshotNeutralizedGuardAcceptsForgery : forall present cs,
 SuccessState(SuccessWhole false present)cs |=
 V293_tcb_internal_pre_cells (V293_byteval 11) Vnull Vnull (Vint32 Int.zero)
 (Vint32(Int.repr 128)) Vnull (Vint32 Int.zero) **
 getasrt(V293_tcb_guard_fpre True (SuccessInternalFpre present cs)
 SuccessArguments [logic_val SnapshotWrongHead] SuccessTid) ** V293_tcb_internal_domain.
Proof.
 intros. apply SnapshotGuardResources;[exact I|apply SuccessLiteralBuilderEntry].
Qed.

Theorem SnapshotSuccessContractChecked : forall present cs,
 InfRules (SuccessDeclaredSpec present cs) V293_scheduler V293_witness_li V293_shared_inv
 (SnapshotPost present cs SuccessHead) Afalse (SnapshotSuccessPre present cs SuccessHead)
 (V293_TCBInit_function_body 501%Z 502%Z) Afalse SuccessTid.
Proof.
 intros present cs.
 eapply V293_OS_TCBInit_snapshot_internal_contract
 with (P:=SuccessProgram) (f:=900%Z) (vl:=rev SuccessArguments) (lg:=[logic_val SuccessHead])
 (Hfun:=SuccessRFun) (old:=fun _=>Vundef) (oldprev:=Vundef) (oldback:=Vundef)
 (slot:=Vundef) (table:=211%positive) (bg:=210%positive) (bt:=301%positive)
 (base:=128%Z) (p:=11) (top:=Vnull) (bottom:=Vnull) (identity:=Vint32 Int.zero)
 (size:=Vint32(Int.repr 128)) (ext:=Vnull) (options:=Vint32 Int.zero) (next:=SuccessNext)
 (bh:=212%positive) (bgrp:=213%positive) (br:=214%positive) (bn:=215%positive)
 (oldblock:=301%positive) (oldbase:=256%Z) (present:=present) (g:=1) (row:=129) (n:=254)
 (aop:=spec_done None) (isr:=fun _=>false) (is:=[]) (cs:=cs).
 - apply SuccessGoodIInhabited.
 - lia.
 - lia.
 - unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia.
 - lia.
 - unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia.
 - repeat split;reflexivity.
 - reflexivity.
 - lia.
 - lia.
 - lia.
 - apply SuccessRGood.
 - apply SuccessRCurLINV.
 - apply SuccessInitLookup.
 - apply SuccessCreateLookup.
 - reflexivity.
 - apply (proj1(SnapshotBuildersBoth present cs)).
 - apply (proj1(proj2(proj2(SnapshotBuildersBoth present cs)))).
Qed.

Theorem SnapshotEmptyContractChecked : forall present cs,
 InfRules (SuccessDeclaredSpec present cs) V293_scheduler V293_witness_li V293_shared_inv
 (SnapshotPost present cs Vnull) Afalse (SnapshotEmptyPre present cs Vnull)
 (V293_TCBInit_function_body 501%Z 502%Z) Afalse SuccessTid.
Proof.
 intros present cs.
 eapply V293_OS_TCBInit_snapshot_internal_contract
 with (P:=SuccessProgram) (f:=900%Z) (vl:=InternalArgs) (lg:=[logic_val Vnull])
 (Hfun:=SuccessRFun) (old:=fun _=>Vundef) (oldprev:=Vundef) (oldback:=Vundef)
 (slot:=Vundef) (table:=211%positive) (bg:=210%positive) (bt:=301%positive)
 (base:=128%Z) (p:=11) (top:=Vnull) (bottom:=Vnull) (identity:=Vint32 Int.zero)
 (size:=Vint32(Int.repr 128)) (ext:=Vnull) (options:=Vint32 Int.zero) (next:=SuccessNext)
 (bh:=212%positive) (bgrp:=213%positive) (br:=214%positive) (bn:=215%positive)
 (oldblock:=301%positive) (oldbase:=256%Z) (present:=present) (g:=1) (row:=129) (n:=254)
 (aop:=spec_done None) (isr:=fun _=>false) (is:=[]) (cs:=cs).
 - apply SuccessGoodIInhabited.
 - lia.
 - lia.
 - unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia.
 - lia.
 - unfold Int.max_unsigned,Int.modulus,Int.wordsize;cbn;lia.
 - repeat split;reflexivity.
 - reflexivity.
 - lia.
 - lia.
 - lia.
 - apply SuccessRGood.
 - apply SuccessRCurLINV.
 - apply SuccessInitLookup.
 - apply SuccessCreateLookup.
 - reflexivity.
 - apply (proj1(proj2(SnapshotBuildersBoth present cs))).
 - apply (proj2(proj2(proj2(SnapshotBuildersBoth present cs)))).
Qed.

