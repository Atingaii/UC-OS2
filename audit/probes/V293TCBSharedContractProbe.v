(* Exact builders and typed return-receiver call. These fixtures do NOT
   jointly instantiate the full callee/Hook/GoodI/freshness obligations. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSharedContract.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReservationOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.audit.probes.V293TCBFreePoolProbe.
Require Import CertiOS.tactics.hoareforward.init_spec.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Definition SCReserved : addrval := (209%positive,Int.zero).
Definition SCOwner := V293_create_owned_share 84%positive SCReserved 5.
Lemma SCGoodR : GoodFunAsrt FPR.
Proof. cbn[FPR CurTid LINV V293_witness_li GoodFunAsrt];repeat split;exact I. Qed.
Definition SCExternal Q := V293_tcb_shared_external
 84%positive 401%positive 94%positive 161%positive 162%positive 184%positive
 Q(spec_done None)(fun _=>false)nil nil.
(* Constructor-level check, not a citation to the production goodness lemma. *)
Lemma SCExternalGood : GoodFunAsrt(SCExternal(SCOwner ** FPR)).
Proof.
 cbn[SCExternal V293_tcb_shared_external V293_tcb_success_global_bindings
 SCOwner V293_create_owned_share V293_reservation_owner
 FPR CurTid LINV V293_witness_li GoodFunAsrt];repeat split;exact I.
Qed.
Definition SCPre := V293_tcb_shared_fpre 84%positive SCReserved
 401%positive 94%positive 161%positive 162%positive 184%positive
 5 Vnull Vnull(Vint32(Int.repr 4))(Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7))
 FPR(spec_done None)(fun _=>false)nil nil SCGoodR.
Definition SCPost := V293_tcb_shared_fpost 84%positive SCReserved
 401%positive 94%positive 161%positive 162%positive 184%positive
 5 FPR(spec_done None)(fun _=>false)nil nil SCGoodR.
Definition SCProgram : progunit := fun f=>if Z.eq_dec f 500%Z
 then Some(V293_TCBInit_function 501%Z 502%Z)else None.
Definition SCArgs : vallist :=
 [Vint32(Int.repr 7);Vnull;Vint32(Int.repr 5);Vint32(Int.repr 4);Vnull;Vnull;Vint32(Int.repr 5)].
Definition SCBuiltPre :=
 V293_tcb_internal_pre_cells(Vint32(Int.repr 5))Vnull Vnull
 (Vint32(Int.repr 4))(Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7)) **
 ([|[Vint32(Int.repr 5);Vnull;Vnull;Vint32(Int.repr 4);Vint32(Int.repr 5);Vnull;Vint32(Int.repr 7)]=
 V293_tcb_success_arguments 5 Vnull Vnull(Vint32(Int.repr 4))(Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7))|] **
 SCExternal(SCOwner ** FPR)) ** V293_tcb_internal_domain.
Definition SCBuiltPost result := V293_tcb_internal_post_cells **
 getasrt(SCPost  nil result nil FPTid) ** V293_tcb_internal_domain.
Lemma SCBuilders :
 Some SCBuiltPre=BuildPreI SCProgram 500%Z SCArgs  nil  SCPre FPTid /\
 Some SCBuiltPost=BuildRetI SCProgram 500%Z SCArgs  nil  SCPost FPTid.
Proof. split;reflexivity. Qed.
Lemma SCTyped : dl_vl_match V293_TCBInit_parameters(rev SCArgs)=true.
Proof. reflexivity. Qed.
(* All values and the code are identical except top: Vnull -> integer zero. *)
Definition SCWrongTopArgs : vallist :=
 [Vint32(Int.repr 7);Vnull;Vint32(Int.repr 5);Vint32(Int.repr 4);Vnull;Vint32 Int.zero;Vint32(Int.repr 5)].
Lemma SCWrongTopUntyped : dl_vl_match V293_TCBInit_parameters(rev SCWrongTopArgs)=false.
Proof. reflexivity. Qed.
Lemma SCWrongTopBuilderRejected : BuildPreI SCProgram 500%Z SCWrongTopArgs  nil  SCPre FPTid=None.
Proof. reflexivity. Qed.
Lemma SC66Owner : forall s,
 s |= getasrt(SCPost  nil (Some(Vint32(Int.repr 66))) nil FPTid) <-> s |= SCExternal(SCOwner ** FPR).
Proof.
 intros s;split;intro H.
 - cbn[SCPost V293_tcb_shared_fpost getasrt]in H. destruct H as[H|H];
   apply astar_l_apure_elim in H;destruct H as[Code H];[exact H|discriminate Code].
 - cbn[SCPost V293_tcb_shared_fpost getasrt]. left.
   apply astar_l_apure_intro;[exact H|reflexivity].
Qed.
Lemma SC0ConsumesOwner : forall s,
 s |= getasrt(SCPost  nil (Some(Vint32 Int.zero)) nil FPTid) <-> s |= SCExternal FPR.
Proof.
 intros s;split;intro H.
 - cbn[SCPost V293_tcb_shared_fpost getasrt]in H. destruct H as[H|H];
   apply astar_l_apure_elim in H;destruct H as[Code H];[discriminate Code|exact H].
 - cbn[SCPost V293_tcb_shared_fpost getasrt]. right.
   apply astar_l_apure_intro;[exact H|reflexivity].
Qed.
Lemma SCNoneRejected : forall s,~s |= getasrt(SCPost  nil None nil FPTid).
Proof.
 intros s H. cbn[SCPost V293_tcb_shared_fpost getasrt]in H. destruct H as[H|H];
 apply astar_l_apure_elim in H;destruct H as[Code _];discriminate Code.
Qed.
Lemma SCDomainNoShadow : forall le x,
 eq_dom_env le(getlenvdom V293_tcb_internal_declarations) ->
 (91<=x<=96)%Z -> get le x=None.
Proof. exact V293_tcb_internal_no_shadow_globals. Qed.
Definition SCSpec : funspec := fun f=>if Z.eq_dec f 500%Z
 then Some(SCPre,SCPost,(Tint8,rev V293_TCBInit_argument_types))else None.
Theorem SCActualReceiverCall : forall sd I r ri olderr,
 InfRules SCSpec sd V293_witness_li I r ri
 (SCExternal(SCOwner ** FPR) ** LV 209%Z @ Tint8 |->olderr **
 V293_create_tcb_arguments 5 Vnull Vnull(Vint32(Int.repr 4))(Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7))Aemp)
 (V293_TaskCreateExt_TCB_call 209%Z 500%Z 101%Z 108%Z 205%Z 206%Z 207%Z 208%Z 204%Z)
 (EX result:val,getasrt(SCPost  nil (Some result) nil FPTid) ** LV 209%Z @ Tint8 |->result **
 V293_create_tcb_arguments 5 Vnull Vnull(Vint32(Int.repr 4))(Vint32(Int.repr 5))Vnull(Vint32(Int.repr 7))Aemp)FPTid.
Proof.
 intros. eapply V293_TaskCreateExt_TCB_shared_call with(good:=SCGoodR).
 - constructor.
 - lia.
 - vm_compute;repeat split;reflexivity.
 - apply FPRCurLINV.
 - reflexivity.
Qed.
