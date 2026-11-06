(* Audit-only: independent constructor controls and concrete typed Hook Spec.
   Full body remains conditional on freshness/returns/Hook implementations. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookFrame.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEnabledPublication.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEnabledHook.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFullPriority.
Require Import CertiOS.certiucos.v293.proofs.V293TCBOwnedPriority.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReservationOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateJointShared.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBAllocatedFields.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.audit.probes.V293TCBFreePoolProbe.
Require Import CertiOS.audit.probes.V293TCBAllocatedFieldsProbe.
Require Import CertiOS.audit.probes.V293TCBEnabledHookProbe.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Definition HFToken : addrval := (209%positive,Int.zero).
Definition HFOwner := V293_create_owned_share 84%positive HFToken 5.
Definition HFGlobals := V293_tcb_publication_globals 94%positive 161%positive 162%positive 184%positive.
(* Both use the original constructors, not the new accepted/rejected lemmas. *)
Lemma HFPositive : GoodFunAsrt(HFOwner ** FPR).
Proof. cbn[HFOwner HFToken V293_create_owned_share V293_reservation_owner FPR CurTid LINV V293_witness_li GoodFunAsrt]. repeat split;exact I. Qed.
Lemma HFNegative : ~ GoodFunAsrt(HFOwner ** (HFGlobals ** FPR)).
Proof. intro H. exact(proj1(proj1(proj2 H))). Qed.
Lemma HFOwnerOnly : GoodFunAsrt(HFOwner ** Aemp).
Proof. cbn[HFOwner V293_create_owned_share V293_reservation_owner GoodFunAsrt];auto. Qed.
Lemma HFGlobalOnly : GoodFunAsrt(Agvarenv 93%Z(Tptr V293_tcb_type)(94%positive,0%Z)).
Proof. exact I. Qed.
Lemma HFLocalOnly : ~ GoodFunAsrt(A_notin_lenv 93%Z).
Proof. exact(fun H=>H). Qed.
Definition HFGE : env :=
 set(set(set(sig 93%Z(94%positive,Tptr V293_tcb_type))
 94%Z(161%positive,Tint8))95%Z(162%positive,Tarray Tint8 2))96%Z(184%positive,Tint8).
Definition HFEnvState le : RstateOP :=
 (HFGE,le,empmem,(fun _=>false),(true,[],[]),empabst,spec_done None).
Lemma HFGlobalsLiteral : HFEnvState emp |= HFGlobals.
Proof.
 unfold HFGlobals,V293_tcb_publication_globals.
 repeat split;try reflexivity.
 all:try (intro H;destruct H as[v H];vm_compute in H;discriminate).
 all: first[solve[exists 94%positive;repeat split;vm_compute;reflexivity]|solve[exists 161%positive;repeat split;vm_compute;reflexivity]|solve[exists 162%positive;repeat split;vm_compute;reflexivity]|solve[exists 184%positive;repeat split;vm_compute;reflexivity]].
Qed.
Definition HFShadow : env := sig 93%Z(701%positive,Tint8).
Lemma HFShadowRejected : ~ (HFEnvState HFShadow |= HFGlobals).
Proof.
 intro H. destruct H as[[NotIn _] Rest]. apply NotIn.
 exists(701%positive,Tint8). reflexivity.
Qed.
Lemma HFGlobalsFrame : GoodFrm HFGlobals.
Proof. cbn[HFGlobals V293_tcb_publication_globals GoodFrm];tauto. Qed.
(* Physical owner half and caller-only lookup facts can coexist. Changing
   only the local binding rejects the frame; pointer bytes are unchanged. *)
Definition HFMemory := V293_encoded_memory 84%positive 20%Z false
 (encode_val(Tptr V293_tcb_type)(Vptr HFToken)).
Definition HFCallerState le : RstateOP :=
 (HFGE,le,HFMemory,(fun _=>false),(true,[],[]),empabst,spec_done None).
Lemma HFCallerLiteral : HFCallerState emp |= HFOwner ** HFGlobals.
Proof.
 apply sat_split'. exists HFMemory. exists empmem. exists empabst. exists empabst.
 split;[apply map_join_emp| ]. split;[apply map_join_emp| ]. split.
 - split;[change(mapstoval(84%positive,20%Z)(Tptr V293_tcb_type)false(Vptr HFToken)HFMemory);
   apply V293_encoded_memory_mapsto|reflexivity].
 - exact HFGlobalsLiteral.
Qed.
Lemma HFCallerShadowRejected : ~ (HFCallerState HFShadow |= HFOwner ** HFGlobals).
Proof.
 intro H. apply sat_split in H. destruct H as(m1&m2&o1&o2&JM&JO&Owner&Globals).
 destruct Globals as[[NotIn _] Rest]. apply NotIn.
 exists(701%positive,Tint8). reflexivity.
Qed.
Definition HFFrame := HFGlobals **
 V293_tcb_priority_caller_frame 401%positive 208%positive 209%positive
 201%positive 202%positive 203%positive 204%positive 205%positive 206%positive 207%positive
 (Vint32 Int.zero) AFTop AFBottom AFIdentity AFSize Vnull AFOptions.
Lemma HFFrameGood : GoodFrm HFFrame.
Proof. cbn[HFFrame GoodFrm]. split;[apply HFGlobalsFrame|apply V293_tcb_priority_caller_frame_good]. Qed.
Definition HFPre1 cs := V293_tcb_enabled_hook_fpre 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions
 (HFOwner ** FPR)(spec_done None)(fun _=>false)nil cs FPTid HFPositive.
Definition HFPost1 cs := V293_tcb_enabled_hook_fpost 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions
 (HFOwner ** FPR)(spec_done None)(fun _=>false)nil cs FPTid HFPositive.
Definition HFPre2 cs := V293_tcb_enabled_hook_fpre 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions
 FPR(spec_done None)(fun _=>false)nil cs FPTid(proj2 HFPositive).
Definition HFPost2 cs := V293_tcb_enabled_hook_fpost 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions
 FPR(spec_done None)(fun _=>false)nil cs FPTid(proj2 HFPositive).
Definition HFSpec cs : funspec := fun f=>if Z.eq_dec f 990%Z then
 Some(HFPre1 cs,HFPost1 cs,(Tvoid,[Tptr V293_tcb_type]))else if Z.eq_dec f 991%Z then
 Some(HFPre2 cs,HFPost2 cs,(Tvoid,[Tptr V293_tcb_type]))else None.
Lemma HFLookup1 : forall cs,HFSpec cs 990%Z=Some(HFPre1 cs,HFPost1 cs,(Tvoid,[Tptr V293_tcb_type])).
Proof. intro;reflexivity. Qed.
Lemma HFLookup2 : forall cs,HFSpec cs 991%Z=Some(HFPre2 cs,HFPost2 cs,(Tvoid,[Tptr V293_tcb_type])).
Proof. intro;reflexivity. Qed.
Definition HFInv := V293_create_joint_inv 82%positive 95%positive 84%positive
 94%positive 161%positive 162%positive 184%positive 182%positive HFToken.
Definition HFPriority R b off next cs :=
 V293_tcb_priority_state 84%positive 201%positive 208%positive 5(Vptr(b,off))
 (V293_tcb_allocated_initialized b off next 5 AFTop AFBottom AFIdentity AFSize Vnull AFOptions **
 (R ** HFFrame))(spec_done None)(fun _=>false)true nil cs.
Theorem HFCall1 : forall sd r ri b off next cs,
 InfRules(HFSpec cs)sd V293_witness_li HFInv r ri(HFPriority(HFOwner ** FPR)b off next cs)
 (scall 990%Z[evar 108%Z])(HFPriority(HFOwner ** FPR)b off next cs)FPTid.
Proof.
 intros. apply V293_tcb_priority_first_hook with(good:=HFPositive).
 - apply HFFrameGood.
 - apply V293_star_CurLINV_r;apply FPRCurLINV.
 - apply HFLookup1.
Qed.
Theorem HFCall2 : forall sd r ri b off next cs,
 InfRules(HFSpec cs)sd V293_witness_li HFInv r ri(HFPriority FPR b off next cs)
 (scall 991%Z[evar 108%Z])(HFPriority FPR b off next cs)FPTid.
Proof.
 intros. apply V293_tcb_priority_first_hook with(good:=proj2 HFPositive).
 - apply HFFrameGood.
 - apply FPRCurLINV.
 - apply HFLookup2.
Qed.
Print Assumptions HFNegative.
Print Assumptions HFGlobalsLiteral.
Print Assumptions HFCall1.
Print Assumptions HFCall2.
Print Assumptions HFCallerLiteral.
Print Assumptions HFCallerShadowRejected.
