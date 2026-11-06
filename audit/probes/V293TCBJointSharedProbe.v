(* Independent literal byte entry reused unchanged from the frozen initialization
   probe; it does not depend on the joint invariant or its folds. *)
Require Import CertiOS.audit.probes.V293InitChainProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TCBJointShared.
Require Import CertiOS.certiucos.v293.proofs.V293InitChain.
Require Import CertiOS.certiucos.v293.proofs.V293InitMisc.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteSites.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFiniteEnabled.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateReservationOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.code.V293OSInitMisc.
Require Import CertiOS.certiucos.v293.code.V293OSInitRdyList.
Require Import CertiOS.certiucos.v293.code.V293OSInitChain.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBCall.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBClear.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition JPCore := V293_tcb_joint_core 82%positive 95%positive 84%positive
 94%positive 161%positive 162%positive 184%positive (209%positive,Int.zero).
Definition JPInv := V293_tcb_joint_inv 82%positive 95%positive 84%positive
 94%positive 161%positive 162%positive 184%positive (209%positive,Int.zero).
Theorem JPActualInitialization : forall ks, exists (Mmisc Mrdy Mf:mem)(bri bi bn b1 b2:block),
 cstepstar ChainProgram (curs(V293_init_three_calls 201%Z 202%Z 203%Z),(kenil,ks))
  (ChainGE,ChainCaller,ChainEntryMemory)(curs(sskip None),(kenil,ks))(ChainGE,ChainCaller,Mf) /\
 ChainState Mf |= JPCore ** V293_rdy_raw_cells ChainFrame Atrue /\
 get Mrdy(bri,0%Z)=None /\
 (forall c tp k,In(c,tp)[(bi,Tint8);(bn,Tint8);(b1,Tptr V293_tcb_type);(b2,Tptr V293_tcb_type)] ->
  k<typelen tp -> get Mf(c,Z.of_nat k)=None).
Proof.
 intro ks.
 destruct (V293_OSInit_three_calls_joint
   (Build_V293_init_slot 1004%Z Tint8 184%positive) 184%positive (209%positive,Int.zero) ChainSlots (repeat Vundef 728)
   (repeat (Vint32 (Int.repr 255)) 52) ChainFrame ChainProgram ks ChainGE ChainCaller ChainEntryMemory
   (fun _=>false) (false,nil,nil) emp (spec_done None)
   201%Z 202%Z 203%Z 204%Z 11%Z 12%Z 21%Z 22%Z 23%Z 24%Z 25%Z 26%Z 41%Z
   161%positive 162%positive 163%positive 164%positive 165%positive 166%positive
   31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z 82%positive 84%positive 94%positive 95%positive
   (Vint32 (Int.repr 7)) (Vint32 (Int.repr 3)) Vundef (Vint32 (Int.repr 5))
   (Vint32 (Int.repr 9)) (Vptr (211%positive,Int.zero)) (Vptr (212%positive,Int.zero))
   (Vptr (121%positive,Int.zero)) (Vptr (122%positive,Int.zero))
   ltac:(unfold ChainSlots,V293_InitMisc_slots;cbn;tauto) ltac:(reflexivity) ltac:(reflexivity)
   ltac:(unfold ChainSlots,V293_InitMisc_slots;repeat (apply Forall_cons;[unfold V293_init_scalar;cbn;auto | ]);apply Forall_nil)
   ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
   ltac:(discriminate) ltac:(lia) ltac:(lia) ltac:(lia)
   ChainReadyEnvironment ChainTCBEnvironment ltac:(intros;reflexivity) ltac:(reflexivity)
   ltac:(apply repeat_length) ltac:(apply repeat_length) ChainLiteralFullEntry)
   as (Mmisc&Mrdy&Mf&bri&bi&bn&b1&b2&Exec&MiscExec&ReadyExec&TCBExec&Final&ReadyFreed&TCBFreed).
 exists Mmisc. exists Mrdy. exists Mf. exists bri. exists bi. exists bn. exists b1. exists b2.
 split;[exact Exec| ]. split;[exact Final| ]. split;assumption.
Qed.
Theorem JPAllPriorities : forall p,p<13 ->
 JPCore <==> V293_reservation_pool(84%positive,(4*Z.of_nat p)%Z)(209%positive,Int.zero) **
 V293_tcb_joint_priority_rest 82%positive 95%positive 84%positive
 94%positive 161%positive 162%positive 184%positive (209%positive,Int.zero)p.
Proof. intros;apply V293_tcb_joint_priority_view;assumption. Qed.
Theorem JPBothRows : forall y,y<2 ->
 JPCore <==> V293_tcb_finite_shared 82%positive 94%positive 161%positive 162%positive 184%positive y **
 V293_tcb_joint_publication_rest 82%positive 95%positive 84%positive (209%positive,Int.zero).
Proof. intros;apply V293_tcb_joint_publication_view;assumption. Qed.
Theorem JPActualPriorityViews : forall ks,exists Mf,
 cstepstar ChainProgram(curs(V293_init_three_calls 201%Z 202%Z 203%Z),(kenil,ks))
  (ChainGE,ChainCaller,ChainEntryMemory)(curs(sskip None),(kenil,ks))(ChainGE,ChainCaller,Mf) /\
 (forall p,p<13 -> ChainState Mf |=
  (V293_reservation_pool(84%positive,(4*Z.of_nat p)%Z)(209%positive,Int.zero) **
   V293_tcb_joint_priority_rest 82%positive 95%positive 84%positive
   94%positive 161%positive 162%positive 184%positive (209%positive,Int.zero)p) **
  V293_rdy_raw_cells ChainFrame Atrue).
Proof.
 intro ks. destruct(JPActualInitialization ks)as(Mmisc&Mrdy&Mf&bri&bi&bn&b1&b2&Exec&Joint&FR&FT).
 exists Mf. split;[exact Exec| ]. intros p Bound.
 eapply astar_mono;[intros st HS;exact(proj1(JPAllPriorities p Bound st)HS)|intros st HS;exact HS|exact Joint].
Qed.
(* The permission ablation changes only the four permission bits of one
   non-null slot; every pointer byte, address and outside byte stays fixed. *)
Definition JPToken : addrval := (209%positive,Int.zero).
Definition JPSlotMemory perm := V293_encoded_memory 84%positive 16%Z perm
 (encode_val(Tptr V293_tcb_type)(Vptr JPToken)).
Definition JPSlotState perm := V293_wstate ChainGE ChainCaller(JPSlotMemory perm).
Lemma JPLiteralReserved : forall perm,JPSlotState perm |=
 Amapsto(84%positive,16%Z)(Tptr V293_tcb_type)perm(Vptr JPToken).
Proof. intro. split;[apply V293_encoded_memory_mapsto|reflexivity]. Qed.
Theorem JPHalfPool : JPSlotState false |= V293_reservation_pool(84%positive,16%Z)JPToken.
Proof.
 exists(Vptr JPToken). apply astar_l_apure_intro;[ |reflexivity].
 rewrite V293_reservation_permission_reserved. apply JPLiteralReserved.
Qed.
Theorem JPReservedShareCompatible : JPSlotState true |=
 V293_reservation_owner(84%positive,16%Z)JPToken ** V293_reservation_pool(84%positive,16%Z)JPToken.
Proof. apply V293_reservation_publish. apply JPLiteralReserved. Qed.
Theorem JPFullPoolOverbookingRejected : forall s,
 s |= V293_reservation_owner(84%positive,16%Z)JPToken **
 Amapsto(84%positive,16%Z)(Tptr V293_tcb_type)true(Vptr JPToken) -> False.
Proof. intros s H. apply astar_comm in H. eapply V293_reservation_full_half_conflict;exact H. Qed.
Ltac JPConcreteMemory :=
 vm_compute;repeat match goal with
 | |- context[addr_eq_dec ?a ?b]=>destruct(addr_eq_dec a b);try congruence
 end;reflexivity.
Theorem JPPermissionOnlyControl :
 get(JPSlotMemory true)(84%positive,16%Z)=Some(true,Pointer 209%positive Int.zero 3) /\
 get(JPSlotMemory false)(84%positive,16%Z)=Some(false,Pointer 209%positive Int.zero 3) /\
 (forall k,k<4 ->
 option_map snd(get(JPSlotMemory true)(84%positive,(16+Z.of_nat k)%Z))=
 option_map snd(get(JPSlotMemory false)(84%positive,(16+Z.of_nat k)%Z))) /\
 (forall b j,b<>84%positive \/ (j<16)%Z \/ (20<=j)%Z ->
 get(JPSlotMemory true)(b,j)=None /\ get(JPSlotMemory false)(b,j)=None).
Proof.
 split;[JPConcreteMemory| ]. split;[JPConcreteMemory| ]. split.
 - intros k Bound. assert(k=0\/k=1\/k=2\/k=3)by lia.
   repeat destruct H as[H|H];subst k;JPConcreteMemory.
 - intros b j Away. split;unfold JPSlotMemory;apply V293_encoded_memory_outside;cbn[length encode_val inj_pointer];exact Away.
Qed.
Theorem JPNullFullControl :
 V293_wstate ChainGE ChainCaller
 (V293_encoded_memory 84%positive 16%Z true(encode_val(Tptr V293_tcb_type)Vnull)) |=
 V293_reservation_pool(84%positive,16%Z)JPToken.
Proof. apply V293_reservation_pool_null. split;[apply V293_encoded_memory_mapsto|reflexivity]. Qed.
Print Assumptions JPActualInitialization.
Print Assumptions JPPermissionOnlyControl.
Print Assumptions JPFullPoolOverbookingRejected.
