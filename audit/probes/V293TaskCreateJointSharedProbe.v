(* Independent literal byte entry reused unchanged from the frozen initialization
   probe; it does not depend on the joint invariant or its folds. *)
Require Import CertiOS.audit.probes.V293InitChainProbe.
Require Import CertiOS.audit.probes.V293TCBJointSharedProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateJointShared.
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
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Import ListNotations.
Local Open Scope nat_scope.
Definition CPCore := V293_create_joint_core 82%positive 95%positive 84%positive
 94%positive 161%positive 162%positive 184%positive 182%positive (209%positive,Int.zero).
Theorem CPActualInitialization : forall ks, exists (Mmisc Mrdy Mf:mem)(bri bi bn b1 b2:block),
 cstepstar ChainProgram (curs(V293_init_three_calls 201%Z 202%Z 203%Z),(kenil,ks))
  (ChainGE,ChainCaller,ChainEntryMemory)(curs(sskip None),(kenil,ks))(ChainGE,ChainCaller,Mf) /\
 ChainState Mf |= CPCore ** V293_rdy_raw_cells ChainFrame Atrue /\
 get Mrdy(bri,0%Z)=None /\
 (forall c tp k,In(c,tp)[(bi,Tint8);(bn,Tint8);(b1,Tptr V293_tcb_type);(b2,Tptr V293_tcb_type)] ->
  k<typelen tp -> get Mf(c,Z.of_nat k)=None).
Proof.
 intro ks.
 destruct (V293_OSInit_three_calls_creator_joint
   (Build_V293_init_slot 1004%Z Tint8 184%positive)
   (Build_V293_init_slot 1002%Z Tint8 182%positive) 184%positive 182%positive (209%positive,Int.zero) ChainSlots (repeat Vundef 728)
   (repeat (Vint32 (Int.repr 255)) 52) ChainFrame ChainProgram ks ChainGE ChainCaller ChainEntryMemory
   (fun _=>false) (false,nil,nil) emp (spec_done None)
   201%Z 202%Z 203%Z 204%Z 11%Z 12%Z 21%Z 22%Z 23%Z 24%Z 25%Z 26%Z 41%Z
   161%positive 162%positive 163%positive 164%positive 165%positive 166%positive
   31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z 82%positive 84%positive 94%positive 95%positive
   (Vint32 (Int.repr 7)) (Vint32 (Int.repr 3)) Vundef (Vint32 (Int.repr 5))
   (Vint32 (Int.repr 9)) (Vptr (211%positive,Int.zero)) (Vptr (212%positive,Int.zero))
   (Vptr (121%positive,Int.zero)) (Vptr (122%positive,Int.zero))
   ltac:(unfold ChainSlots,V293_InitMisc_slots;cbn;tauto) ltac:(reflexivity) ltac:(reflexivity)
   ltac:(unfold ChainSlots,V293_InitMisc_slots;cbn;tauto) ltac:(reflexivity) ltac:(reflexivity) ltac:(discriminate)
   ltac:(unfold ChainSlots,V293_InitMisc_slots;repeat (apply Forall_cons;[unfold V293_init_scalar;cbn;auto | ]);apply Forall_nil)
   ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity) ltac:(reflexivity)
   ltac:(discriminate) ltac:(lia) ltac:(lia) ltac:(lia)
   ChainReadyEnvironment ChainTCBEnvironment ltac:(intros;reflexivity) ltac:(reflexivity)
   ltac:(apply repeat_length) ltac:(apply repeat_length) ChainLiteralFullEntry)
   as (Mmisc&Mrdy&Mf&bri&bi&bn&b1&b2&Exec&MiscExec&ReadyExec&TCBExec&Final&ReadyFreed&TCBFreed).
 exists Mmisc. exists Mrdy. exists Mf. exists bri. exists bi. exists bn. exists b1. exists b2.
 split;[exact Exec| ]. split;[exact Final| ]. split;assumption.
Qed.
Theorem CPAllPriorities : forall p,p<13 ->
 CPCore <==> V293_create_owned_pool 84%positive (209%positive,Int.zero)p
 (Amapsto(182%positive,0%Z)Tint8 true(V293_byteval 0) **
 V293_tcb_joint_priority_rest 82%positive 95%positive 84%positive
 94%positive 161%positive 162%positive 184%positive (209%positive,Int.zero)p).
Proof. intros;apply V293_create_joint_priority_view;assumption. Qed.
Theorem CPActualPriorityViews : forall ks,exists Mf,
 cstepstar ChainProgram(curs(V293_init_three_calls 201%Z 202%Z 203%Z),(kenil,ks))
  (ChainGE,ChainCaller,ChainEntryMemory)(curs(sskip None),(kenil,ks))(ChainGE,ChainCaller,Mf) /\
 (forall p,p<13 -> ChainState Mf |=
  V293_create_owned_pool 84%positive(209%positive,Int.zero)p
  (Amapsto(182%positive,0%Z)Tint8 true(V293_byteval 0) **
   V293_tcb_joint_priority_rest 82%positive 95%positive 84%positive
   94%positive 161%positive 162%positive 184%positive (209%positive,Int.zero)p) **
  V293_rdy_raw_cells ChainFrame Atrue).
Proof.
 intro ks. destruct(CPActualInitialization ks)as(Mmisc&Mrdy&Mf&bri&bi&bn&b1&b2&Exec&Joint&FR&FT).
 exists Mf. split;[exact Exec| ]. intros p Bound.
 eapply astar_mono;[intros st HS;exact(proj1(CPAllPriorities p Bound st)HS)|intros st HS;exact HS|exact Joint].
Qed.
(* Both resources are present in the actual post-state, not aliases. *)
Theorem CPActualNestingZero : forall ks,exists Mf,
 cstepstar ChainProgram(curs(V293_init_three_calls 201%Z 202%Z 203%Z),(kenil,ks))
  (ChainGE,ChainCaller,ChainEntryMemory)(curs(sskip None),(kenil,ks))(ChainGE,ChainCaller,Mf) /\
 load Tint8 Mf(182%positive,0%Z)=Some(V293_byteval 0) /\
 184%positive<>182%positive.
Proof.
 intro ks. destruct(CPActualInitialization ks)as(Mmisc&Mrdy&Mf&bri&bi&bn&b1&b2&Exec&Joint&FR&FT).
 exists Mf. split;[exact Exec| ]. split;[ |discriminate].
 change(load Tint8(getmem(ChainState Mf))(182%positive,0%Z)=Some(V293_byteval 0)).
 unfold CPCore,V293_create_joint_core in Joint.
 eapply V293_record_star_load_l;[ |exact Joint].
 eapply V293_record_star_load_r. intros st [HM HO].
 eapply mapstoval_load;[reflexivity|exact HM].
Qed.
(* Independent literal reserved input, with the same bytes in both branches.
   Only the NULL store is removed in the negative branch; not a whole-API run. *)
Theorem CPReservedRoundTrip : JPSlotState true |=
 Amapsto(84%positive,16%Z)(Tptr V293_tcb_type)true(Vptr JPToken).
Proof. apply V293_reservation_reacquire. exact JPReservedShareCompatible. Qed.
Theorem CPReservedLoad : load(Tptr V293_tcb_type)(JPSlotMemory true)(84%positive,16%Z)=Some(Vptr JPToken).
Proof. destruct CPReservedRoundTrip as[HM HO]. eapply mapstoval_load;[reflexivity|exact HM]. Qed.
Theorem CPPhysicalRollback : exists Mf,
 store(Tptr V293_tcb_type)(JPSlotMemory true)(84%positive,16%Z)Vnull=Some Mf /\
 load(Tptr V293_tcb_type)Mf(84%positive,16%Z)=Some Vnull /\
 V293_wstate ChainGE ChainCaller Mf |= V293_reservation_pool(84%positive,16%Z)JPToken /\
 (forall b j,b<>84%positive \/ (j<16)%Z \/ (20<=j)%Z -> get Mf(b,j)=get(JPSlotMemory true)(b,j)).
Proof.
 assert(Owned:JPSlotState true |=
  V293_owned_record_cell((84%positive,16%Z),Tptr V293_tcb_type,Vptr JPToken) ** Aemp).
 { apply astar_r_aemp_intro. unfold V293_owned_record_cell. apply astar_l_apure_intro;[apply CPReservedRoundTrip|reflexivity]. }
 destruct(V293_owned_record_cell_update (84%positive,16%Z)(Tptr V293_tcb_type)(Vptr JPToken) Vnull _ _ _ _ _ _ _ _ eq_refl Owned)as(Mf&Store&Final).
 exists Mf. split;[exact Store| ]. split.
 - change(load(Tptr V293_tcb_type)(getmem(V293_wstate ChainGE ChainCaller Mf))(84%positive,16%Z)=Some Vnull).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Final].
 - split.
   + apply V293_reservation_pool_null. apply astar_r_aemp_elim in Final.
     unfold V293_owned_record_cell in Final. apply astar_l_apure_elim in Final. exact(proj2 Final).
   + intros b j Away. unfold store in Store.
     eapply V293_storebytes_outside;[exact Store| ]. cbn[length encode_val inj_pointer]. exact Away.
Qed.
Definition CPObserve (write:bool) :=
 match (if write then store(Tptr V293_tcb_type)(JPSlotMemory true)(84%positive,16%Z)Vnull else Some(JPSlotMemory true))with
 |Some M=>load(Tptr V293_tcb_type)M(84%positive,16%Z)|None=>None end.
Theorem CPWrittenRollbackRead : CPObserve true=Some Vnull.
Proof. destruct CPPhysicalRollback as(Mf&Store&Read&Pool&Outside). unfold CPObserve;rewrite Store;exact Read. Qed.
Theorem CPOmittedRollbackRead : CPObserve false=Some(Vptr JPToken).
Proof. exact CPReservedLoad. Qed.
Theorem CPOmittedRollbackNotNull : CPObserve false<>Some Vnull.
Proof. rewrite CPOmittedRollbackRead;discriminate. Qed.
Theorem CPHalfAloneCannotRollback :
 load(Tptr V293_tcb_type)(JPSlotMemory false)(84%positive,16%Z)=Some(Vptr JPToken) /\
 store(Tptr V293_tcb_type)(JPSlotMemory false)(84%positive,16%Z)Vnull=None.
Proof.
 split.
 - destruct(JPLiteralReserved false)as[HM HO]. eapply mapstoval_load;[reflexivity|exact HM].
 - change(storebytes(JPSlotMemory false)(84%positive,16%Z)[Byte Byte.zero;Byte Byte.zero;Byte Byte.zero;Byte Byte.zero]=None).
   pose proof(proj1(proj2 JPPermissionOnlyControl))as Half.
   unfold storebytes at 1. unfold addr,offset,block in *. rewrite Half. reflexivity.
Qed.
Print Assumptions CPActualInitialization.
Print Assumptions CPPhysicalRollback.
Print Assumptions CPOmittedRollbackNotNull.
