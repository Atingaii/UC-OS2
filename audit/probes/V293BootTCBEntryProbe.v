(* Same literal boot bytes and same program on both sides of the control.
   This exercises a direct TCB component call, not full OSTaskCreateExt. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.audit.probes.V293InitChainProbe.
Require Import CertiOS.certiucos.v293.proofs.V293BootRunningBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293StartCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateJointShared.
Require Import CertiOS.certiucos.v293.proofs.V293InitChain.
Require Import CertiOS.certiucos.v293.proofs.V293InitMisc.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBList.
Require Import CertiOS.certiucos.v293.proofs.V293NullBytes.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.code.V293OSInitChain.
Require Import CertiOS.certiucos.v293.code.V293OSInitMisc.
Require Import CertiOS.certiucos.v293.code.V293OSInitRdyList.
Require Import CertiOS.certiucos.v293.code.V293OSInitTCBCall.
Require Import CertiOS.certiucos.v293.code.V293OSMemClr.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Require Import CertiOS.certiucos.v293.proofs.V293BootTCBEntry.
Require Import CertiOS.certiucos.v293.proofs.V293MemClr.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBCallSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitPrefix.
Require Import CertiOS.audit.probes.V293BootRunningBoundaryProbe.

Definition BTGE : env := set BRGE 91%Z(95%positive,Tptr V293_tcb_type).
Definition BTProgram f := if Z.eq_dec f 205%Z then
 Some(V293_TCBInit_function 206%Z 207%Z)else BRProgram f.
Definition BTState M := V293_wstate BTGE ChainCaller M.
Definition BTTop := Vptr(800%positive,Int.repr 252).
Definition BTBottom := Vptr(800%positive,Int.zero).
Definition BTArguments := [Vint32(Int.repr 3);Vnull;Vint32(Int.repr 64);
 Vint32(Int.repr 65535);BTBottom;BTTop;V293_byteval 12].
Definition BTFrame := V293_boot_tcb_frame 94%positive 82%positive 84%positive ChainExtraCells.
Definition BTBefore := V293_tcb_init_old_fields 82%positive 0 V293_boot_tcb_old++
 V293_tcb_prefix_links 95%positive 82%positive 0(Vptr(82%positive,Int.zero))
 (Vptr(82%positive,Int.repr 56))++BTFrame.
Definition BTAux := (false,(nil:list hid),(nil:list bool)).
Definition BTFullState le M : RstateOP :=
 (BTGE,le,M,(fun _=>false),BTAux,emp,spec_done None).
Lemma BTLiteralEntry : V293_wstate BTGE emp ChainEntryMemory |=
 V293_init_resources ChainSlots false(V293_rdy_raw_cells ChainTail Atrue).
Proof.
 eapply BRResourcesRebind;[ |exact BRLiteralEntry].
 intros d Member. vm_compute in Member.
 repeat(destruct Member as[Same|Member];[subst d;reflexivity| ]);contradiction.
Qed.
Lemma BTReadyEnvironment : forall bi,
 V293_rdy_env BTGE(V293_rdy_locals 41%Z bi)21%Z 22%Z 23%Z 24%Z 25%Z OSTCBCur 41%Z
 161%positive 162%positive 163%positive 164%positive 165%positive 166%positive bi.
Proof. intro bi;repeat split;reflexivity. Qed.
Lemma BTTCBEnvironment : forall bi bn b1 b2,
 V293_tcb_link_env BTGE(V293_tcb_call_locals 41%Z 42%Z 43%Z 44%Z bi bn b1 b2)
 31%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z 82%positive 94%positive 95%positive bi bn b1 b2.
Proof. intros;repeat split;reflexivity. Qed.
Theorem BTActualInitialization : forall ks,exists Mf,
 cstepstar BTProgram(curs(V293_init_three_calls 201%Z 202%Z 203%Z),(kenil,ks))
 (BTGE,ChainCaller,ChainEntryMemory)(curs(sskip None),(kenil,ks))(BTGE,ChainCaller,Mf) /\
 BTState Mf |= V293_rdy_raw_cells ChainFinalCells Atrue /\
 BTState Mf |= V293_rdy_raw_cells BTBefore Atrue.
Proof.
 intro ks.
 destruct(V293_OSInit_three_calls ChainSlots(repeat Vundef 728)
 (repeat(Vint32(Int.repr 255))52)ChainFrame BTProgram ks BTGE ChainCaller ChainEntryMemory
 (fun _=>false)(false,nil,nil)emp(spec_done None)
 201%Z 202%Z 203%Z 204%Z 11%Z 12%Z 21%Z 22%Z 23%Z 24%Z 25%Z OSTCBCur 41%Z
 161%positive 162%positive 163%positive 164%positive 165%positive 166%positive
 31%Z 32%Z 33%Z 34%Z 41%Z 42%Z 43%Z 44%Z 82%positive 84%positive 94%positive 95%positive
 (Vint32(Int.repr 7))(Vint32(Int.repr 3))Vundef(Vint32(Int.repr 5))
 (Vint32(Int.repr 9))(Vptr(211%positive,Int.zero))(Vptr(212%positive,Int.zero))
 (Vptr(121%positive,Int.zero))(Vptr(122%positive,Int.zero))
 ltac:(unfold ChainSlots,V293_InitMisc_slots;repeat(apply Forall_cons;[unfold V293_init_scalar;cbn;auto| ]);apply Forall_nil)
 ltac:(reflexivity)ltac:(reflexivity)ltac:(reflexivity)ltac:(reflexivity)
 ltac:(discriminate)ltac:(lia)ltac:(lia)ltac:(lia)
 BTReadyEnvironment BTTCBEnvironment ltac:(intros;reflexivity)ltac:(reflexivity)
 ltac:(apply repeat_length)ltac:(apply repeat_length)BTLiteralEntry)
 as(Mmisc&Mrdy&Mf&bri&bi&bn&b1&b2&Exec&EM&ER&ET&Final&FR&FT).
 exists Mf. split;[exact Exec| ]. split;[exact Final| ].
 unfold BTBefore,BTFrame,ChainFinalCells in *.
 apply V293_boot_first_tcb_entry;exact Final.
Qed.

Definition BTAtHook ks M := exists b1 b2 b3 b4 b5 b6 b7 b8 b9 Mh,
 let le:=V293_tcb_function_env b1 b2 b3 b4 b5 b6 b7 b8 b9 in
 let cells:=V293_tcb_init_final_fields 82%positive 0 12 BTTop BTBottom
  (Vint32(Int.repr 65535))(Vint32(Int.repr 64))Vnull(Vint32(Int.repr 3))++
  V293_tcb_init_input_cells b8 b1 b2 b3 b4 b5 b6 b7 82%positive 0 12 BTTop BTBottom
   (Vint32(Int.repr 65535))(Vint32(Int.repr 64))Vnull(Vint32(Int.repr 3))++
  V293_tcb_prefix_links 95%positive 82%positive 0(Vptr(82%positive,Int.repr 56))
   (Vptr(82%positive,Int.repr 56))++((b9,0%Z),Tint32,Vint32 Int.zero)::BTFrame in
 V293_local_steps BTProgram
 (curs(sfexec 205%Z BTArguments V293_TCBInit_argument_types),(kenil,ks))
 ((BTGE,ChainCaller,M),(fun _=>false),BTAux)
 (curs(sfexec 206%Z [Vptr(82%positive,Int.zero)][Tptr V293_tcb_type]),
  (kenil,V293_tcb_first_hook_cont 205%Z 206%Z 207%Z ChainCaller ks))
 ((BTGE,le,Mh),(fun _=>false),BTAux) /\
 (BTFullState le Mh |= V293_rdy_raw_cells cells Atrue) /\
 load(Tptr V293_tcb_type)Mh(95%positive,0%Z)=Some(Vptr(82%positive,Int.repr 56)) /\
 load Tint8 Mh(82%positive,50%Z)=Some(V293_byteval 12) /\
 load(Tptr V293_tcb_type)Mh(166%positive,0%Z)=Some Vnull /\
 load Tint8 Mh(185%positive,0%Z)=Some(Vint32 Int.zero) /\
 ~exists C' state',loststep BTProgram
 (curs(sfexec 206%Z [Vptr(82%positive,Int.zero)][Tptr V293_tcb_type]),
  (kenil,V293_tcb_first_hook_cont 205%Z 206%Z 207%Z ChainCaller ks))
 ((BTGE,le,Mh),(fun _=>false),BTAux) C' state'.
Ltac BTLoad H :=
 lazymatch type of H with ?st |= V293_rdy_raw_cells ?cells ?R =>
  lazymatch goal with |- load ?tp ?M ?a=Some ?v =>
   change(load tp(getmem st)a=Some v);
   eapply V293_rdy_raw_load;[ |reflexivity|exact H]
  end
 end.
Lemma BTEntryToFirstHook : forall ks M,
 BTState M |= V293_rdy_raw_cells BTBefore Atrue -> BTAtHook ks M.
Proof.
 intros ks M Owned.
 destruct(V293_OS_TCBInit_call_to_first_hook BTProgram ks BTGE ChainCaller M
 (fun _=>false)BTAux emp(spec_done None)false nil nil
 205%Z 206%Z 207%Z 95%positive 82%positive 0 12 BTTop BTBottom
 (Vint32(Int.repr 65535))(Vint32(Int.repr 64))Vnull(Vint32(Int.repr 3))
 (Vptr(82%positive,Int.repr 56))V293_boot_tcb_old BTFrame
 ltac:(reflexivity)ltac:(reflexivity)ltac:(lia)ltac:(lia)
 ltac:(vm_compute;congruence)ltac:(repeat split;reflexivity)ltac:(reflexivity)Owned)
 as(b1&b2&b3&b4&b5&b6&b7&b8&b9&Mh&ND&Exec&Final&Missing).
 unfold BTAtHook. exists b1. exists b2. exists b3. exists b4. exists b5.
 exists b6. exists b7. exists b8. exists b9. exists Mh.
 split;[exact Exec| ]. split;[exact Final| ].
 split.
 - BTLoad Final.
   do 2(apply in_or_app;right). left;reflexivity.
 - split.
   + BTLoad Final.
     apply in_or_app;left. right;left;reflexivity.
   + split.
     * BTLoad Final.
       do 3(apply in_or_app;right). right.
       unfold BTFrame,V293_boot_tcb_frame. do 5(apply in_or_app;right).
       unfold ChainExtraCells. apply in_or_app;left. do 6 right;left;reflexivity.
     * split.
       -- BTLoad Final.
          do 3(apply in_or_app;right). right.
          unfold BTFrame,V293_boot_tcb_frame. do 5(apply in_or_app;right).
          unfold ChainExtraCells. apply in_or_app;right. apply in_or_app;left.
          do 4 right;left;reflexivity.
       -- apply Missing;reflexivity.
Qed.
Theorem BTReachableFirstHook : forall ks,exists M,
 cstepstar BTProgram(curs(V293_init_three_calls 201%Z 202%Z 203%Z),(kenil,ks))
 (BTGE,ChainCaller,ChainEntryMemory)(curs(sskip None),(kenil,ks))(BTGE,ChainCaller,M) /\
 BTAtHook ks M.
Proof.
 intro ks. destruct(BTActualInitialization ks)as(M&Exec&Raw&Entry).
 exists M. split;[exact Exec|apply BTEntryToFirstHook;exact Entry].
Qed.

Definition BTFreeTail := V293_tcb_init_old_fields 82%positive 0 V293_boot_tcb_old++
 [((82%positive,20%Z),Tcom_ptr 410%Z,Vptr(82%positive,Int.repr 56))]++BTFrame.
Lemma BTFreeHeadOut : forall M,
 BTState M |= V293_rdy_raw_cells BTBefore Atrue ->
 BTState M |= Amapsto(95%positive,0%Z)(Tptr V293_tcb_type)true(Vptr(82%positive,Int.zero)) **
 V293_rdy_raw_cells BTFreeTail Atrue.
Proof.
 intros M H. unfold BTBefore,V293_tcb_prefix_links in H.
 repeat rewrite V293_raw_cells_append in H.
 change(BTState M |=
 V293_rdy_raw_cells(V293_tcb_init_old_fields 82%positive 0 V293_boot_tcb_old)
 (V293_rdy_raw_cells (((95%positive,0%Z),Tptr V293_tcb_type,Vptr(82%positive,Int.zero))::nil)
 (V293_rdy_raw_cells (((82%positive,20%Z),Tcom_ptr 410%Z,Vptr(82%positive,Int.repr 56))::nil)
 (V293_rdy_raw_cells BTFrame Atrue))))in H.
 apply V293_raw_cells_swap in H.
 unfold BTFreeTail. repeat rewrite V293_raw_cells_append. exact H.
Qed.
Definition BTEmptyControl ks M := exists Mn Mr,
 store(Tptr V293_tcb_type)M(95%positive,0%Z)Vnull=Some Mn /\
 V293_local_steps BTProgram
 (curs(sfexec 205%Z BTArguments V293_TCBInit_argument_types),(kenil,ks))
 ((BTGE,ChainCaller,Mn),(fun _=>false),BTAux)
 (curs(sskip(Some(Vint32(Int.repr 66)))),(kenil,ks))
 ((BTGE,ChainCaller,Mr),(fun _=>false),BTAux) /\
 (BTState Mr |= V293_rdy_raw_cells
  (((95%positive,0%Z),Tptr V293_tcb_type,Vnull)::BTFreeTail)Atrue) /\
 load Tint8 Mr(82%positive,50%Z)=Some(Vint32 Int.zero) /\
 load(Tptr V293_tcb_type)Mr(166%positive,0%Z)=Some Vnull /\
 load Tint8 Mr(185%positive,0%Z)=Some(Vint32 Int.zero).
Lemma BTNullHeadControl : forall ks M,
 BTState M |= V293_rdy_raw_cells BTBefore Atrue -> BTEmptyControl ks M.
Proof.
 intros ks M H. apply BTFreeHeadOut in H.
 assert(Owned:BTState M |=
 V293_owned_record_cell((95%positive,0%Z),Tptr V293_tcb_type,Vptr(82%positive,Int.zero)) **
 V293_rdy_raw_cells BTFreeTail Atrue).
 { eapply astar_mono;[ |intros st HS;exact HS|exact H].
   intros st HS. unfold V293_owned_record_cell. apply astar_l_apure_intro;[exact HS|reflexivity]. }
 destruct(V293_owned_record_cell_update(95%positive,0%Z)(Tptr V293_tcb_type)
 (Vptr(82%positive,Int.zero))Vnull _ _ _ _ _ _ _ _ eq_refl Owned)
 as(Mn&Store&Updated).
 assert(Entry:BTState Mn |= V293_rdy_raw_cells
 (((95%positive,0%Z),Tptr V293_tcb_type,Vnull)::BTFreeTail)Atrue).
 { unfold V293_owned_record_cell in Updated.
   apply astar_assoc_elim in Updated. apply astar_l_apure_elim in Updated.
   exact(proj2 Updated). }
 destruct(V293_tcb_fresh_nine_avoiding Mn
 (((95%positive,0%Z),Tptr V293_tcb_type,Vnull)::BTFreeTail))
 as(b1&b2&b3&b4&b5&b6&b7&b8&b9&ND&Fresh&Away).
 destruct(V293_OS_TCBInit_empty_call_return BTProgram ks BTGE ChainCaller Mn
 (fun _=>false)BTAux emp(spec_done None)false nil nil 205%Z 206%Z 207%Z
 95%positive b1 b2 b3 b4 b5 b6 b7 b8 b9
 (V293_byteval 12)BTTop BTBottom(Vint32(Int.repr 65535))
 (Vint32(Int.repr 64))Vnull(Vint32(Int.repr 3))BTFreeTail
 ltac:(reflexivity)ltac:(reflexivity)ND Fresh ltac:(repeat split;reflexivity)Away Entry)
 as(Ms&Mr&Exec&Locals&Final&Freed).
 unfold BTEmptyControl. exists Mn. exists Mr.
 split;[exact Store| ]. split;[exact Exec| ]. split;[exact Final| ].
 split.
 - BTLoad Final. right. unfold BTFreeTail. apply in_or_app;left. right;left;reflexivity.
 - split.
   + BTLoad Final. right. unfold BTFreeTail. do 2(apply in_or_app;right).
     unfold BTFrame,V293_boot_tcb_frame. do 5(apply in_or_app;right).
     unfold ChainExtraCells. apply in_or_app;left. do 6 right;left;reflexivity.
   + BTLoad Final. right. unfold BTFreeTail. do 2(apply in_or_app;right).
     unfold BTFrame,V293_boot_tcb_frame. do 5(apply in_or_app;right).
     unfold ChainExtraCells. apply in_or_app;right. apply in_or_app;left.
     do 4 right;left;reflexivity.
Qed.

(* One factor only: the same actual M, program, arguments, global and local
   bindings, interrupt state and frame. Only the real free-head store differs.
   Existence of these traces is not a determinism or all-runs theorem. *)
Theorem BTSameMemoryControl : forall ks,exists M,
 cstepstar BTProgram(curs(V293_init_three_calls 201%Z 202%Z 203%Z),(kenil,ks))
 (BTGE,ChainCaller,ChainEntryMemory)(curs(sskip None),(kenil,ks))(BTGE,ChainCaller,M) /\
 BTAtHook ks M /\ BTEmptyControl ks M.
Proof.
 intro ks. destruct(BTActualInitialization ks)as(M&Exec&Raw&Entry).
 exists M. split;[exact Exec| ]. split.
 - apply BTEntryToFirstHook;exact Entry.
 - apply BTNullHeadControl;exact Entry.
Qed.
Print Assumptions BTActualInitialization.
Print Assumptions BTReachableFirstHook.
Print Assumptions BTSameMemoryControl.
