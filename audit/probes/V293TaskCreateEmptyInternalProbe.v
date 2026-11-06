(* Composition witness reuses Stage93/96 literal bytes; it is not an
   independent source translation or a call allocation/free execution. *)
Require Import CertiOS.audit.probes.V293TaskCreateTCBCallProbe.
Require Import CertiOS.audit.probes.V293TCBSuccessInternalProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateFailureHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBCall.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSnapshotInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import Coq.Lists.List.ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.audit.probes.V293TaskCreateFailureHoareProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.

Require Import CertiOS.audit.probes.V293TaskCreateStackCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateBodyFailure.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtFunction.
Require Import CertiOS.audit.probes.V293TaskCreateBodyFailureProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEmptyInternal.
Require Import CertiOS.tactics.hoareforward.init_spec.
Definition InternalArgs := V293_create_internal_values 17%Z StackArg StackInput 11
 (Vint32 Int.zero)Vnull(Vint32(Int.repr 128))Vnull(Vint32 Int.zero).
Definition InternalProgram running sched : progunit := fun f=>
 if Z.eq_dec f 903%Z then Some(V293_CreateExt_function 92%Z 99%Z 97%Z running sched 902%Z 900%Z)
 else SuccessProgram f.
Definition InternalPre cs :=
 V293_create_internal_pre_cells 17%Z StackArg StackInput 11(Vint32 Int.zero)Vnull
 (Vint32(Int.repr 128))Vnull(Vint32 Int.zero) **
 ([|InternalArgs=InternalArgs|] **
 V293_create_internal_external 211%positive 720%positive 901%positive 210%positive 11 SuccessR
 (spec_done None)(fun _=>false)[]cs) ** V293_create_internal_domain.
Definition InternalPost cs : retasrt := fun result=>V293_create_internal_post_cells **
 ([|result=Some(Vint32(Int.repr 66))|] **
 V293_create_internal_external 211%positive 720%positive 901%positive 210%positive 11 SuccessR
 (spec_done None)(fun _=>false)[]cs) ** V293_create_internal_domain.
Theorem InternalTypedArguments : dl_vl_match V293_CreateExt_parameters InternalArgs=true.
Proof. reflexivity. Qed.
Theorem InternalRealBuilders : forall cs running sched,
 Some(InternalPre cs)=BuildPreI(InternalProgram running sched)903%Z(rev InternalArgs)[]
 (V293_create_empty_fpre 211%positive 720%positive 901%positive 210%positive 11 17%Z StackArg StackInput
 (Vint32 Int.zero)Vnull(Vint32(Int.repr 128))Vnull(Vint32 Int.zero)SuccessR
 (spec_done None)(fun _=>false)[]cs SuccessRFun)SuccessTid /\
 Some(InternalPost cs)=BuildRetI(InternalProgram running sched)903%Z(rev InternalArgs)[]
 (V293_create_empty_fpost 211%positive 720%positive 901%positive 210%positive 11 SuccessR
 (spec_done None)(fun _=>false)[]cs SuccessRFun)SuccessTid.
Proof.
 intros. unfold BuildPreI,BuildRetI,InternalProgram.
 destruct(Z.eq_dec 903%Z 903%Z);[ |contradiction]. rewrite rev_involutive. split;reflexivity.
Qed.
Theorem InternalFullContractChecked : forall present cs running sched,
 InfRules(StackSpec present cs)V293_scheduler V293_witness_li V293_shared_inv
 (InternalPost cs)Afalse(InternalPre cs)
 (V293_CreateExt_body 92%Z 99%Z 97%Z running sched 902%Z 900%Z)Afalse SuccessTid.
Proof.
 intros present cs running sched.
 eapply V293_OSTaskCreateExt_empty_internal_contract with
 (P:=InternalProgram running sched)(creator:=903%Z)(vl:=rev InternalArgs)(lg:=[])
 (good:=SuccessRFun)(gb:=SuccessRFun)(old:=fun _=>Vundef)(oldprev:=Vundef)(oldback:=Vundef)
 (slot:=Vundef)(table:=211%positive)(bg:=210%positive)(bt:=301%positive)
 (base:=128%Z)(p:=11)(top:=Vnull)(bottom:=Vnull)(identity:=Vint32 Int.zero)
 (size:=Vint32(Int.repr 128))(ext:=Vnull)(options:=Vint32 Int.zero)(next:=SuccessNext)
 (bh:=212%positive)(bgrp:=213%positive)(br:=214%positive)(bn:=215%positive)
 (oldblock:=301%positive)(oldbase:=256%Z)(present:=present)(g:=1)(row:=129)(n:=254)
 (Rbefore:=SuccessR)(R:=SuccessR)(aop:=spec_done None)(isr:=fun _=>false)(is:=[])(cs:=cs)
 (target:=17%Z)(argv:=StackArg)(inputtop:=StackInput).
 - apply SuccessRGood.
 - apply SuccessRGood.
 - lia.
 - repeat split;reflexivity.
 - apply SuccessRCurLINV.
 - repeat split;reflexivity.
 - apply SuccessRCurLINV.
 - apply StackLookup.
 - apply StackTCBLookup.
 - unfold InternalProgram. destruct(Z.eq_dec 903%Z 903%Z);[reflexivity|contradiction].
 - apply InternalRealBuilders.
 - apply InternalRealBuilders.
Qed.
(* The unchanged full-snapshot callee is also checked under THIS SAME Spec. *)
Theorem InternalSameSpecCallee : forall present cs saved,
 InfRules(StackSpec present cs)V293_scheduler V293_witness_li V293_shared_inv
 (CallInternalPost present cs saved)Afalse(CallInternalPre present cs saved)
 (V293_TCBInit_function_body 501%Z 502%Z)Afalse SuccessTid.
Proof. apply StackCalleeContractChecked. Qed.
Lemma InternalExactDomain : eq_dom_env BodyLE(getlenvdom V293_create_internal_declarations).
Proof.
 unfold eq_dom_env. intros x tp.
 destruct(Z.eq_dec x 109%Z)as[E109|E109].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold BodyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 203%Z)as[E203|E203].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold BodyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 202%Z)as[E202|E202].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold BodyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 201%Z)as[E201|E201].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold BodyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 209%Z)as[E209|E209].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold BodyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 204%Z)as[E204|E204].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold BodyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 208%Z)as[E208|E208].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold BodyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 207%Z)as[E207|E207].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold BodyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 206%Z)as[E206|E206].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold BodyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 205%Z)as[E205|E205].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold BodyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 108%Z)as[E108|E108].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold BodyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 101%Z)as[E101|E101].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold BodyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
 unfold BodyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence. rewrite map_get_sig' by congruence.
 split.
 - intro H. repeat destruct H as[H|H];try contradiction;inversion H;congruence.
 - intros[b H]. discriminate.
Qed.
Theorem InternalLiteralFramedEntry : forall cs,
 BodyState(BodyMemory Vnull Vundef StackInput Vundef Vundef)cs |= InternalPre cs ** CallFrame.
Proof.
 intro cs. pose proof(BodyJointSpatial Vnull Vundef StackInput Vundef Vundef cs)as H.
 unfold BodyExtraAsrt,StackEntry,StackFrame,StackLocalAsrt,V293_create_stack_arguments,
 V293_create_stack_kept,CallArgs,V293_create_tcb_arguments in H.
 assert(J:BodyState(BodyMemory Vnull Vundef StackInput Vundef Vundef)cs |=
 Alvarenv 109%Z Tint32(713%positive,0%Z) **
 Agvarenv 99%Z Tint8(720%positive,0%Z) ** Agvarenv 97%Z Tint8(901%positive,0%Z) **
 (BodyExtraAsrt Vundef ** StackEntry Vnull Vundef StackInput Vundef cs)).
 { apply astar_l_alvarenv_intro;[ |split;[reflexivity|vm_compute;reflexivity]].
   apply astar_l_agvarenv_intro;[ |split;[reflexivity|vm_compute;reflexivity]].
   apply astar_l_agvarenv_intro;[apply BodyJointSpatial|split;[reflexivity|vm_compute;reflexivity]]. }
 unfold BodyExtraAsrt,StackEntry,StackFrame,StackLocalAsrt,V293_create_stack_arguments,
 V293_create_stack_kept,CallArgs,V293_create_tcb_arguments in J.
 assert(K:BodyState(BodyMemory Vnull Vundef StackInput Vundef Vundef)cs |=
 ((Alvarenv 109%Z Tint32(713%positive,0%Z) ** Amapsto(713%positive,0%Z)Tint32 true Vundef) **
 V293_tcb_table_binding 211%positive) **
 (Agvarenv 99%Z Tint8(720%positive,0%Z) ** Agvarenv 97%Z Tint8(901%positive,0%Z) **
 Amapsto(720%positive,0%Z)Tint8 true(V293_byteval 0) **
 V293_tcb_empty_external 210%positive SuccessR(spec_done None)(fun _=>false)[]cs **
 LV 108%Z @ (Tptr Tint32) |->Vundef **
 LV 201%Z @ Tint32 |->V293_task_selector 17%Z **
 LV 202%Z @ (Tptr Tvoid) |->StackArg ** LV 203%Z @ (Tptr Tint32) |->StackInput **
 LV 204%Z @ Tint16 |->Vint32 Int.zero ** LV 209%Z @ Tint8 |->Vundef **
 LV 101%Z @ Tint8 |->V293_byteval 11 ** LV 205%Z @ (Tptr Tint32) |->Vnull **
 LV 206%Z @ Tint16 |->Vint32 Int.zero ** LV 207%Z @ Tint32 |->Vint32(Int.repr 128) **
 LV 208%Z @ (Tptr Tvoid) |->Vnull **
 Amapsto(211%positive,44%Z)(Tptr V293_tcb_type)true Vnull ** CallFrame)).
 { clear -J. sep auto. }
 eapply astar_mono in K.
 2: { apply astar_mono;[apply V293_create_raw_local|intros st [G N];exact G]. }
 2: { intros st HS;exact HS. }
 assert(D:BodyState(BodyMemory Vnull Vundef StackInput Vundef Vundef)cs |=
 V293_create_internal_domain **
 ((LV 109%Z @ Tint32 |->Vundef ** Agvarenv 92%Z(Tarray(Tptr V293_tcb_type)13)(211%positive,0%Z)) **
 (Agvarenv 99%Z Tint8(720%positive,0%Z) ** Agvarenv 97%Z Tint8(901%positive,0%Z) **
 Amapsto(720%positive,0%Z)Tint8 true(V293_byteval 0) **
 V293_tcb_empty_external 210%positive SuccessR(spec_done None)(fun _=>false)[]cs **
 LV 108%Z @ (Tptr Tint32) |->Vundef **
 LV 201%Z @ Tint32 |->V293_task_selector 17%Z **
 LV 202%Z @ (Tptr Tvoid) |->StackArg ** LV 203%Z @ (Tptr Tint32) |->StackInput **
 LV 204%Z @ Tint16 |->Vint32 Int.zero ** LV 209%Z @ Tint8 |->Vundef **
 LV 101%Z @ Tint8 |->V293_byteval 11 ** LV 205%Z @ (Tptr Tint32) |->Vnull **
 LV 206%Z @ Tint16 |->Vint32 Int.zero ** LV 207%Z @ Tint32 |->Vint32(Int.repr 128) **
 LV 208%Z @ (Tptr Tvoid) |->Vnull **
 Amapsto(211%positive,44%Z)(Tptr V293_tcb_type)true Vnull ** CallFrame))).
 { apply astar_l_adomlenv_intro;[exact K|apply InternalExactDomain]. }
 unfold InternalPre,V293_create_internal_pre_cells,V293_create_internal_locals,
 V293_create_internal_external. change(4*Z.of_nat 11)%Z with 44%Z.
 clear -D. sep auto.
Qed.
Theorem InternalEntrySatisfiable : forall cs,exists s,s |= InternalPre cs.
Proof.
 intro cs. pose proof(InternalLiteralFramedEntry cs)as H.
 apply sat_split in H. destruct H as[m1[m2[O1[O2[_[_[Pre Rest]]]]]]].
 eexists;exact Pre.
Qed.
Theorem InternalLiteralFramedReturn : forall cs,
 BodyState(BodyMemory Vnull Vnull StackInput(Vint32(Int.repr 66))(Vint32 Int.zero))cs |=
 InternalPost cs(Some(Vint32(Int.repr 66))) ** CallFrame.
Proof.
 intro cs. pose proof(BodyReturnSatisfiable cs)as H.
 assert(D:BodyState(BodyMemory Vnull Vnull StackInput(Vint32(Int.repr 66))(Vint32 Int.zero))cs |=
 V293_create_internal_domain ** BodyReturn cs(Some(Vint32(Int.repr 66)))).
 { apply astar_l_adomlenv_intro;[exact H|apply InternalExactDomain]. }
 assert(K:BodyState(BodyMemory Vnull Vnull StackInput(Vint32(Int.repr 66))(Vint32 Int.zero))cs |=
 V293_create_failure_return 211%positive 11
 (V293_create_failure_kept 210%positive Vnull Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero)SuccessR
 (V293_create_stack_kept 17%Z StackArg StackInput
 (V293_create_prefix_kept 720%positive 713%positive 99%Z 97%Z 901%positive V293_create_internal_domain)))
 (spec_done None)(fun _=>false)[]cs(Some(Vint32(Int.repr 66))) ** CallFrame).
 { unfold BodyReturn,BodyKept,V293_create_failure_return,V293_create_failure_state,
 V293_create_failure_resources,V293_create_failure_kept,V293_create_stack_kept,
 V293_create_prefix_kept in *. cbn [V293_rdy_raw_cells]in *. clear -D. sep auto. }
 eapply astar_mono in K;[ |apply V293_create_internal_exit|intros st HS;exact HS].
 exact K.
Qed.
Theorem InternalReturnSatisfiable : forall cs,exists s,s |= InternalPost cs(Some(Vint32(Int.repr 66))).
Proof.
 intro cs. pose proof(InternalLiteralFramedReturn cs)as H.
 apply sat_split in H. destruct H as[m1[m2[O1[O2[_[_[Post Rest]]]]]]].
 eexists;exact Post.
Qed.
