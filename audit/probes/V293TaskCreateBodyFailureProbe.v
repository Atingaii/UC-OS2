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
(* Extend actual existing finite fixture, preserving every old key. The two
   RESERVED names have equal types and distinct blocks in this SAME GE. *)
Definition BodyGE : env := set(set(set SuccessGE 97%Z(901%positive,Tint8))
 98%Z(902%positive,Tint8))99%Z(720%positive,Tint8).
Definition BodyLE : env := set StackLE 109%Z(713%positive,Tint32).
Definition BodyState M cs : RstateOP :=
 (BodyGE,BodyLE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Lemma BodyStar : forall m1 m2 m cs A B,
 join m1 m2 m -> BodyState m1 cs |= A -> BodyState m2 cs |= B ->
 BodyState m cs |= A ** B.
Proof.
 intros. apply sat_split'. exists m1. exists m2. exists(emp:osabst). exists(emp:osabst).
 split;[exact H| ]. split;[apply map_join_emp| ]. split;assumption.
Qed.
Lemma BodyLVar : forall b x tp v cs,
 get BodyLE x=Some(b,tp) -> BodyState(CallByte b tp v)cs |= LV x @ tp |->v.
Proof.
 intros b x tp v cs Env. exists b.
 eapply BodyStar with(m1:=emp)(m2:=CallByte b tp v).
 - apply map_join_comm;apply map_join_emp.
 - exists b. split;[exact Env| ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Ltac BodyLocalApart b :=
 apply map_join_merge;apply map_disjoint;intros[other off];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold CallByte;
 repeat first[rewrite map_merge_semp by reflexivity|
 rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Ltac BodyLocalTactic :=
 lazymatch goal with
 | |- BodyState(merge(CallByte ?b ?tp ?v)?tail)?cs |= LV ?x @ ?tp |-> ?v ** _ =>
   eapply BodyStar with(m1:=CallByte b tp v)(m2:=tail);
   [BodyLocalApart b|apply BodyLVar;vm_compute;reflexivity|BodyLocalTactic]
 | |- BodyState(CallByte 709%positive Tint8(Vint32(Int.repr 77)))?cs |= _ =>
   split;[apply V293_encoded_memory_mapsto|reflexivity]
 end.

Lemma BodyLocalsSpatial : forall psp inputtop err cs,
 BodyState(StackLocals psp inputtop err)cs |= StackLocalAsrt psp inputtop err.
Proof.
 intros. unfold StackLocals,StackLocalAsrt,V293_create_stack_kept,CallLocals,CallArgs,V293_create_tcb_arguments,CallFrame.
 BodyLocalTactic.
Qed.
Lemma BodyCurrentSpatial : forall cs, BodyState SuccessCurrent cs |= CurTid SuccessTid.
Proof.
 intro cs. exists Tvoid. exists 402%positive.
 eapply BodyStar with (m1:=emp) (m2:=SuccessCurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 402%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma BodyLInvSpatial : forall cs, BodyState emp cs |= LINV V293_witness_li SuccessTid [].
Proof.
 intro cs. unfold LINV. apply astar_comm. apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Ltac BodyFrameApart b :=
 apply map_join_merge;apply map_disjoint;intros [other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold SuccessCurrent,SuccessSentinel,SuccessBytes;
 repeat first [rewrite map_merge_semp by reflexivity |
 rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity.
Lemma BodyRSpatial : forall cs,
 BodyState (merge SuccessCurrent SuccessSentinel) cs |= SuccessR.
Proof.
 intro cs. unfold SuccessR.
 eapply BodyStar with (m1:=SuccessCurrent) (m2:=SuccessSentinel).
 - BodyFrameApart 402%positive.
 - apply BodyCurrentSpatial.
 - eapply BodyStar with (m1:=emp) (m2:=SuccessSentinel).
   + apply map_join_comm;apply map_join_emp.
   + apply BodyLInvSpatial.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma BodyEmptySpatial : forall cs,
 BodyState CallEmptyMemory cs |= V293_tcb_empty_external 210%positive SuccessR
 (spec_done None)(fun _=>false)[]cs.
Proof.
 intro cs. unfold V293_tcb_empty_external.
 eapply BodyStar with(m1:=emp)(m2:=CallEmptyMemory).
 - apply map_join_comm;apply map_join_emp.
 - exists 210%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - unfold CallEmptyMemory. eapply BodyStar with(m1:=SuccessBytes 210%positive false(Tptr V293_tcb_type)Vnull).
   + unfold SuccessCurrent,SuccessSentinel,SuccessBytes. BodyLocalApart 210%positive.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
   + apply astar_l_aop'_intro;[ |reflexivity].
     assert(K:BodyState(merge SuccessCurrent SuccessSentinel)cs |=
      Aisr(fun _=>false) ** Aie false ** (Ais nil) ** Acs cs ** SuccessR).
     { apply astar_l_aisr_intro;[ |reflexivity].
       apply astar_l_aie_intro;[ |reflexivity].
       apply astar_l_ais_intro;[ |reflexivity].
       apply astar_l_acs_intro;[ |reflexivity]. apply BodyRSpatial. }
     clear -K. sep auto.
Qed.

Lemma BodyBindingSpatial : forall cs,BodyState emp cs |= RollbackBinding.
Proof.
 intro cs. unfold RollbackBinding,V293_tcb_table_binding. split.
 - exists 211%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - split;[intros[x Bad];vm_compute in Bad;discriminate|repeat split;reflexivity].
Qed.
Theorem BodyStackLiteralEntry : forall slot psp inputtop err cs,
 BodyState(StackMemory slot psp inputtop err)cs |= StackEntry slot psp inputtop err cs.
Proof.
 intros.
 assert(H:BodyState(StackMemory slot psp inputtop err)cs |=
 Amapsto(211%positive,44%Z)(Tptr V293_tcb_type)true slot **
 ((V293_tcb_empty_external 210%positive SuccessR(spec_done None)(fun _=>false)[]cs **
 StackLocalAsrt psp inputtop err) ** RollbackBinding)).
 { eapply BodyStar with(m1:=RollbackSlot slot)(m2:=StackRest psp inputtop err).
   - apply StackReserveApart.
   - split;[apply V293_encoded_memory_mapsto|reflexivity].
   - eapply BodyStar with(m1:=StackRest psp inputtop err)(m2:=emp).
     + apply map_join_emp.
     + unfold StackRest. eapply BodyStar with(m1:=CallEmptyMemory)(m2:=StackLocals psp inputtop err).
       * apply StackFreshApart.
       * apply BodyEmptySpatial.
       * apply BodyLocalsSpatial.
     + apply BodyBindingSpatial. }
 unfold StackEntry,StackFrame,StackLocalAsrt,V293_create_stack_arguments,V293_create_stack_kept,
 CallArgs,V293_create_tcb_arguments in *. clear -H. sep auto.
Qed.
Lemma BodyLocalRaw : forall M cs x b tp v F,
 get BodyLE x=Some(b,tp) ->
 BodyState M cs |= LV x @ tp |-> v ** F ->
 BodyState M cs |= Amapsto(b,0%Z)tp true v ** F.
Proof.
 intros M cs x b tp v F Env Owned. unfold Alvarmapsto,Alvarenv',Aptrmapsto in Owned.
 apply astar_l_aexists_elim in Owned. destruct Owned as[actual Owned].
 apply astar_assoc_elim in Owned. apply astar_l_alvarenv_elim in Owned.
 destruct Owned as[[_ Bind]Owned]. change(get BodyLE x=Some(actual,tp))in Bind.
 rewrite Env in Bind. inversion Bind;subst actual. exact Owned.
Qed.

Definition BodyExtra cpu := merge(CallByte 720%positive Tint8(V293_byteval 0))
 (CallByte 713%positive Tint32 cpu).
Definition BodyMemory slot psp inputtop err cpu :=
 merge(BodyExtra cpu)(StackMemory slot psp inputtop err).
Definition BodyExtraAsrt cpu :=
 Amapsto(720%positive,0%Z)Tint8 true(V293_byteval 0) **
 Amapsto(713%positive,0%Z)Tint32 true cpu.
Lemma BodyExtraSpatial : forall cpu cs, BodyState(BodyExtra cpu)cs |= BodyExtraAsrt cpu.
Proof.
 intros. unfold BodyExtra,BodyExtraAsrt.
 eapply BodyStar with(m1:=CallByte 720%positive Tint8(V293_byteval 0)).
 - BodyLocalApart 720%positive.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma BodyExtraApart : forall slot psp inputtop err cpu,
 join(BodyExtra cpu)(StackMemory slot psp inputtop err)(BodyMemory slot psp inputtop err cpu).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 720%positive);[subst b;right;left| ].
 { unfold StackMemory,StackRest,StackLocals,CallLocals,CallEmptyMemory,RollbackSlot,
   CallByte,SuccessCurrent,SuccessSentinel,SuccessBytes. SuccessOutside. }
 destruct(Pos.eq_dec b 713%positive);[subst b;right;left|left].
 { unfold StackMemory,StackRest,StackLocals,CallLocals,CallEmptyMemory,RollbackSlot,
   CallByte,SuccessCurrent,SuccessSentinel,SuccessBytes. SuccessOutside. }
 unfold BodyExtra,CallByte. SuccessOutside.
Qed.
Lemma BodyJointSpatial : forall slot psp inputtop err cpu cs,
 BodyState(BodyMemory slot psp inputtop err cpu)cs |=
 BodyExtraAsrt cpu ** StackEntry slot psp inputtop err cs.
Proof.
 intros. eapply BodyStar;[apply BodyExtraApart|apply BodyExtraSpatial|apply BodyStackLiteralEntry].
Qed.
Lemma BodyPrefixBindingsSpatial : forall cs,
 BodyState emp cs |= V293_create_prefix_bindings 701%positive 720%positive 713%positive
 211%positive 99%Z 97%Z 901%positive.
Proof.
 intros. unfold V293_create_prefix_bindings.
 eapply BodyStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
 - exists 701%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - eapply BodyStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
   + exists 713%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + eapply BodyStar with(m1:=emp)(m2:=emp);[apply map_join_emp| | ].
     * unfold V293_create_global_binding. split.
       -- exists 720%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
       -- split;[intros[x Bad];vm_compute in Bad;discriminate|repeat split;reflexivity].
     * eapply BodyStar with(m1:=emp)(m2:=emp);[apply map_join_emp| |apply BodyBindingSpatial].
       unfold V293_create_global_binding. split.
       -- exists 901%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
       -- split;[intros[x Bad];vm_compute in Bad;discriminate|repeat split;reflexivity].
Qed.
Definition BodyFrame psp err := V293_create_body_frame 210%positive SuccessR psp 17%Z StackArg StackInput
 (Vint32 Int.zero)err Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))Vnull CallFrame.
Definition BodyEntry cpu cs := V293_create_prefix_state 701%positive 720%positive 713%positive
 211%positive 99%Z 97%Z 901%positive 11 cpu Vnull(BodyFrame Vundef Vundef)
 (spec_done None)(fun _=>false)[]cs.
Lemma BodyTableBindingEmpty : forall table, V293_tcb_table_binding table ==> Aemp.
Proof. intros table s [_[_ Empty]]. exact Empty. Qed.
Theorem BodyLiteralEntry : forall cpu cs,
 BodyState(BodyMemory Vnull Vundef StackInput Vundef cpu)cs |= BodyEntry cpu cs.
Proof.
 intros cpu cs.
 pose proof(BodyJointSpatial Vnull Vundef StackInput Vundef cpu cs)as H.
 unfold BodyExtraAsrt,StackEntry,StackFrame,RollbackBinding,V293_create_stack_arguments in H.
 assert(K:BodyState(BodyMemory Vnull Vundef StackInput Vundef cpu)cs |=
 LV 101%Z @ Tint8 |-> V293_byteval 11 **
 (BodyExtraAsrt cpu ** V293_tcb_empty_external 210%positive SuccessR(spec_done None)(fun _=>false)[]cs **
 LV 108%Z @ (Tptr Tint32) |->Vundef **
 V293_create_stack_arguments 17%Z StackArg StackInput(Vint32 Int.zero)
 (LV 209%Z @ Tint8 |->Vundef **
 LV 205%Z @ (Tptr Tint32) |->Vnull ** LV 206%Z @ Tint16 |->Vint32 Int.zero **
 LV 207%Z @ Tint32 |->Vint32(Int.repr 128) ** LV 208%Z @ (Tptr Tvoid) |->Vnull **
 (V293_tcb_table_binding 211%positive **
 (Amapsto(211%positive,44%Z)(Tptr V293_tcb_type)true Vnull ** CallFrame))))).
 { unfold BodyExtraAsrt,V293_create_stack_arguments. clear -H. sep auto. }
 clear H.
 eapply BodyLocalRaw with(x:=101%Z)(b:=701%positive)in K;[ |vm_compute;reflexivity].
 assert(J:BodyState(BodyMemory Vnull Vundef StackInput Vundef cpu)cs |=
 V293_create_prefix_bindings 701%positive 720%positive 713%positive 211%positive 99%Z 97%Z 901%positive **
 (Amapsto(701%positive,0%Z)Tint8 true(V293_byteval 11) **
 (BodyExtraAsrt cpu ** V293_tcb_empty_external 210%positive SuccessR(spec_done None)(fun _=>false)[]cs **
 LV 108%Z @ (Tptr Tint32) |->Vundef **
 V293_create_stack_arguments 17%Z StackArg StackInput(Vint32 Int.zero)
 (LV 209%Z @ Tint8 |->Vundef **
 LV 205%Z @ (Tptr Tint32) |->Vnull ** LV 206%Z @ Tint16 |->Vint32 Int.zero **
 LV 207%Z @ Tint32 |->Vint32(Int.repr 128) ** LV 208%Z @ (Tptr Tvoid) |->Vnull **
 (V293_tcb_table_binding 211%positive **
 (Amapsto(211%positive,44%Z)(Tptr V293_tcb_type)true Vnull ** CallFrame)))))).
 { eapply BodyStar with(m1:=emp);[apply map_join_comm;apply map_join_emp|apply BodyPrefixBindingsSpatial|exact K]. }
 unfold BodyEntry,BodyFrame,V293_create_prefix_state,V293_create_prefix_cells,
 V293_create_body_frame,V293_tcb_empty_external,V293_create_stack_arguments,BodyExtraAsrt,
 V293_create_prefix_bindings,V293_tcb_table_binding in *.
 cbn [V293_rdy_raw_cells]in *. clear -J. sep auto.
 eapply astar_mono in J;[ |apply BodyTableBindingEmpty|intros st HS;exact HS].
 apply astar_l_aemp_elim in J. exact J.
Qed.
Definition BodyKept := V293_create_failure_kept 210%positive Vnull Vnull
 (Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero)SuccessR
 (V293_create_stack_kept 17%Z StackArg StackInput
 (V293_create_prefix_kept 720%positive 713%positive 99%Z 97%Z 901%positive CallFrame)).
Definition BodyReturn cs := V293_create_failure_return 211%positive 11 BodyKept
 (spec_done None)(fun _=>false)[]cs.
Theorem BodyFullFunctionChecked : forall present cs running sched,
 InfRules(StackSpec present cs)V293_scheduler V293_witness_li V293_shared_inv
 (BodyReturn cs)Afalse(BodyEntry Vundef cs)
 (V293_CreateExt_body 92%Z 99%Z 97%Z running sched 902%Z 900%Z) Afalse SuccessTid.
Proof.
 intros. unfold BodyReturn,BodyKept,BodyEntry,BodyFrame.
 eapply V293_OSTaskCreateExt_empty_body_hoare with
 (good:=SuccessRFun)(gb:=SuccessRFun)(old:=fun _=>Vundef)(oldprev:=Vundef)(oldback:=Vundef)
 (slot:=Vundef)(table:=211%positive)(bg:=210%positive)(bt:=301%positive)
 (base:=128%Z)(p:=11)(top:=Vnull)(bottom:=Vnull)(identity:=Vint32 Int.zero)
 (size:=Vint32(Int.repr 128))(ext:=Vnull)(options:=Vint32 Int.zero)(next:=SuccessNext)
 (bh:=212%positive)(bgrp:=213%positive)(br:=214%positive)(bn:=215%positive)
 (oldblock:=301%positive)(oldbase:=256%Z)(present:=present)(g:=1)(row:=129)(n:=254)
 (Rbefore:=SuccessR)(aop:=spec_done None)(isr:=fun _=>false)(is:=[])(cs:=cs).
 - apply SuccessRGood.
 - apply SuccessRGood.
 - exact I.
 - lia.
 - repeat split;reflexivity.
 - apply SuccessRCurLINV.
 - repeat split;reflexivity.
 - apply SuccessRCurLINV.
 - apply StackLookup.
 - apply StackTCBLookup.
Qed.

Theorem BodyReturnSatisfiable : forall cs,
 BodyState(BodyMemory Vnull Vnull StackInput(Vint32(Int.repr 66))(Vint32 Int.zero))cs |=
 BodyReturn cs(Some(Vint32(Int.repr 66))).
Proof.
 intro cs.
 assert(J:BodyState(BodyMemory Vnull Vnull StackInput(Vint32(Int.repr 66))(Vint32 Int.zero))cs |=
 V293_create_prefix_bindings 701%positive 720%positive 713%positive 211%positive 99%Z 97%Z 901%positive **
 (BodyExtraAsrt(Vint32 Int.zero) ** StackEntry Vnull Vnull StackInput(Vint32(Int.repr 66))cs)).
 { eapply BodyStar with(m1:=emp);[apply map_join_comm;apply map_join_emp|apply BodyPrefixBindingsSpatial|apply BodyJointSpatial]. }
 unfold BodyReturn,V293_create_failure_return. apply astar_l_apure_intro;[ |reflexivity].
 unfold BodyKept,V293_create_failure_state,V293_create_failure_resources,V293_create_failure_kept,
 V293_create_stack_kept,V293_create_prefix_kept,BodyExtraAsrt,StackEntry,StackFrame,RollbackBinding,
 V293_tcb_empty_external,V293_create_stack_arguments,V293_create_prefix_bindings in *.
 cbn [V293_rdy_raw_cells]in *. clear -J. sep auto.
 assert(K:H7 |= V293_tcb_table_binding 211%positive **
 ((720%positive,0%Z)#Tint8|->V293_byteval 0 **
 (713%positive,0%Z)#Tint32|->Vint32 Int.zero **
 (211%positive,44%Z)#(Tptr V293_tcb_type)|->Vnull))by(clear -J;sep auto).
 eapply astar_mono in K;[ |apply BodyTableBindingEmpty|intros st HS;exact HS].
 apply astar_l_aemp_elim in K. clear -K. sep auto.
Qed.

(* Measure before rollback: its NULL write would erase the reserved identity.
   The entire literal entry, types and suffix stay fixed for both symbols. *)
Theorem BodyPrefixExecution : forall P ks cs suffix symbol token,
 get BodyLE symbol=None -> get BodyGE symbol=Some(token,Tint8) ->
 exists Mf,
 V293_local_steps P
 (curs(V293_TaskCreateExt_prefix 92%Z 101%Z 99%Z 109%Z symbol suffix),(kenil,ks))
 ((BodyGE,BodyLE,BodyMemory Vnull Vundef StackInput Vundef Vundef),(fun _=>false),(false,[],cs))
 (curs suffix,(kenil,kseq V293_TaskCreateExt_occupied ks))
 ((BodyGE,BodyLE,Mf),(fun _=>false),(false,[],cs)) /\
 load(Tptr V293_tcb_type)Mf(211%positive,44%Z)=Some(Vptr(token,Int.zero)).
Proof.
 intros P ks cs suffix symbol token Local Global.
 pose proof(BodyLiteralEntry Vundef cs)as Owned.
 unfold BodyEntry,V293_create_prefix_state in Owned.
 apply astar_l_aop'_elim in Owned. destruct Owned as[_ Owned].
 edestruct V293_OSTaskCreateExt_prefix_reserved with
 (P:=P)(ks:=ks)(ge:=BodyGE)(le:=BodyLE)
 (M:=BodyMemory Vnull Vundef StackInput Vundef Vundef)
 (ir:=fun (_:hid)=>false)(aux:=(false,(@nil hid),cs))(O:=(emp:osabst))(op:=spec_done None)
 (enabled:=false)(si:=(@nil hid))(ci:=cs)(table:=92%Z)(prio:=101%Z)(nesting:=99%Z)
 (cpu:=109%Z)(reserved:=symbol)(bp:=701%positive)(bn:=720%positive)(bc:=713%positive)
 (bt:=211%positive)(br:=token)(p:=11)(old:=Vundef)(suffix:=suffix)
 as[Mf[Trace Final]].
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - exact Local.
 - exact Global.
 - lia.
 - exact Owned.
 - exists Mf. split;[exact Trace| ]. unfold V293_create_prefix_cells in Final.
   V293_tcb_init_read Final 3%nat Read. exact Read.
Qed.
Theorem BodyActualReservedExecution : forall P ks cs suffix,
 exists Mf,
 V293_local_steps P
 (curs(V293_TaskCreateExt_prefix 92%Z 101%Z 99%Z 109%Z 97%Z suffix),(kenil,ks))
 ((BodyGE,BodyLE,BodyMemory Vnull Vundef StackInput Vundef Vundef),(fun _=>false),(false,[],cs))
 (curs suffix,(kenil,kseq V293_TaskCreateExt_occupied ks))
 ((BodyGE,BodyLE,Mf),(fun _=>false),(false,[],cs)) /\
 load(Tptr V293_tcb_type)Mf(211%positive,44%Z)=Some(Vptr(901%positive,Int.zero)).
Proof. intros. apply BodyPrefixExecution;vm_compute;reflexivity. Qed.
Theorem BodyWrongReservedExecution : forall P ks cs suffix,
 exists Mf,
 V293_local_steps P
 (curs(V293_TaskCreateExt_prefix 92%Z 101%Z 99%Z 109%Z 98%Z suffix),(kenil,ks))
 ((BodyGE,BodyLE,BodyMemory Vnull Vundef StackInput Vundef Vundef),(fun _=>false),(false,[],cs))
 (curs suffix,(kenil,kseq V293_TaskCreateExt_occupied ks))
 ((BodyGE,BodyLE,Mf),(fun _=>false),(false,[],cs)) /\
 load(Tptr V293_tcb_type)Mf(211%positive,44%Z)=Some(Vptr(902%positive,Int.zero)).
Proof. intros. apply BodyPrefixExecution;vm_compute;reflexivity. Qed.
