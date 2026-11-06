(* Same finite specification for both allocation branches. Frozen literal fixtures
   are reused, not independently retranslated. Empty fixture changes ONLY the
   reserved-object global address to the success fixture address; owned bytes,
   C body and builder declarations are unchanged. No whole-execution claim. *)
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessHoare.
Require Import CertiOS.audit.probes.V293TaskCreateTCBCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPublish.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateBodyFailure.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtSuffix.
Require Import CertiOS.audit.probes.V293TCBSuccessInternalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateSuccessHoare.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSnapshotInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBEmptyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateTCBCall.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtCalls.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.certiucos.v293.proofs.V293InitTCBClear.
Require Import CertiOS.certiucos.v293.proofs.V293StartRecord.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFields.
Require Import CertiOS.certiucos.v293.proofs.V293TCBHookCall.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TCBLinkedHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateBodySuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBFieldsHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTaskCreateExtPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateSuccessInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateEmptyInternal.
Require Import CertiOS.tactics.hoareforward.init_spec.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateFailureHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.audit.probes.V293TaskCreateFailureHoareProbe.
Require Import CertiOS.audit.probes.V293TaskCreateStackCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InitAllRecords.
Require Import CertiOS.audit.probes.V293TaskCreateBodyFailureProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateRejectInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TCBUnifiedInternal.
Require Import CertiOS.audit.probes.V293TaskCreateSuccessInternalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateUnifiedInternal.
Require Import Coq.Logic.FunctionalExtensionality.
Import Coq.Lists.List.ListNotations.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Definition UIEmptyInternalArgs := V293_create_internal_values 17%Z StackArg StackInput 11
 (Vint32 Int.zero)Vnull(Vint32(Int.repr 128))Vnull(Vint32 Int.zero).
Definition UIEmptyInternalPre cs :=
 V293_create_internal_pre_cells 17%Z StackArg StackInput 11(Vint32 Int.zero)Vnull
 (Vint32(Int.repr 128))Vnull(Vint32 Int.zero) **
 ([|UIEmptyInternalArgs=UIEmptyInternalArgs|] **
 V293_create_internal_external 211%positive 720%positive 721%positive 210%positive 11 SuccessR
 (spec_done None)(fun _=>false)[]cs) ** V293_create_internal_domain.
Definition UIEmptyGE : env := set(set(set SuccessGE 97%Z(721%positive,Tint8))
 98%Z(902%positive,Tint8))99%Z(720%positive,Tint8).
Definition UIEmptyLE : env := set StackLE 109%Z(713%positive,Tint32).
Definition UIEmptyState M cs : RstateOP :=
 (UIEmptyGE,UIEmptyLE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Lemma UIEmptyStar : forall m1 m2 m cs A B,
 join m1 m2 m -> UIEmptyState m1 cs |= A -> UIEmptyState m2 cs |= B ->
 UIEmptyState m cs |= A ** B.
Proof.
 intros. apply sat_split'. exists m1. exists m2. exists(emp:osabst). exists(emp:osabst).
 split;[exact H| ]. split;[apply map_join_emp| ]. split;assumption.
Qed.
Lemma UIEmptyLVar : forall b x tp v cs,
 get UIEmptyLE x=Some(b,tp) -> UIEmptyState(CallByte b tp v)cs |= LV x @ tp |->v.
Proof.
 intros b x tp v cs Env. exists b.
 eapply UIEmptyStar with(m1:=emp)(m2:=CallByte b tp v).
 - apply map_join_comm;apply map_join_emp.
 - exists b. split;[exact Env| ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Ltac UIEmptyLocalApart b :=
 apply map_join_merge;apply map_disjoint;intros[other off];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold CallByte;
 repeat first[rewrite map_merge_semp by reflexivity|
 rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Ltac UIEmptyLocalTactic :=
 lazymatch goal with
 | |- UIEmptyState(merge(CallByte ?b ?tp ?v)?tail)?cs |= LV ?x @ ?tp |-> ?v ** _ =>
   eapply UIEmptyStar with(m1:=CallByte b tp v)(m2:=tail);
   [UIEmptyLocalApart b|apply UIEmptyLVar;vm_compute;reflexivity|UIEmptyLocalTactic]
 | |- UIEmptyState(CallByte 709%positive Tint8(Vint32(Int.repr 77)))?cs |= _ =>
   split;[apply V293_encoded_memory_mapsto|reflexivity]
 end.

Lemma UIEmptyLocalsSpatial : forall psp inputtop err cs,
 UIEmptyState(StackLocals psp inputtop err)cs |= StackLocalAsrt psp inputtop err.
Proof.
 intros. unfold StackLocals,StackLocalAsrt,V293_create_stack_kept,CallLocals,CallArgs,V293_create_tcb_arguments,CallFrame.
 UIEmptyLocalTactic.
Qed.
Lemma UIEmptyCurrentSpatial : forall cs, UIEmptyState SuccessCurrent cs |= CurTid SuccessTid.
Proof.
 intro cs. exists Tvoid. exists 402%positive.
 eapply UIEmptyStar with (m1:=emp) (m2:=SuccessCurrent).
 - apply map_join_comm;apply map_join_emp.
 - exists 402%positive. split;[vm_compute;reflexivity | ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma UIEmptyLInvSpatial : forall cs, UIEmptyState emp cs |= LINV V293_witness_li SuccessTid [].
Proof.
 intro cs. unfold LINV. apply astar_comm. apply astar_l_apure_intro.
 - split;reflexivity.
 - apply V293_witness_li_good.
Qed.
Ltac UIEmptyFrameApart b :=
 apply map_join_merge;apply map_disjoint;intros [other offset];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold SuccessCurrent,SuccessSentinel,SuccessBytes;
 repeat first [rewrite map_merge_semp by reflexivity |
 rewrite V293_encoded_memory_outside by (left;congruence)];reflexivity.
Lemma UIEmptyRSpatial : forall cs,
 UIEmptyState (merge SuccessCurrent SuccessSentinel) cs |= SuccessR.
Proof.
 intro cs. unfold SuccessR.
 eapply UIEmptyStar with (m1:=SuccessCurrent) (m2:=SuccessSentinel).
 - UIEmptyFrameApart 402%positive.
 - apply UIEmptyCurrentSpatial.
 - eapply UIEmptyStar with (m1:=emp) (m2:=SuccessSentinel).
   + apply map_join_comm;apply map_join_emp.
   + apply UIEmptyLInvSpatial.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma UIEmptyEmptySpatial : forall cs,
 UIEmptyState CallEmptyMemory cs |= V293_tcb_empty_external 210%positive SuccessR
 (spec_done None)(fun _=>false)[]cs.
Proof.
 intro cs. unfold V293_tcb_empty_external.
 eapply UIEmptyStar with(m1:=emp)(m2:=CallEmptyMemory).
 - apply map_join_comm;apply map_join_emp.
 - exists 210%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - unfold CallEmptyMemory. eapply UIEmptyStar with(m1:=SuccessBytes 210%positive false(Tptr V293_tcb_type)Vnull).
   + unfold SuccessCurrent,SuccessSentinel,SuccessBytes. UIEmptyLocalApart 210%positive.
   + split;[apply V293_encoded_memory_mapsto|reflexivity].
   + apply astar_l_aop'_intro;[ |reflexivity].
     assert(K:UIEmptyState(merge SuccessCurrent SuccessSentinel)cs |=
      Aisr(fun _=>false) ** Aie false ** (Ais nil) ** Acs cs ** SuccessR).
     { apply astar_l_aisr_intro;[ |reflexivity].
       apply astar_l_aie_intro;[ |reflexivity].
       apply astar_l_ais_intro;[ |reflexivity].
       apply astar_l_acs_intro;[ |reflexivity]. apply UIEmptyRSpatial. }
     clear -K. sep auto.
Qed.

Lemma UIEmptyBindingSpatial : forall cs,UIEmptyState emp cs |= RollbackBinding.
Proof.
 intro cs. unfold RollbackBinding,V293_tcb_table_binding. split.
 - exists 211%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - split;[intros[x Bad];vm_compute in Bad;discriminate|repeat split;reflexivity].
Qed.
Theorem UIEmptyStackLiteralEntry : forall slot psp inputtop err cs,
 UIEmptyState(StackMemory slot psp inputtop err)cs |= StackEntry slot psp inputtop err cs.
Proof.
 intros.
 assert(H:UIEmptyState(StackMemory slot psp inputtop err)cs |=
 Amapsto(211%positive,44%Z)(Tptr V293_tcb_type)true slot **
 ((V293_tcb_empty_external 210%positive SuccessR(spec_done None)(fun _=>false)[]cs **
 StackLocalAsrt psp inputtop err) ** RollbackBinding)).
 { eapply UIEmptyStar with(m1:=RollbackSlot slot)(m2:=StackRest psp inputtop err).
   - apply StackReserveApart.
   - split;[apply V293_encoded_memory_mapsto|reflexivity].
   - eapply UIEmptyStar with(m1:=StackRest psp inputtop err)(m2:=emp).
     + apply map_join_emp.
     + unfold StackRest. eapply UIEmptyStar with(m1:=CallEmptyMemory)(m2:=StackLocals psp inputtop err).
       * apply StackFreshApart.
       * apply UIEmptyEmptySpatial.
       * apply UIEmptyLocalsSpatial.
     + apply UIEmptyBindingSpatial. }
 unfold StackEntry,StackFrame,StackLocalAsrt,V293_create_stack_arguments,V293_create_stack_kept,
 CallArgs,V293_create_tcb_arguments in *. clear -H. sep auto.
Qed.
Lemma UIEmptyLocalRaw : forall M cs x b tp v F,
 get UIEmptyLE x=Some(b,tp) ->
 UIEmptyState M cs |= LV x @ tp |-> v ** F ->
 UIEmptyState M cs |= Amapsto(b,0%Z)tp true v ** F.
Proof.
 intros M cs x b tp v F Env Owned. unfold Alvarmapsto,Alvarenv',Aptrmapsto in Owned.
 apply astar_l_aexists_elim in Owned. destruct Owned as[actual Owned].
 apply astar_assoc_elim in Owned. apply astar_l_alvarenv_elim in Owned.
 destruct Owned as[[_ Bind]Owned]. change(get UIEmptyLE x=Some(actual,tp))in Bind.
 rewrite Env in Bind. inversion Bind;subst actual. exact Owned.
Qed.

Definition UIEmptyExtra cpu := merge(CallByte 720%positive Tint8(V293_byteval 0))
 (CallByte 713%positive Tint32 cpu).
Definition UIEmptyMemory slot psp inputtop err cpu :=
 merge(UIEmptyExtra cpu)(StackMemory slot psp inputtop err).
Definition UIEmptyExtraAsrt cpu :=
 Amapsto(720%positive,0%Z)Tint8 true(V293_byteval 0) **
 Amapsto(713%positive,0%Z)Tint32 true cpu.
Lemma UIEmptyExtraSpatial : forall cpu cs, UIEmptyState(UIEmptyExtra cpu)cs |= UIEmptyExtraAsrt cpu.
Proof.
 intros. unfold UIEmptyExtra,UIEmptyExtraAsrt.
 eapply UIEmptyStar with(m1:=CallByte 720%positive Tint8(V293_byteval 0)).
 - UIEmptyLocalApart 720%positive.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Lemma UIEmptyExtraApart : forall slot psp inputtop err cpu,
 join(UIEmptyExtra cpu)(StackMemory slot psp inputtop err)(UIEmptyMemory slot psp inputtop err cpu).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 720%positive);[subst b;right;left| ].
 { unfold StackMemory,StackRest,StackLocals,CallLocals,CallEmptyMemory,RollbackSlot,
   CallByte,SuccessCurrent,SuccessSentinel,SuccessBytes. SuccessOutside. }
 destruct(Pos.eq_dec b 713%positive);[subst b;right;left|left].
 { unfold StackMemory,StackRest,StackLocals,CallLocals,CallEmptyMemory,RollbackSlot,
   CallByte,SuccessCurrent,SuccessSentinel,SuccessBytes. SuccessOutside. }
 unfold UIEmptyExtra,CallByte. SuccessOutside.
Qed.
Lemma UIEmptyJointSpatial : forall slot psp inputtop err cpu cs,
 UIEmptyState(UIEmptyMemory slot psp inputtop err cpu)cs |=
 UIEmptyExtraAsrt cpu ** StackEntry slot psp inputtop err cs.
Proof.
 intros. eapply UIEmptyStar;[apply UIEmptyExtraApart|apply UIEmptyExtraSpatial|apply UIEmptyStackLiteralEntry].
Qed.
Lemma UIEmptyInternalExactDomain : eq_dom_env UIEmptyLE(getlenvdom V293_create_internal_declarations).
Proof.
 unfold eq_dom_env. intros x tp.
 destruct(Z.eq_dec x 109%Z)as[E109|E109].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold UIEmptyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 203%Z)as[E203|E203].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold UIEmptyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 202%Z)as[E202|E202].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold UIEmptyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 201%Z)as[E201|E201].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold UIEmptyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 209%Z)as[E209|E209].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold UIEmptyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 204%Z)as[E204|E204].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold UIEmptyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 208%Z)as[E208|E208].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold UIEmptyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 207%Z)as[E207|E207].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold UIEmptyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 206%Z)as[E206|E206].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold UIEmptyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 205%Z)as[E205|E205].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold UIEmptyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 108%Z)as[E108|E108].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold UIEmptyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 destruct(Z.eq_dec x 101%Z)as[E101|E101].
 { subst x. cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
   unfold UIEmptyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence.
   first[rewrite map_get_set|rewrite map_get_sig]. split.
   - intro H. repeat destruct H as[H|H];try discriminate;try contradiction;inversion H;subst;eexists;reflexivity.
   - intros[b H]. inversion H;subst. cbn. tauto. }
 cbn [V293_create_internal_declarations V293_CreateExt_parameters V293_CreateExt_locals revlcons getlenvdom].
 unfold UIEmptyLE,StackLE,CallLE. repeat rewrite map_get_set' by congruence. rewrite map_get_sig' by congruence.
 split.
 - intro H. repeat destruct H as[H|H];try contradiction;inversion H;congruence.
 - intros[b H]. discriminate.
Qed.
Theorem UIEmptyInternalLiteralFramedEntry : forall cs,
 UIEmptyState(UIEmptyMemory Vnull Vundef StackInput Vundef Vundef)cs |= UIEmptyInternalPre cs ** CallFrame.
Proof.
 intro cs. pose proof(UIEmptyJointSpatial Vnull Vundef StackInput Vundef Vundef cs)as H.
 unfold UIEmptyExtraAsrt,StackEntry,StackFrame,StackLocalAsrt,V293_create_stack_arguments,
 V293_create_stack_kept,CallArgs,V293_create_tcb_arguments in H.
 assert(J:UIEmptyState(UIEmptyMemory Vnull Vundef StackInput Vundef Vundef)cs |=
 Alvarenv 109%Z Tint32(713%positive,0%Z) **
 Agvarenv 99%Z Tint8(720%positive,0%Z) ** Agvarenv 97%Z Tint8(721%positive,0%Z) **
 (UIEmptyExtraAsrt Vundef ** StackEntry Vnull Vundef StackInput Vundef cs)).
 { apply astar_l_alvarenv_intro;[ |split;[reflexivity|vm_compute;reflexivity]].
   apply astar_l_agvarenv_intro;[ |split;[reflexivity|vm_compute;reflexivity]].
   apply astar_l_agvarenv_intro;[apply UIEmptyJointSpatial|split;[reflexivity|vm_compute;reflexivity]]. }
 unfold UIEmptyExtraAsrt,StackEntry,StackFrame,StackLocalAsrt,V293_create_stack_arguments,
 V293_create_stack_kept,CallArgs,V293_create_tcb_arguments in J.
 assert(K:UIEmptyState(UIEmptyMemory Vnull Vundef StackInput Vundef Vundef)cs |=
 ((Alvarenv 109%Z Tint32(713%positive,0%Z) ** Amapsto(713%positive,0%Z)Tint32 true Vundef) **
 V293_tcb_table_binding 211%positive) **
 (Agvarenv 99%Z Tint8(720%positive,0%Z) ** Agvarenv 97%Z Tint8(721%positive,0%Z) **
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
 assert(D:UIEmptyState(UIEmptyMemory Vnull Vundef StackInput Vundef Vundef)cs |=
 V293_create_internal_domain **
 ((LV 109%Z @ Tint32 |->Vundef ** Agvarenv 92%Z(Tarray(Tptr V293_tcb_type)13)(211%positive,0%Z)) **
 (Agvarenv 99%Z Tint8(720%positive,0%Z) ** Agvarenv 97%Z Tint8(721%positive,0%Z) **
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
 { apply astar_l_adomlenv_intro;[exact K|apply UIEmptyInternalExactDomain]. }
 unfold UIEmptyInternalPre,V293_create_internal_pre_cells,V293_create_internal_locals,
 V293_create_internal_external. change(4*Z.of_nat 11)%Z with 44%Z.
 clear -D. sep auto.
Qed.
Theorem UIEmptyInternalEntrySatisfiable : forall cs,exists s,s |= UIEmptyInternalPre cs.
Proof.
 intro cs. pose proof(UIEmptyInternalLiteralFramedEntry cs)as H.
 apply sat_split in H. destruct H as[m1[m2[O1[O2[_[_[Pre Rest]]]]]]].
 eexists;exact Pre.
Qed.

Definition UIEmptyFpre cs := V293_create_empty_fpre 211%positive 720%positive 721%positive
 210%positive 11 17%Z SIArg SIInput(Vint32 Int.zero)Vnull(Vint32(Int.repr 128))Vnull
 (Vint32 Int.zero)SuccessR(spec_done None)(fun _=>false)[]cs SuccessRFun.
Definition UIEmptyHookPre cs := V293_create_stack_fpre 210%positive SuccessR
 (spec_done None)(fun _=>false)[]cs SuccessRFun SIArgs.
Definition UIEmptyHookPost cs := V293_create_stack_fpost 210%positive SuccessR
 (spec_done None)(fun _=>false)[]cs SuccessRFun SIArgs Vnull.
Definition UIHookPre present cs := V293_create_stack_cases_fpre(UIEmptyHookPre cs)(SIHookPre present cs).
Definition UIHookPost present cs := V293_create_stack_cases_fpost(UIEmptyHookPost cs)(SIHookPost present cs).
Definition UISpec present cs : funspec := fun f=>
 if Z.eq_dec f 902%Z then Some(UIHookPre present cs,UIHookPost present cs,(Tptr Tint32,rev V293_stack_argument_types))
 else SISpec present cs f.
Definition UIFpre present cs := V293_create_unified_fpre 211%positive 720%positive 721%positive
 210%positive 301%positive 212%positive 213%positive 214%positive 215%positive 301%positive 710%positive
 128%Z 256%Z(fun _=>Vundef)present 11 1 129 254 0(750%positive,Int.zero)Vundef Vundef
 SuccessNext Vnull Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero)
 SIArg SIInput 17%Z SuccessR SuccessR(spec_done None)(fun _=>false)[]cs SuccessRFun SuccessRFun.
Definition UIFpost present cs := V293_create_unified_fpost 211%positive 720%positive 721%positive
 210%positive 301%positive 212%positive 213%positive 214%positive 215%positive 301%positive 710%positive
 128%Z 256%Z present 11 1 129 254 0(750%positive,Int.zero)SuccessNext
 Vnull Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero)SIArg SIInput
 SuccessR SuccessR(spec_done None)(fun _=>false)[]cs SuccessRFun SuccessRFun.
Definition UIBuilderPre present cs := V293_create_internal_pre_cells 17%Z SIArg SIInput 11
 (Vint32 Int.zero)Vnull(Vint32(Int.repr 128))Vnull(Vint32 Int.zero) **
 getasrt(UIFpre present cs SIValues[]SuccessTid) ** V293_create_internal_domain.
Definition UIBuilderPost present cs : retasrt := fun result=>V293_create_internal_post_cells **
 getasrt(UIFpost present cs SIValues result[]SuccessTid) ** V293_create_internal_domain.
Ltac UILookup := unfold UISpec,SISpec;repeat destruct(Z.eq_dec _ _);try discriminate;try contradiction;reflexivity.
Lemma UISharedLookups : forall present cs,
 UISpec present cs 902%Z=Some(UIHookPre present cs,UIHookPost present cs,(Tptr Tint32,rev V293_stack_argument_types)) /\
 UISpec present cs 900%Z=Some(SIFpre present cs,SIFpost present cs,(Tint8,rev V293_TCBInit_argument_types)).
Proof. intros;split;UILookup. Qed.
Lemma UIHookExactInstances : forall present cs vl result lg tid,
 getasrt(UIHookPre present cs vl(logic_ie false::lg)tid)=getasrt(UIEmptyHookPre cs vl lg tid) /\
 getasrt(UIHookPre present cs vl(logic_ie true::lg)tid)=getasrt(SIHookPre present cs vl lg tid) /\
 getasrt(UIHookPost present cs vl result(logic_ie false::lg)tid)=getasrt(UIEmptyHookPost cs vl result lg tid) /\
 getasrt(UIHookPost present cs vl result(logic_ie true::lg)tid)=getasrt(SIHookPost present cs vl result lg tid).
Proof. intros;repeat split;reflexivity. Qed.
Theorem UIRealBuilders : forall present cs,
 Some(UIBuilderPre present cs)=BuildPreI SIProgram 903%Z(rev SIValues)[](UIFpre present cs)SuccessTid /\
 Some(UIBuilderPost present cs)=BuildRetI SIProgram 903%Z(rev SIValues)[](UIFpost present cs)SuccessTid.
Proof.
 intros. unfold BuildPreI,BuildRetI,SIProgram.
 destruct(Z.eq_dec 903%Z 903%Z);[ |contradiction]. rewrite rev_involutive. split;reflexivity.
Qed.
Theorem UIContractChecked : forall present cs,
 InfRules(UISpec present cs)V293_scheduler V293_witness_li V293_shared_inv
 (UIBuilderPost present cs)Afalse(UIBuilderPre present cs)
 (V293_CreateExt_body 92%Z 99%Z 97%Z 98%Z 901%Z 902%Z 900%Z)Afalse SuccessTid.
Proof.
 intros present cs.
 eapply V293_OSTaskCreateExt_unified_internal_contract with
 (P:=SIProgram)(creator:=903%Z)(vl:=rev SIValues)(lg:=[])
 (good:=SuccessRFun)(gb:=SuccessRFun)(old:=fun _=>Vundef)(oldprev:=Vundef)(oldback:=Vundef)
 (table:=211%positive)(bg:=210%positive)(bt:=301%positive)(base:=128%Z)(p:=11)
 (top:=Vnull)(bottom:=Vnull)(identity:=Vint32 Int.zero)(size:=Vint32(Int.repr 128))
 (ext:=Vnull)(options:=Vint32 Int.zero)(next:=SuccessNext)(bh:=212%positive)(bgrp:=213%positive)
 (br:=214%positive)(bn:=215%positive)(oldblock:=301%positive)(oldbase:=256%Z)(present:=present)
 (g:=1)(row:=129)(n:=254)(nesting:=0)(occupied:=(750%positive,Int.zero))
 (R:=SuccessR)(Rbefore:=SuccessR)(aop:=spec_done None)(isr:=fun _=>false)(is:=[])(cs:=cs)
 (bnest:=720%positive)(breserved:=721%positive)(brun:=710%positive)
 (target:=17%Z)(argv:=SIArg)(inputtop:=SIInput).
 - apply SuccessRGood.
 - apply SuccessRGood.
 - apply SuccessRCurLINV.
 - apply SuccessRCurLINV.
 - discriminate.
 - apply UISharedLookups.
 - apply UISharedLookups.
 - unfold SIProgram;destruct(Z.eq_dec 903%Z 903%Z);[reflexivity|contradiction].
 - apply UIRealBuilders.
 - apply UIRealBuilders.
Qed.
Lemma UIAllocationValid : V293_create_allocation_valid 11 Vnull Vnull(Vint32 Int.zero)
 (Vint32(Int.repr 128))Vnull(Vint32 Int.zero)SIArg SIInput.
Proof. split;[lia| ]. split;repeat split;reflexivity. Qed.
Lemma UIReadyInject : forall present cs vl lg tid,
 getasrt(SICreatorPre present cs vl lg tid) ==> getasrt(UIFpre present cs vl lg tid).
Proof.
 intros present cs vl lg tid s H.
 unfold UIFpre,V293_create_unified_fpre;cbn[V293_tcb_union_fpre getasrt].
 right;right;right;right.
 unfold V293_create_union_ready_pre;cbn[V293_tcb_guard_fpre getasrt].
 apply astar_l_apure_intro;[exact H|apply UIAllocationValid].
Qed.
Lemma UIEmptyInject : forall present cs vl lg tid,
 getasrt(UIEmptyFpre cs vl lg tid) ==> getasrt(UIFpre present cs vl lg tid).
Proof.
 intros present cs vl lg tid s H.
 unfold UIFpre,V293_create_unified_fpre;cbn[V293_tcb_union_fpre getasrt].
 right;right;right;left.
 unfold V293_create_union_empty_pre;cbn[V293_tcb_guard_fpre getasrt].
 apply astar_l_apure_intro;[exact H|apply UIAllocationValid].
Qed.
Theorem UILiteralReadyEntry : forall present cpu cs,
 SIState(SIMemory present cpu)cs |= UIBuilderPre present cs ** CallFrame.
Proof.
 intros. pose proof(SILiteralBuilderEntry present cpu cs)as H.
 eapply astar_mono in H;[exact H| |intros s K;exact K].
 unfold SIBuilderPre,UIBuilderPre. apply astar_mono;[intros s K;exact K| ].
 apply astar_mono;[apply UIReadyInject|intros s K;exact K].
Qed.
Theorem UILiteralEmptyEntry : forall present cs,
 UIEmptyState(UIEmptyMemory Vnull Vundef StackInput Vundef Vundef)cs |= UIBuilderPre present cs ** CallFrame.
Proof.
 intros. pose proof(UIEmptyInternalLiteralFramedEntry cs)as H.
 eapply astar_mono in H;[exact H| |intros s K;exact K].
 unfold UIEmptyInternalPre,UIBuilderPre. apply astar_mono;[intros s K;exact K| ].
 apply astar_mono;[ |intros s K;exact K].
 change(getasrt(UIEmptyFpre cs SIValues[]SuccessTid) ==> getasrt(UIFpre present cs SIValues[]SuccessTid)).
 apply UIEmptyInject.
Qed.
Theorem UIUnifiedEntrySatisfiableSameSpec : forall present cs,
 (exists s,s |= UIBuilderPre present cs) /\
 UISpec present cs 902%Z=Some(UIHookPre present cs,UIHookPost present cs,(Tptr Tint32,rev V293_stack_argument_types)).
Proof.
 intros;split;[ |apply UISharedLookups].
 pose proof(UILiteralReadyEntry present Vundef cs)as H.
 apply sat_split in H;destruct H as[m1[m2[O1[O2[_[_[Pre Rest]]]]]]];eexists;exact Pre.
Qed.
Lemma UIInvalidPriorityCannotAllocate : ~V293_create_allocation_valid 13 Vnull Vnull(Vint32 Int.zero)
 (Vint32(Int.repr 128))Vnull(Vint32 Int.zero)SIArg SIInput.
Proof. intros[Bad _];lia. Qed.
(* The three rejection injections use the guarded branches already defined in
   the public union; they do not assert satisfiability at priority=11 for bad-prio. *)
Lemma UIRejectBadInject : forall present cs vl lg tid,
 getasrt(V293_create_union_reject_pre 211%positive 720%positive 11 0(750%positive,Int.zero)
 Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero)SIArg SIInput 17%Z
 SuccessR(spec_done None)(fun _=>false)[]cs SuccessRFun V293_create_bad_priority vl lg tid)
 ==> getasrt(UIFpre present cs vl lg tid).
Proof. intros present cs vl lg tid s H. left;exact H. Qed.
Lemma UIRejectISRInject : forall present cs vl lg tid,
 getasrt(V293_create_union_reject_pre 211%positive 720%positive 11 0(750%positive,Int.zero)
 Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero)SIArg SIInput 17%Z
 SuccessR(spec_done None)(fun _=>false)[]cs SuccessRFun V293_create_from_isr vl lg tid)
 ==> getasrt(UIFpre present cs vl lg tid).
Proof. intros present cs vl lg tid s H. right;left;exact H. Qed.
Lemma UIRejectOccupiedInject : forall present cs vl lg tid,
 getasrt(V293_create_union_reject_pre 211%positive 720%positive 11 0(750%positive,Int.zero)
 Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero)SIArg SIInput 17%Z
 SuccessR(spec_done None)(fun _=>false)[]cs SuccessRFun V293_create_occupied_priority vl lg tid)
 ==> getasrt(UIFpre present cs vl lg tid).
Proof. intros present cs vl lg tid s H. right;right;left;exact H. Qed.
Lemma UIAllocationInputHeads : forall present cpu,
 load(Tptr V293_tcb_type)(SIMemory present cpu)(210%positive,0%Z)=Some SuccessHead /\
 load(Tptr V293_tcb_type)(UIEmptyMemory Vnull Vundef StackInput Vundef Vundef)(210%positive,0%Z)=Some Vnull.
Proof.
 intros present cpu. split.
 - change(load(Tptr V293_tcb_type)(getmem(SIState(SIMemory present cpu)[]))(210%positive,0%Z)=Some SuccessHead).
   pose proof(SISplitSpatial present cpu [])as HS. unfold SISplit in HS.
   eapply V293_star_load_r;[ |exact HS]. intros st H.
   eapply V293_star_load_l;[ |exact H]. intros st1 H1.
   eapply V293_rdy_raw_load;[ |reflexivity|exact H1].
   unfold SIRestCells,SICells,V293_tcb_success_pre_owned. cbn[tl].
   apply in_or_app;right. apply in_or_app;left. unfold V293_tcb_prefix_links;left;reflexivity.
 - change(load(Tptr V293_tcb_type)(getmem(UIEmptyState(UIEmptyMemory Vnull Vundef StackInput Vundef Vundef)[]))
     (210%positive,0%Z)=Some Vnull).
   pose proof(UIEmptyJointSpatial Vnull Vundef StackInput Vundef Vundef [])as HS.
   eapply V293_star_load_r;[ |exact HS]. intros st H. unfold StackEntry in H.
   eapply V293_star_load_l;[ |exact H]. intros st1 H1. unfold V293_tcb_empty_external in H1.
   eapply V293_star_load_r;[ |exact H1]. intros st2 H2.
   eapply V293_star_load_l;[ |exact H2]. intros st3[Points Empty].
   eapply mapstoval_load;[reflexivity|exact Points].
Qed.
Theorem UIAllocationBranchesNonvacuous : forall present cs,
 (exists s,s |= SIBuilderPre present cs) /\
 (exists s,s |= UIEmptyInternalPre cs) /\
 UISpec present cs 902%Z=Some(UIHookPre present cs,UIHookPost present cs,(Tptr Tint32,rev V293_stack_argument_types)).
Proof.
 intros. split.
 - pose proof(SILiteralBuilderEntry present Vundef cs)as H.
   apply sat_split in H;destruct H as[m1[m2[O1[O2[_[_[Pre Rest]]]]]]];eexists;exact Pre.
 - split;[apply UIEmptyInternalEntrySatisfiable|apply UISharedLookups].
Qed.
Lemma UIReadySpecEmbedding : forall present cs,V293_spec_instances(SISpec present cs)(UISpec present cs).
Proof.
 intros present cs.
 assert(Same:V293_spec_replace(UISpec present cs)902%Z
 (SIHookPre present cs,SIHookPost present cs,(Tptr Tint32,rev V293_stack_argument_types))=SISpec present cs).
 { apply functional_extensionality;intro f. unfold V293_spec_replace,UISpec,SISpec.
   destruct(Z.eq_dec f 902%Z);reflexivity. }
 rewrite <-Same at 1.
 apply V293_create_stack_cases_embed with(ready:=true)
 (ep:=UIEmptyHookPre cs)(eq:=UIEmptyHookPost cs).
 - apply UISharedLookups.
 - apply V293_create_stack_retpost.
 - apply V293_create_stack_resource_retpost.
Qed.
Theorem UISameSpecCallee : forall present cs saved,
 InfRules(UISpec present cs)V293_scheduler V293_witness_li V293_shared_inv
 (CallInternalPost present cs saved)Afalse(SIInternalPre present cs saved)
 (V293_TCBInit_function_body 501%Z 502%Z)Afalse SuccessTid.
Proof.
 intros. eapply V293_InfRules_spec_instances;[apply SISameSpecCallee|apply UIReadySpecEmbedding].
Qed.
