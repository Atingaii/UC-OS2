(* Same finite CallSpec and frozen byte fixtures; only global 98 / block710 added. *)
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
Require Import CertiOS.audit.probes.V293TCBSuccessInternalProbe.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import Coq.Lists.List Lia.
Import Coq.Lists.List.ListNotations.
Local Open Scope nat_scope.
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
Import Coq.Lists.List.ListNotations.
Local Open Scope nat_scope.



Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackSuccess.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackCall.
Require Import CertiOS.certiucos.v293.proofs.V293TaskCreateStackEntry.
Require Import CertiOS.audit.probes.V293TaskCreateSuccessHoareProbe.

(* NULL is a typed call-site witness only, never a valid port stack claim.
   Existing GoodFunAsrt transport avoids rebuilding frozen byte fixtures. *)
Definition SSArg := Vptr(801%positive,Int.zero).
Definition SSInput := Vptr(802%positive,Int.repr 16).
Definition SSArgs := V293_create_stack_values 17%Z SSArg SSInput(Vint32 Int.zero).
Definition SSBefore present cs := CallFpre present cs SuccessArguments[logic_val SuccessHead]SuccessTid.
Definition SSHookPre present cs := V293_create_stack_resource_fpre(SSBefore present cs)SSArgs.
Definition SSOtherStack := Vptr(803%positive,Int.zero).
Definition SSHookPost present cs stack := V293_create_stack_resource_fpost(SSBefore present cs)SSArgs stack.
Definition SSSpec present cs : funspec := fun f=>
 if Z.eq_dec f 902%Z then Some(SSHookPre present cs,SSHookPost present cs Vnull,(Tptr Tint32,rev V293_stack_argument_types))
 else if Z.eq_dec f 903%Z then Some(SSHookPre present cs,SSHookPost present cs SSOtherStack,(Tptr Tint32,rev V293_stack_argument_types))
 else CallSpec present cs f.
Lemma SSHookLookup : forall present cs,
 SSSpec present cs 902%Z=Some(SSHookPre present cs,SSHookPost present cs Vnull,(Tptr Tint32,rev V293_stack_argument_types)).
Proof. intros. unfold SSSpec. destruct(Z.eq_dec 902%Z 902%Z);[reflexivity|contradiction]. Qed.
Lemma SSOtherLookup : forall present cs,
 SSSpec present cs 903%Z=Some(SSHookPre present cs,SSHookPost present cs SSOtherStack,(Tptr Tint32,rev V293_stack_argument_types)).
Proof. intros. unfold SSSpec. destruct(Z.eq_dec 903%Z 902%Z);[discriminate| ]. destruct(Z.eq_dec 903%Z 903%Z);[reflexivity|contradiction]. Qed.
Lemma SSTCBLookup : forall present cs,
 SSSpec present cs 900%Z=Some(CallFpre present cs,CallFpost present cs,(Tint8,rev V293_TCBInit_argument_types)).
Proof. intros. unfold SSSpec. destruct(Z.eq_dec 900%Z 902%Z);[discriminate| ]. destruct(Z.eq_dec 900%Z 903%Z);[discriminate|apply CallLookup]. Qed.
Definition SSLE : env := set(set(set CallLE 201%Z(711%positive,Tint32))
 202%Z(712%positive,Tptr Tvoid))203%Z(713%positive,Tptr Tint32).
Definition SSState M cs : RstateOP :=
 (IdleGE,SSLE,M,(fun _=>false),(false,[],cs),(emp:osabst),spec_done None).
Definition SSExtra := merge(CallByte 711%positive Tint32(V293_task_selector 17%Z))
 (merge(CallByte 712%positive(Tptr Tvoid)SSArg)(CallByte 713%positive(Tptr Tint32)SSInput)).
Definition SSKept F := V293_create_stack_kept 17%Z SSArg SSInput F.
Definition SSPre present cs :=
 getasrt(SSBefore present cs) ** LV 108%Z @ (Tptr Tint32) |->Vundef **
 V293_create_stack_arguments 17%Z SSArg SSInput(Vint32 Int.zero)
 (LV 209%Z @ Tint8 |->Vundef ** LV 101%Z @ Tint8 |->V293_byteval 11 **
 LV 205%Z @ (Tptr Tint32) |->Vnull ** LV 206%Z @ Tint16 |->Vint32 Int.zero **
 LV 207%Z @ Tint32 |->Vint32(Int.repr 128) ** LV 208%Z @ (Tptr Tvoid) |->Vnull **
 (V293_create_idle_running 98%Z 710%positive ** CallFrame)).
Definition SSPost present cs := V293_create_success_return 98%Z 710%positive
 (getasrt(CallFpost present cs SuccessArguments(Some(Vint32 Int.zero))[logic_val SuccessHead]SuccessTid) **
 V293_create_tcb_arguments 11 Vnull Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero)(SSKept CallFrame)).
Definition SSBody := V293_TaskCreateExt_calls 108%Z 902%Z 201%Z 202%Z 203%Z 204%Z 209%Z 900%Z
 101%Z 205%Z 206%Z 207%Z 208%Z (V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z 98%Z 901%Z).
Theorem SSHoareChecked : forall present cs,
 InfRules(SSSpec present cs)V293_scheduler V293_witness_li V293_shared_inv
 (SSPost present cs) Afalse(SSPre present cs)SSBody Afalse SuccessTid.
Proof.
 intros. unfold SSPre,SSPost,SSBody,SSKept.
 eapply V293_OSTaskCreateExt_stack_success_hoare with
 (good:=SuccessRFun) (before:=SSBefore present cs) (old:=fun _=>Vundef) (oldprev:=Vundef) (oldback:=Vundef)
 (slot:=Vundef) (table:=211%positive) (bg:=210%positive) (bt:=301%positive)
 (base:=128%Z) (p:=11) (top:=Vnull) (bottom:=Vnull) (identity:=Vint32 Int.zero)
 (size:=Vint32(Int.repr 128)) (ext:=Vnull) (options:=Vint32 Int.zero) (next:=SuccessNext)
 (bh:=212%positive) (bgrp:=213%positive) (br:=214%positive) (bn:=215%positive)
 (oldblock:=301%positive) (oldbase:=256%Z) (present:=present) (g:=1) (row:=129) (n:=254)
 (aop:=spec_done None) (isr:=fun _=>false) (is:=[]) (cs:=cs).
 - exact I.
 - repeat split;reflexivity.
 - unfold SSBefore,CallFpre,SuccessInternalFpre.
   cbn [V293_tcb_snapshot_fpre V293_tcb_guard_fpre V293_tcb_success_fpre getasrt].
   do 2 apply V293_star_CurLINV_r. unfold V293_tcb_success_external.
   apply V293_hook_resource_linv. apply V293_star_CurLINV_r. apply SuccessRCurLINV.
 - lia.
 - repeat split;reflexivity.
 - apply SuccessRCurLINV.
 - apply SSHookLookup.
 - apply SSTCBLookup.
Qed.
Lemma SSStar : forall m1 m2 m cs A B,
 join m1 m2 m -> SSState m1 cs |= A -> SSState m2 cs |= B -> SSState m cs |= A ** B.
Proof.
 intros. apply sat_split'. exists m1. exists m2. exists(emp:osabst). exists(emp:osabst).
 split;[exact H| ]. split;[apply map_join_emp| ]. split;assumption.
Qed.
Lemma SSLVar : forall b x tp v cs,
 get SSLE x=Some(b,tp) -> SSState(CallByte b tp v)cs |= LV x @ tp |->v.
Proof.
 intros b x tp v cs Env. exists b. eapply SSStar with(m1:=emp)(m2:=CallByte b tp v).
 - apply map_join_comm;apply map_join_emp.
 - exists b. split;[exact Env| ]. repeat split;reflexivity.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.
Ltac SSLocalApart b :=
 apply map_join_merge;apply map_disjoint;intros[other off];
 destruct(Pos.eq_dec other b);[subst other;right;left|left];
 unfold CallByte;
 repeat first[rewrite map_merge_semp by reflexivity|
 rewrite V293_encoded_memory_outside by(left;congruence)];reflexivity.
Ltac SSLocalTactic :=
 lazymatch goal with
 | |- SSState(merge(CallByte ?b ?tp ?v)?tail)?cs |= LV ?x @ ?tp |-> ?v ** _ =>
   eapply SSStar with(m1:=CallByte b tp v)(m2:=tail);
   [SSLocalApart b|apply SSLVar;vm_compute;reflexivity|SSLocalTactic]
 | |- SSState(CallByte 709%positive Tint8(Vint32(Int.repr 77)))?cs |= _ =>
   split;[apply V293_encoded_memory_mapsto|reflexivity]
 end.
Lemma SSLocalsSpatial : forall psp err cs,
 SSState(CallLocals psp Vnull err)cs |= LV 209%Z @ Tint8 |->err ** CallArgs psp Vnull.
Proof. intros. unfold CallLocals,CallArgs,V293_create_tcb_arguments,CallFrame. SSLocalTactic. Qed.
Lemma SSExtraSpatial : forall cs, SSState SSExtra cs |= SSKept Aemp.
Proof.
 intros. unfold SSExtra,SSKept,V293_create_stack_kept.
 eapply SSStar with(m1:=CallByte 711%positive Tint32(V293_task_selector 17%Z)).
 - SSLocalApart 711%positive.
 - apply SSLVar;vm_compute;reflexivity.
 - eapply SSStar with(m1:=CallByte 712%positive(Tptr Tvoid)SSArg).
   + SSLocalApart 712%positive.
   + apply SSLVar;vm_compute;reflexivity.
   + eapply SSStar with(m1:=CallByte 713%positive(Tptr Tint32)SSInput)(m2:=emp).
     * apply map_join_emp.
     * apply SSLVar;vm_compute;reflexivity.
     * split;reflexivity.
Qed.
Lemma SSExternalSpatial : forall present cs,
 SSState(CallReadyMemory present)cs |= getasrt(SSBefore present cs).
Proof.
 intros. unfold SSBefore,CallFpre,SuccessInternalFpre.
 cbn[V293_tcb_snapshot_fpre V293_tcb_guard_fpre getasrt].
 apply astar_l_apure_intro;[ |reflexivity].
 cbn[V293_tcb_success_fpre getasrt]. apply astar_l_apure_intro;[ |reflexivity].
 eapply good_fun_asrt_absop.
 - apply V293_tcb_success_external_good. exact SuccessRFun.
 - apply IdleReadySpatial.
Qed.
Lemma SSRunningSpatial : forall cs, SSState IdleByte cs |= V293_create_idle_running 98%Z 710%positive.
Proof.
 intro cs. unfold V293_create_idle_running,V293_create_global_binding.
 eapply SSStar with(m1:=emp)(m2:=IdleByte).
 - apply map_join_comm;apply map_join_emp.
 - split.
   + exists 710%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
   + split;[intros[v H];vm_compute in H;discriminate H|repeat split;reflexivity].
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
Qed.

Lemma SSExtraRunning : forall cs,
 SSState(merge SSExtra IdleByte)cs |= SSKept Aemp ** V293_create_idle_running 98%Z 710%positive.
Proof.
 intros. eapply SSStar.
 - apply map_join_merge;apply map_disjoint;intros[b off].
   destruct(Pos.eq_dec b 710%positive);[subst b;left|right;left].
   + unfold SSExtra,CallByte. SuccessOutside.
   + unfold IdleByte. apply V293_encoded_memory_outside;left;congruence.
 - apply SSExtraSpatial.
 - apply SSRunningSpatial.
Qed.
Lemma SSFresh : forall present psp err,
 join(merge(CallReadyMemory present)(CallLocals psp Vnull err))(merge SSExtra IdleByte)
 (merge(merge(CallReadyMemory present)(CallLocals psp Vnull err))(merge SSExtra IdleByte)).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 711%positive);[subst b;left| ].
 { destruct present;unfold CallReadyMemory,CallLocals,CallByte,SuccessExternalCells,
   V293_tcb_success_pre_owned,V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 destruct(Pos.eq_dec b 712%positive);[subst b;left| ].
 { destruct present;unfold CallReadyMemory,CallLocals,CallByte,SuccessExternalCells,
   V293_tcb_success_pre_owned,V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 destruct(Pos.eq_dec b 713%positive);[subst b;left| ].
 { destruct present;unfold CallReadyMemory,CallLocals,CallByte,SuccessExternalCells,
   V293_tcb_success_pre_owned,V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 destruct(Pos.eq_dec b 710%positive);[subst b;left| ].
 { destruct present;unfold CallReadyMemory,CallLocals,CallByte,SuccessExternalCells,
   V293_tcb_success_pre_owned,V293_tcb_init_old_fields,V293_tcb_prefix_links,V293_link_extra,
   SuccessCurrent,SuccessSentinel,SuccessBytes;cbn[app tl SuccessMemory];SuccessOutside. }
 right;left. unfold SSExtra,CallByte,IdleByte. SuccessOutside.
Qed.
Theorem SSLiteralEntry : forall present cs,
 SSState(merge(merge(CallReadyMemory present)(CallLocals Vundef Vnull Vundef))(merge SSExtra IdleByte))cs |= SSPre present cs.
Proof.
 intros. assert(H:SSState(merge(merge(CallReadyMemory present)(CallLocals Vundef Vnull Vundef))(merge SSExtra IdleByte))cs |=
 (getasrt(SSBefore present cs) ** LV 209%Z @ Tint8 |->Vundef ** CallArgs Vundef Vnull) **
 (SSKept Aemp ** V293_create_idle_running 98%Z 710%positive)).
 { eapply SSStar.
   - apply SSFresh.
   - eapply SSStar.
     + apply(CallFreshApart present false).
     + apply SSExternalSpatial.
     + apply SSLocalsSpatial.
   - apply SSExtraRunning. }
 unfold SSPre,SSKept,V293_create_stack_kept,V293_create_stack_arguments,CallArgs,V293_create_tcb_arguments in *.
 clear -H. sep auto.
Qed.
Theorem SSEntrySatisfiable : forall present cs, exists s, s |= SSPre present cs.
Proof. intros. eexists. apply SSLiteralEntry. Qed.
Theorem SSActualStackArguments : forall present cs,
 SSState(merge(merge(CallReadyMemory present)(CallLocals Vundef Vnull Vundef))(merge SSExtra IdleByte))cs |=
 Rvl[evar 201%Z;evar 202%Z;evar 203%Z;evar 204%Z]@(rev V293_stack_argument_types)==SSArgs.
Proof.
 intros. pose proof(SSLiteralEntry present cs)as H.
 eapply V293_create_stack_arguments_read with(F:=Atrue).
 - repeat split;reflexivity.
 - unfold SSPre,V293_create_stack_arguments in *. clear -H. sep auto.
Qed.

Theorem SSOtherPostRejectsNull : forall present cs s,
 s |= getasrt(SSHookPost present cs SSOtherStack SSArgs(Some Vnull)[]SuccessTid) -> False.
Proof.
 intros present cs s H. cbn [SSHookPost V293_create_stack_resource_fpost getasrt]in H.
 apply astar_l_apure_elim in H. destruct H as[[_ Bad] _]. discriminate Bad.
Qed.
Theorem SSHookNullPostInhabited : forall present cs,
 SSState(CallReadyMemory present)cs |=
 getasrt(SSHookPost present cs Vnull SSArgs(Some Vnull)[]SuccessTid).
Proof.
 intros. cbn [SSHookPost V293_create_stack_resource_fpost getasrt].
 apply astar_l_apure_intro;[apply SSExternalSpatial|split;reflexivity].
Qed.

Theorem SSSameSpecCallee : forall present cs saved,
 InfRules(SSSpec present cs)V293_scheduler V293_witness_li V293_shared_inv
 (CallInternalPost present cs saved) Afalse (CallInternalPre present cs saved)
 (V293_TCBInit_function_body 501%Z 502%Z) Afalse SuccessTid.
Proof.
 intros present cs saved.
 eapply V293_OS_TCBInit_snapshot_internal_contract
 with (P:=SuccessProgram) (f:=900%Z) (vl:=rev SuccessArguments) (lg:=[logic_val saved])
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
 - unfold SSSpec. destruct(Z.eq_dec 501%Z 902%Z);[discriminate| ].
   destruct(Z.eq_dec 501%Z 903%Z);[discriminate| ].
   unfold CallSpec. destruct(Z.eq_dec 501%Z 900%Z);[discriminate|apply SuccessInitLookup].
 - unfold SSSpec. destruct(Z.eq_dec 502%Z 902%Z);[discriminate| ].
   destruct(Z.eq_dec 502%Z 903%Z);[discriminate| ].
   unfold CallSpec. destruct(Z.eq_dec 502%Z 900%Z);[discriminate|apply SuccessCreateLookup].
 - reflexivity.
 - reflexivity.
 - reflexivity.
Qed.

