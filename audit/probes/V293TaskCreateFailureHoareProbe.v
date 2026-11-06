(* Composition witness reuses Stage93/96 literal bytes; it is not an
   independent source translation or a call allocation/free execution. *)
Require Import CertiOS.audit.probes.V293TaskCreateTCBCallProbe.
Require Import CertiOS.audit.probes.V293TCBSuccessInternalProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.rulesoundlib.
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

Definition RollbackReserved := Vptr(901%positive,Int.zero).
Definition RollbackSlot v := V293_encoded_memory 211%positive 44%Z true(encode_val(Tptr V293_tcb_type)v).
Definition RollbackRest err := merge CallEmptyMemory(CallLocals Vnull Vnull err).
Definition RollbackMemory slot err := merge(RollbackSlot slot)(RollbackRest err).
Definition RollbackBinding := V293_tcb_table_binding 211%positive.
Definition RollbackFrame := RollbackBinding **
 (Amapsto(211%positive,44%Z)(Tptr V293_tcb_type)true RollbackReserved ** CallFrame).
Definition RollbackPre present cs :=
 getasrt(CallFpre present cs SuccessArguments[logic_val Vnull]SuccessTid) **
 LV 209%Z @ Tint8 |-> Vundef **
 V293_create_tcb_arguments 11 Vnull Vnull(Vint32 Int.zero)(Vint32(Int.repr 128))
 Vnull(Vint32 Int.zero)RollbackFrame.
Definition RollbackKept := V293_create_failure_kept 210%positive Vnull Vnull
 (Vint32 Int.zero)(Vint32(Int.repr 128))Vnull(Vint32 Int.zero)SuccessR CallFrame.
Definition RollbackReturn cs := V293_create_failure_return 211%positive 11 RollbackKept
 (spec_done None)(fun _=>false)[]cs.
Lemma RollbackApart : forall v err,
 join(RollbackSlot v)(RollbackRest err)(RollbackMemory v err).
Proof.
 intros. apply map_join_merge;apply map_disjoint;intros[b off].
 destruct(Pos.eq_dec b 211%positive);[subst b;right;left|left].
 - unfold RollbackRest,CallEmptyMemory,CallLocals,CallByte,
   SuccessCurrent,SuccessSentinel,SuccessBytes. SuccessOutside.
 - unfold RollbackSlot. rewrite V293_encoded_memory_outside by(left;congruence). reflexivity.
Qed.
Lemma RollbackBindingSpatial : forall cs,CallState emp cs |= RollbackBinding.
Proof.
 intro cs. unfold RollbackBinding,V293_tcb_table_binding.
 split.
 - exists 211%positive. split;[vm_compute;reflexivity| ]. repeat split;reflexivity.
 - split.
   + intros[x Bad]. vm_compute in Bad. discriminate.
   + repeat split;reflexivity.
Qed.
Theorem RollbackLiteralEntry : forall present cs,
 CallState(RollbackMemory RollbackReserved Vundef)cs |= RollbackPre present cs.
Proof.
 intros present cs.
 assert(K:CallState(RollbackMemory RollbackReserved Vundef)cs |=
 Amapsto(211%positive,44%Z)(Tptr V293_tcb_type)true RollbackReserved **
 (CallPre present cs Vnull ** RollbackBinding)).
 { eapply CallStar with(m1:=RollbackSlot RollbackReserved)(m2:=RollbackRest Vundef).
   - apply RollbackApart.
   - split;[apply V293_encoded_memory_mapsto|reflexivity].
   - eapply CallStar with(m1:=RollbackRest Vundef)(m2:=emp).
     + apply map_join_emp.
     + apply CallLiteralEmptyEntry.
     + apply RollbackBindingSpatial. }
 unfold RollbackPre,RollbackFrame,CallPre,CallArgs,V293_create_tcb_arguments.
 unfold CallPre,CallArgs,V293_create_tcb_arguments in K. clear -K. sep auto.
Qed.
Theorem RollbackCallSuffixChecked : forall present cs running sched,
 InfRules(CallSpec present cs)V293_scheduler V293_witness_li V293_shared_inv
 (RollbackReturn cs)Afalse(RollbackPre present cs)
 (sseq(V293_TaskCreateExt_TCB_call 209%Z 900%Z 101%Z 108%Z 205%Z 206%Z 207%Z 208%Z 204%Z)
 (V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z running sched))Afalse SuccessTid.
Proof.
 intros present cs running sched. unfold RollbackReturn,RollbackKept,RollbackPre,RollbackFrame,RollbackBinding.
 eapply V293_OSTaskCreateExt_empty_call_suffix_hoare with
 (good:=SuccessRFun)(old:=fun _=>Vundef)(oldprev:=Vundef)(oldback:=Vundef)
 (reserved:=RollbackReserved)(slot:=Vundef)(table:=211%positive)(bg:=210%positive)(bt:=301%positive)
 (base:=128%Z)(p:=11)(top:=Vnull)(bottom:=Vnull)(identity:=Vint32 Int.zero)
 (size:=Vint32(Int.repr 128))(ext:=Vnull)(options:=Vint32 Int.zero)(next:=SuccessNext)
 (bh:=212%positive)(bgrp:=213%positive)(br:=214%positive)(bn:=215%positive)
 (oldblock:=301%positive)(oldbase:=256%Z)(present:=present)(g:=1)(row:=129)(n:=254)
 (aop:=spec_done None)(isr:=fun _=>false)(is:=[])(cs:=cs).
 - apply SuccessRGood.
 - exact I.
 - lia.
 - repeat split;reflexivity.
 - apply SuccessRCurLINV.
 - apply CallLookup.
Qed.

(* Concrete post-call state: exactly the same caller bytes, with err=66.
   Both controls enter this SAME reachable error branch; only the assignment
   is replaced below. Non-NULL reserved token is not treated as a real TCB. *)
Definition RollbackBefore := RollbackMemory RollbackReserved(Vint32(Int.repr 66)).
Definition RollbackAfter := match store(Tptr V293_tcb_type)RollbackBefore(211%positive,44%Z)Vnull with
 |Some m=>m|None=>emp end.
Definition RollbackRemainder cs :=
 (V293_tcb_empty_external 210%positive SuccessR(spec_done None)(fun _=>false)[]cs **
 (LV 209%Z @ Tint8 |-> Vint32(Int.repr 66) ** CallArgs Vnull Vnull)) ** RollbackBinding.
Lemma RollbackBeforeSpatial : forall cs,
 CallState RollbackBefore cs |=
 Amapsto(211%positive,44%Z)(Tptr V293_tcb_type)true RollbackReserved ** RollbackRemainder cs.
Proof.
 intro cs. eapply CallStar with(m1:=RollbackSlot RollbackReserved)(m2:=RollbackRest(Vint32(Int.repr 66))).
 - apply RollbackApart.
 - split;[apply V293_encoded_memory_mapsto|reflexivity].
 - unfold RollbackRemainder. eapply CallStar with(m1:=RollbackRest(Vint32(Int.repr 66)))(m2:=emp).
   + apply map_join_emp.
   + unfold RollbackRest. eapply CallStar with(m1:=CallEmptyMemory)(m2:=CallLocals Vnull Vnull(Vint32(Int.repr 66))).
     * apply(CallFreshApart false true).
     * apply CallEmptySpatial.
     * apply CallLocalsSpatial.
   + apply RollbackBindingSpatial.
Qed.
Lemma RollbackStore : store(Tptr V293_tcb_type)RollbackBefore(211%positive,44%Z)Vnull=Some RollbackAfter.
Proof.
 destruct(V293_tick_raw_slot_update (211%positive,44%Z)(Tptr V293_tcb_type)RollbackReserved Vnull _ _ _ _ _ _ _ _
 ltac:(reflexivity)(RollbackBeforeSpatial nil))as[Mf[Store Updated]].
 unfold RollbackAfter. rewrite Store. reflexivity.
Qed.
Theorem RollbackAfterSpatial : forall cs,
 CallState RollbackAfter cs |=
 V293_create_failure_state 211%positive 11 Vnull RollbackKept(spec_done None)(fun _=>false)[]cs.
Proof.
 intro cs. destruct(V293_tick_raw_slot_update (211%positive,44%Z)(Tptr V293_tcb_type)RollbackReserved Vnull _ _ _ _ _ _ _ _
 ltac:(reflexivity)(RollbackBeforeSpatial cs))as[Mf[Store Updated]].
 rewrite RollbackStore in Store. inversion Store;subst Mf.
 unfold V293_owned_record_cell in Updated. apply astar_assoc_elim in Updated.
 apply astar_l_apure_elim in Updated. destruct Updated as[_ Updated].
 unfold V293_create_failure_state,V293_create_failure_resources,RollbackKept,V293_create_failure_kept.
 unfold RollbackRemainder,V293_tcb_empty_external,CallArgs,V293_create_tcb_arguments,RollbackBinding in Updated.
 clear -Updated. sep auto.
Qed.
Theorem RollbackReturnSatisfiable : forall cs,
 CallState RollbackAfter cs |= RollbackReturn cs (Some(Vint32(Int.repr 66))).
Proof.
 intro cs. unfold RollbackReturn,V293_create_failure_return.
 apply astar_l_apure_intro;[apply RollbackAfterSpatial|reflexivity].
Qed.
Lemma RollbackBeforeFull : forall cs,
 CallState RollbackBefore cs |=
 V293_create_failure_state 211%positive 11 RollbackReserved RollbackKept(spec_done None)(fun _=>false)[]cs.
Proof.
 intro cs. pose proof(RollbackBeforeSpatial cs)as H.
 unfold V293_create_failure_state,V293_create_failure_resources,RollbackKept,V293_create_failure_kept.
 unfold RollbackRemainder,V293_tcb_empty_external,CallArgs,V293_create_tcb_arguments,RollbackBinding in H.
 clear -H. sep auto.
Qed.
Lemma RollbackRawRead : forall M cs a tp perm v,
 rule_type_val_match tp v=true ->
 CallState M cs |= Amapsto a tp perm v ** Atrue -> load tp M a=Some v.
Proof.
 intros M cs a tp perm v Valid Owned.
 change(load tp(getmem(CallState M cs))a=Some v).
 eapply V293_star_load_l;[ |exact Owned]. intros st[Map Empty].
 eapply mapstoval_load;[exact Valid|exact Map].
Qed.
Lemma RollbackLocalRead : forall M cs x b tp v,
 get CallLE x=Some(b,tp) -> rule_type_val_match tp v=true ->
 CallState M cs |= LV x @ tp |->v ** Atrue ->load tp M(b,0%Z)=Some v.
Proof.
 intros M cs x b tp v Env Valid Owned.
 assert(Read:CallState M cs |= Rv(evar x) @ tp == v).
 { eapply lvar_rv with(perm:=true)(P:=Atrue);assumption. }
 cbn [sat getsmem get_smem evalval evaltype get_lenv get_mem CallState]in Read.
 cbv delta [env var memory.ident Modules.ident]in *. rewrite Env in Read.
 exact(proj1 Read).
Qed.
Theorem RollbackBeforeReads :
 load Tint8 RollbackBefore(701%positive,0%Z)=Some(V293_byteval 11) /\
 load Tint8 RollbackBefore(708%positive,0%Z)=Some(Vint32(Int.repr 66)) /\
 load(Tptr V293_tcb_type)RollbackBefore(211%positive,44%Z)=Some RollbackReserved /\
 load(Tptr V293_tcb_type)RollbackBefore(210%positive,0%Z)=Some Vnull /\
 load Tint8 RollbackBefore(709%positive,0%Z)=Some(Vint32(Int.repr 77)).
Proof.
 pose proof(RollbackBeforeFull nil)as H.
 unfold V293_create_failure_state,V293_create_failure_resources,RollbackKept,V293_create_failure_kept,CallFrame in H.
 repeat split.
 - eapply RollbackLocalRead with(cs:=nil)(x:=101%Z);[vm_compute;reflexivity|reflexivity| ]. clear -H. sep auto.
 - eapply RollbackLocalRead with(cs:=nil)(x:=209%Z);[vm_compute;reflexivity|reflexivity| ]. clear -H. sep auto.
 - eapply RollbackRawRead with(cs:=nil)(perm:=true);[reflexivity| ]. clear -H. sep auto.
 - eapply RollbackRawRead with(cs:=nil)(perm:=false);[reflexivity| ]. clear -H. sep auto.
 - eapply RollbackRawRead with(cs:=nil)(perm:=true);[reflexivity| ]. clear -H. sep auto.
Qed.
Theorem RollbackAfterReads :
 load(Tptr V293_tcb_type)RollbackAfter(211%positive,44%Z)=Some Vnull.
Proof.
 pose proof(RollbackAfterSpatial nil)as H.
 assert(Owned:CallState RollbackAfter nil |= Amapsto(211%positive,44%Z)(Tptr V293_tcb_type)true Vnull ** Atrue).
 { unfold V293_create_failure_state,V293_create_failure_resources in H. clear -H. sep auto. }
 change(load(Tptr V293_tcb_type)(getmem(CallState RollbackAfter nil))(211%positive,44%Z)=Some Vnull).
 eapply V293_star_load_l;[ |exact Owned]. intros st[Map Empty].
 eapply mapstoval_load;[reflexivity|exact Map].
Qed.
Lemma RollbackAddress :
 evaltype(earrayelem(evar 92%Z)(evar 101%Z))(SuccessGE,CallLE,RollbackBefore)=Some(Tptr V293_tcb_type) /\
 evaladdr(earrayelem(evar 92%Z)(evar 101%Z))(SuccessGE,CallLE,RollbackBefore)=Some(Vptr(211%positive,Int.repr 44)).
Proof.
 pose proof(RollbackBeforeFull nil)as H.
 assert(Resources:CallState RollbackBefore nil |= V293_create_failure_resources 211%positive 11 RollbackReserved RollbackKept).
 { unfold V293_create_failure_state in H. clear -H. sep auto. }
 exact(V293_create_failure_address 211%positive 11 RollbackReserved RollbackKept
 (CallState RollbackBefore nil)ltac:(lia)Resources).
Qed.
Definition RollbackDeletedStore := sseq(sprim encrit)(sseq(sskip None)(sprim excrit)).
Theorem RollbackActualExecution : forall P ks ir is cs,
 V293_local_steps P
 (curs(V293_TaskCreateExt_rollback 92%Z 101%Z),(kenil,ks))
 ((SuccessGE,CallLE,RollbackBefore),ir,(false,is,cs))
 (curs(sskip None),(kenil,ks))
 ((SuccessGE,CallLE,RollbackAfter),ir,(false,is,cs)).
Proof.
 intros. unfold V293_TaskCreateExt_rollback.
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { apply encrit_step;reflexivity. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_trans.
 { apply V293_csteps_local. eapply V293_assign_pointer_execution with(tp:=V293_tcb_type)(tr:=Tptr V293_tcb_type)(b:=211%positive)(off:=44%Z)(value:=Vnull).
   - exact(proj1 RollbackAddress).
   - reflexivity.
   - apply eq_vptr. do 2 eexists;split;reflexivity.
   - exact(proj2 RollbackAddress).
   - reflexivity.
   - change(0<=44<=4294967295)%Z;lia.
   - apply RollbackStore. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { apply excrit_step;reflexivity. }
 apply V293_local_refl.
Qed.
Theorem RollbackDeletedStoreExecution : forall P ks ir is cs,
 V293_local_steps P (curs RollbackDeletedStore,(kenil,ks))
 ((SuccessGE,CallLE,RollbackBefore),ir,(false,is,cs))
 (curs(sskip None),(kenil,ks))
 ((SuccessGE,CallLE,RollbackBefore),ir,(false,is,cs)).
Proof.
 intros. unfold RollbackDeletedStore.
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { apply encrit_step;reflexivity. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { apply excrit_step;reflexivity. }
 apply V293_local_refl.
Qed.
Theorem RollbackDeletedStoreFailsPost :
 load(Tptr V293_tcb_type)RollbackBefore(211%positive,44%Z)<>Some Vnull.
Proof. destruct RollbackBeforeReads as[_[_[Read _]]]. rewrite Read. discriminate. Qed.

Theorem RollbackFalseGuard :
 evalval(ebinop oeq(evar 209%Z)(econst32 Int.zero))(SuccessGE,CallLE,RollbackBefore)=Some(Vint32 Int.zero).
Proof.
 exact(proj1(V293_create_failure_guard 211%positive 11 RollbackReserved RollbackKept
 (spec_done None)(fun _=>false)nil nil(CallState RollbackBefore nil)(RollbackBeforeFull nil))).
Qed.
Definition RollbackSuffixWith body running sched :=
 sseq(sif(ebinop oeq(evar 209%Z)(econst32 Int.zero))
 (sseq(sskip None)(sifthen(ebinop oeq(evar running)(econst32 Int.one))(scall sched nil)))body)
 (srete(evar 209%Z)).
Lemma RollbackSuffixTrace : forall P ks ir is cs running sched body Mf,
 V293_local_steps P(curs body,(kenil,kseq(srete(evar 209%Z))ks))
 ((SuccessGE,CallLE,RollbackBefore),ir,(false,is,cs))
 (curs(sskip None),(kenil,kseq(srete(evar 209%Z))ks))
 ((SuccessGE,CallLE,Mf),ir,(false,is,cs)) ->
 V293_local_steps P(curs(RollbackSuffixWith body running sched),(kenil,ks))
 ((SuccessGE,CallLE,RollbackBefore),ir,(false,is,cs))
 (curs(srete(evar 209%Z)),(kenil,ks))((SuccessGE,CallLE,Mf),ir,(false,is,cs)).
Proof.
 intros P ks ir is cs running sched body Mf Block. unfold RollbackSuffixWith.
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 eapply V293_local_trans.
 { apply V293_csteps_local. apply V293_expr_steps. apply evalval_imply_estepstar. exact RollbackFalseGuard. }
 eapply V293_local_cons.
 { apply ostc_step. eapply stmt_step;[reflexivity| ]. apply sviff_step;reflexivity. }
 eapply V293_local_trans. { exact Block. }
 eapply V293_local_cons. { V293_prefix_stmt. }
 apply V293_local_refl.
Qed.
Theorem RollbackActualSuffixExecution : forall P ks ir is cs running sched,
 V293_local_steps P(curs(V293_TaskCreateExt_suffix 92%Z 101%Z 209%Z running sched),(kenil,ks))
 ((SuccessGE,CallLE,RollbackBefore),ir,(false,is,cs))
 (curs(srete(evar 209%Z)),(kenil,ks))((SuccessGE,CallLE,RollbackAfter),ir,(false,is,cs)).
Proof. intros. apply RollbackSuffixTrace. apply RollbackActualExecution. Qed.
Theorem RollbackDeletedSuffixExecution : forall P ks ir is cs running sched,
 V293_local_steps P(curs(RollbackSuffixWith RollbackDeletedStore running sched),(kenil,ks))
 ((SuccessGE,CallLE,RollbackBefore),ir,(false,is,cs))
 (curs(srete(evar 209%Z)),(kenil,ks))((SuccessGE,CallLE,RollbackBefore),ir,(false,is,cs)).
Proof. intros. apply RollbackSuffixTrace. apply RollbackDeletedStoreExecution. Qed.
