Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSamePriority.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBody.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStorageTail.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import Coq.Lists.List Lia.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHandoffHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedShared.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCritical.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRContext.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrentWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChangeWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitchWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.audit.probes.V293OSIntExitBoundarySwitchProbe.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.audit.probes.V293OSIntExitDispatchHoareProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyBody.
Require Import CertiOS.audit.probes.V293OSIntExitReadyHandoffProbe.

Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.invariant_prop.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceBridge.

Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyInternal.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.

Require Import CertiOS.audit.probes.V293OSIntExitReadyInternalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExactInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Definition XIfq aop ci:=V293_exact_builder_fpost
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil aop nil ci Aemp I.
Definition XIprogram:=V293_exit_exact_unit
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z 120%Z
 300%Z 200%Z 104%Z.
Definition XIspec nest c aop ci:=V293_exit_exact_spec
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive 16 0 6 nest RTentries nil OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipWaiting)c aop nil ci Aemp I 300%Z 200%Z.
(* A literal return boundary; the caller does not own the callee's saved cell. *)
Definition XIpost aop ci(result:option val):=
 [|result=None|] ** (<||aop||> **
 ((SWINV(V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells) **
 p_local V293_shared_li OwnershipWaiting nil) **
 ((Ais nil ** Acs ci) **
 (V293_sched_globals 100%Z 101%Z 102%Z 103%Z 92%positive 81%positive 80%positive 91%positive **
 (RBglobals ** Aemp))))).
Definition XIret aop ci result:=V293_exit_builder_cells 120%Z **
 XIpost aop ci result ** V293_exit_builder_domain 120%Z.
Definition XIcallerframe:=V293_exit_builder_cells 120%Z ** V293_exit_builder_domain 120%Z.
Lemma XIpost_identity : forall aop ci result,
 getasrt(XIfq aop ci nil result nil OwnershipWaiting)=XIpost aop ci result.
Proof. intros;reflexivity. Qed.
Theorem XIbuilders : forall nest c aop ci,
 BuildPreI XIprogram 300%Z nil nil(RBfp nest c aop ci)OwnershipWaiting=Some(RBpre 120%Z nest c aop ci) /\
 BuildRetI XIprogram 300%Z nil nil(XIfq aop ci)OwnershipWaiting=Some(XIret aop ci).
Proof. intros;split;reflexivity. Qed.
Theorem XIentry_owned : forall nest c old ci aop,nest<=1 ->
 JBstate(JBmemory nest c old)ci(sched;;aop)|=RBpre 120%Z nest c aop ci.
Proof. intros;apply RBpre_owned;assumption. Qed.
Theorem XIcall_entry_owned : forall nest c old ci aop,nest<=1 ->
 JBstate(JBmemory nest c old)ci(sched;;aop)|=
 getasrt(RBfp nest c aop ci nil nil OwnershipWaiting) ** XIcallerframe.
Proof.
 intros;pose proof(XIentry_owned nest c old ci aop H)as Entry;
 unfold RBpre,XIcallerframe in *;clear -Entry;sep auto.
Qed.
Theorem XIenvironment : forall nest c aop ci,
 WFFunEnv XIprogram(XIspec nest c aop ci)V293_scheduler V293_shared_li
 (V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells).
Proof.
 intros;unfold XIprogram,XIspec,JBcells;
 apply V293_OSIntExit_exact_WFFunEnv;try discriminate;exact I.
Qed.
Theorem XIactual_contract : forall nest c aop ci,
 InfRules(XIspec nest c aop ci)V293_scheduler V293_shared_li
 (V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells)
 (XIret aop ci)Afalse(RBpre 120%Z nest c aop ci)
 (V293_exit_boundary_body 112%Z 110%Z 111%Z 120%Z 105%Z 103%Z 106%Z 108%Z 109%Z 200%Z
 (V293_interrupt_handoff 103%Z 108%Z 106%Z))Afalse OwnershipWaiting.
Proof.
 intros;eapply V293_OSIntExit_exact_builder_contract with
 (P:=XIprogram)(f:=300%Z)(vl:=nil)(lg:=nil)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)
 (bo:=93%positive)(lo:=16)(hi:=0)(nc:=6)(nest:=nest)
 (entries:=RTentries)(tasks:=OwnershipTasks)(events:=emp)(now:=Int.zero)
 (hv:=V293_byteval 88)(out:=Vptr OwnershipWaiting)(c:=c)(aop:=aop)
 (si:=nil)(ci:=ci)(extra:=Aemp)(EG:=I);
 try discriminate;try exact I;reflexivity.
Qed.
Theorem XIactual_call : forall nest c aop ci RI r ri,
 InfRules(XIspec nest c aop ci)V293_scheduler V293_shared_li RI r ri
 (getasrt(RBfp nest c aop ci nil nil OwnershipWaiting) ** XIcallerframe)
 (scall 300%Z nil)(EX result:option val,XIpost aop ci result ** XIcallerframe)OwnershipWaiting.
Proof.
 intros;change(InfRules(XIspec nest c aop ci)V293_scheduler V293_shared_li RI r ri
 (getasrt(RBfp nest c aop ci nil nil OwnershipWaiting) ** XIcallerframe)
 (scall 300%Z nil)(EX result:option val,getasrt(XIfq aop ci nil result nil OwnershipWaiting) ** XIcallerframe)OwnershipWaiting).
 unfold RBfp,XIfq;apply V293_OSIntExit_exact_call with(EG:=I).
 - unfold XIcallerframe,V293_exit_builder_cells,V293_exit_builder_domain,Alvarmapsto,
 Alvarenv',Aptrmapsto;cbn[GoodFrm];tauto.
 - reflexivity.
Qed.
