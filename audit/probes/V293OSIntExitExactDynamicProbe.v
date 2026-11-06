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
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptExitEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Require Import CertiOS.framework.proof.toptheorem.

Require Import CertiOS.audit.probes.V293OSIntExitReadyDynamicProbe.
Require Import CertiOS.audit.probes.V293OSIntExitExactInternalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExactDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactJoint.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyLocal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Definition XDfq:=V293_exact_dynamic_exit_fpost
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil Aemp I.
Definition XDspec:=V293_exact_dynamic_spec
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil Aemp I 300%Z 301%Z 200%Z.
Definition XDpost lg result:=V293_exit_builder_cells 120%Z **
 getasrt(XDfq nil result lg OwnershipWaiting) ** V293_exit_builder_domain 120%Z.
Lemma XDsame_program : RDprogram=V293_ready_irq_unit
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z 120%Z
 300%Z 301%Z 200%Z 104%Z.
Proof. reflexivity. Qed.
Theorem XDbuilders : forall lg,
 BuildPreI RDprogram 300%Z nil lg RDfp OwnershipWaiting=Some(RDpre lg) /\
 BuildRetI RDprogram 300%Z nil lg XDfq OwnershipWaiting=Some(XDpost lg).
Proof. intros;split;reflexivity. Qed.
Lemma XDliteral_post : forall nest c aop ci result,
 getasrt(XDfq nil result(RDlg nest c aop ci)OwnershipWaiting)=XIpost aop ci result.
Proof.
 intros;unfold XDfq,RDlg,V293_exact_dynamic_exit_fpost,V293_exit_path,
 V293_exact_dynamic_changed_fpost;rewrite V293_changed_codec_roundtrip;reflexivity.
Qed.
Theorem XDentry_owned : forall nest c old aop ci,nest<=1 ->
 JBstate(JBmemory nest c old)ci(sched;;aop)|=RDpre(RDlg nest c aop ci).
Proof. apply RDchanged_nonempty. Qed.
Theorem XDcall_entry_owned : forall nest c old aop ci,nest<=1 ->
 JBstate(JBmemory nest c old)ci(sched;;aop)|=
 getasrt(RDfp nil(RDlg nest c aop ci)OwnershipWaiting) ** XIcallerframe.
Proof.
 intros;pose proof(XDentry_owned nest c old aop ci H)as Entry.
 unfold RDpre,XIcallerframe in *;clear -Entry;sep auto.
Qed.
Theorem XDenvironment :
 GoodI RDinv V293_scheduler V293_shared_li /\
 WFFunEnv RDprogram XDspec V293_scheduler V293_shared_li RDinv /\
 WFIFun RDprogram XDspec V293_scheduler RDinv V293_shared_li.
Proof.
 split;[apply V293_ready_storage_good| ];split;rewrite XDsame_program;unfold XDspec.
 - apply V293_exact_dynamic_WFFunEnv;try discriminate;exact I.
 - apply V293_exact_dynamic_WFIFun;try discriminate;exact I.
Qed.
Theorem XDactual_contract : forall lg,
 InfRules XDspec V293_scheduler V293_shared_li RDinv
 (XDpost lg)Afalse(RDpre lg)
 (V293_exit_boundary_body 112%Z 110%Z 111%Z 120%Z 105%Z 103%Z 106%Z 108%Z 109%Z 200%Z
 (V293_interrupt_handoff 103%Z 108%Z 106%Z))Afalse OwnershipWaiting.
Proof.
 intro lg;eapply V293_OSIntExit_exact_dynamic_builder_contract with(P:=RDprogram)(f:=300%Z)(vl:=nil)(lg:=lg)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(bo:=93%positive)(rest:=nil)(extra:=Aemp)(EG:=I);
 try discriminate;try exact I;reflexivity.
Qed.
Theorem XDactual_call : forall nest c aop ci RI r ri,
 InfRules XDspec V293_scheduler V293_shared_li RI r ri
 (getasrt(RDfp nil(RDlg nest c aop ci)OwnershipWaiting) ** XIcallerframe)
 (scall 300%Z nil)(EX result:option val,XIpost aop ci result ** XIcallerframe)OwnershipWaiting.
Proof.
 intros;change(InfRules XDspec V293_scheduler V293_shared_li RI r ri
 (getasrt(RDfp nil(RDlg nest c aop ci)OwnershipWaiting) ** XIcallerframe)
 (scall 300%Z nil)(EX result:option val,
 getasrt(XDfq nil result(RDlg nest c aop ci)OwnershipWaiting) ** XIcallerframe)OwnershipWaiting).
 unfold RDfp,XDfq,RDlg;apply V293_OSIntExit_exact_dynamic_changed_call with(EG:=I).
 - unfold XIcallerframe,V293_exit_builder_cells,V293_exit_builder_domain,Alvarmapsto,
   Alvarenv',Aptrmapsto;cbn[GoodFrm];tauto.
 - reflexivity.
Qed.
(* Same full physical entry, only the logical counter snapshot is changed.
   Both codec inputs are legal; this stops at the counter load boundary. *)
Theorem XDcounter_control : forall old ci,
 V293_changed_decode(V293_changed_encode(RDsnapshot 1 Int.one(spec_done None)ci))=
 Some(RDsnapshot 1 Int.one(spec_done None)ci) /\
 V293_changed_decode(V293_changed_encode(RDsnapshot 1(Int.repr Int.max_unsigned)(spec_done None)ci))=
 Some(RDsnapshot 1(Int.repr Int.max_unsigned)(spec_done None)ci) /\
 (JBstate(JBmemory 1(Int.repr Int.max_unsigned)old)ci(sched;;spec_done None)|=
 RDpre(RDlg 1(Int.repr Int.max_unsigned)(spec_done None)ci)) /\
 ~(JBstate(JBmemory 1(Int.repr Int.max_unsigned)old)ci(sched;;spec_done None)|=
 RDpre(RDlg 1 Int.one(spec_done None)ci)).
Proof. apply RDcounter_dynamic_control. Qed.
Lemma XDquiet_same_kept : forall vl result lg t,
 XDfq vl result(logic_ie false::lg)t=RDfq vl result(logic_ie false::lg)t.
Proof. intros;reflexivity. Qed.
Lemma XDmalformed : forall t,
 getasrt(RDfp nil(logic_ie true::nil)t)=Afalse /\
 getasrt(XDfq nil None(logic_ie true::nil)t)=Afalse.
Proof. intro;split;reflexivity. Qed.
Lemma XDpost_ignores_counter : forall nest c c' aop ci result,
 XDpost(RDlg nest c aop ci)result=XDpost(RDlg nest c' aop ci)result.
Proof. intros;unfold XDpost;rewrite !XDliteral_post;reflexivity. Qed.
