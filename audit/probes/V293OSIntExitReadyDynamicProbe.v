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

Definition RDfp:=V293_ready_dynamic_exit_fpre
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil Aemp I.
Definition RDfq:=V293_ready_dynamic_exit_fpost
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil Aemp I.
Definition RDspec:=V293_ready_dynamic_exit_env_spec
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil Aemp I 300%Z 301%Z 200%Z.
Definition RDprogram:=V293_exit_env_unit 300%Z 301%Z 200%Z 112%Z 110%Z
 100%Z 101%Z 102%Z 103%Z 104%Z 120%Z
 (V293_exit_boundary_body 112%Z 110%Z 111%Z 120%Z 105%Z 103%Z 106%Z 108%Z 109%Z 200%Z
 (V293_interrupt_handoff 103%Z 108%Z 106%Z)).
Definition RDinv:=V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells.
Definition RDpre lg:=V293_exit_builder_cells 120%Z **
 getasrt(RDfp nil lg OwnershipWaiting) ** V293_exit_builder_domain 120%Z.
Definition RDpost lg result:=V293_exit_builder_cells 120%Z **
 getasrt(RDfq nil result lg OwnershipWaiting) ** V293_exit_builder_domain 120%Z.
Definition RDsnapshot nest c aop ci:=V293_mk_changed_snapshot
 (Int.repr 16)Int.zero(Int.repr 6)(Int.repr(Z.of_nat nest))
 RTentries OwnershipTasks emp Int.zero(V293_byteval 88)(Vptr OwnershipWaiting)c aop nil ci.
Definition RDlg nest c aop ci:=logic_ie true::V293_changed_encode(RDsnapshot nest c aop ci).
Theorem RDenvironment :
 GoodI RDinv V293_scheduler V293_shared_li /\
 WFFunEnv RDprogram RDspec V293_scheduler V293_shared_li RDinv /\
 WFIFun RDprogram RDspec V293_scheduler RDinv V293_shared_li.
Proof.
 split;[apply V293_ready_storage_good| ];split;unfold RDprogram,RDspec.
 - apply V293_ready_dynamic_exit_env_WFFunEnv;try discriminate;exact I.
 - apply V293_ready_dynamic_exit_env_WFIFun;try discriminate;exact I.
Qed.
Lemma RDbuilders : forall lg,
 BuildPreI RDprogram 300%Z nil lg RDfp OwnershipWaiting=Some(RDpre lg) /\
 BuildRetI RDprogram 300%Z nil lg RDfq OwnershipWaiting=Some(RDpost lg).
Proof. intros;split;reflexivity. Qed.
Theorem RDactual_contract : forall lg,
 InfRules RDspec V293_scheduler V293_shared_li RDinv
 (RDpost lg)Afalse(RDpre lg)
 (V293_exit_boundary_body 112%Z 110%Z 111%Z 120%Z 105%Z 103%Z 106%Z 108%Z 109%Z 200%Z
 (V293_interrupt_handoff 103%Z 108%Z 106%Z))Afalse OwnershipWaiting.
Proof.
 intro lg;eapply V293_OSIntExit_ready_dynamic_builder_contract with(P:=RDprogram)(f:=300%Z)(vl:=nil)(lg:=lg)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(bo:=93%positive)(rest:=nil)(extra:=Aemp)(EG:=I);
 try discriminate;try exact I;reflexivity.
Qed.
Lemma RDpre_reduces : forall nest c aop ci,nest<256 ->
 RDpre(RDlg nest c aop ci)=RBpre 120%Z nest c aop ci.
Proof.
 intros nest c aop ci B;unfold RDpre,RDlg,RDfp,V293_ready_dynamic_exit_fpre,V293_exit_path,
 V293_ready_dynamic_changed_fpre;rewrite V293_changed_codec_roundtrip.
 cbn[RDsnapshot V293_clo V293_chi V293_ccurrent V293_cnest V293_centries V293_ctasks
 V293_cevents V293_cnow V293_chigh V293_cout V293_ccounter V293_caop V293_cstack V293_ccritical getasrt].
 rewrite V293_sched_snapshot_roundtrip by exact B;reflexivity.
Qed.
Theorem RDchanged_nonempty : forall nest c old aop ci,nest<=1 ->
 JBstate(JBmemory nest c old)ci(sched;;aop)|=RDpre(RDlg nest c aop ci).
Proof. intros;rewrite RDpre_reduces by lia;apply RBpre_owned;assumption. Qed.
Theorem RDentry_nonempty : forall nest c(old:int32)aop ci,nest<=1 ->exists st,
 st|=RDpre(RDlg nest c aop ci) /\
 V293_highest_ready OwnershipTasks OwnershipReady /\ OwnershipReady<>OwnershipWaiting.
Proof. intros;rewrite RDpre_reduces by lia;eapply RBentry_nonempty;eassumption. Qed.
Lemma RDcounter_load : forall nest c aop ci st,nest<256 ->
 st|=RDpre(RDlg nest c aop ci) ->
 load Tint32(getmem st)(95%positive,0%Z)=Some(Vint32 c).
Proof.
 intros nest c aop ci st B Held;rewrite RDpre_reduces in Held by exact B.
 assert(P:st|=PV(95%positive,Int.zero)@Tint32|->Vint32 c ** Atrue).
 { unfold RBpre,RBfp,V293_ready_builder_fpre,V293_ready_builder_pre,
   V293_ready_builder_external,V293_ready_builder_memory in Held;
   cbn[getasrt]in Held;clear -Held;sep auto. }
 eapply V293_star_load_l;[ |exact P];intros s[M _];eapply mapstoval_load;[reflexivity|exact M].
Qed.
(* Change only the logical snapshot of one fixed physical state. This is an
   entry-resource control, not two complete function executions. *)
Theorem RDcounter_dynamic_control : forall old ci,
 V293_changed_decode(V293_changed_encode(RDsnapshot 1 Int.one(spec_done None)ci))=
 Some(RDsnapshot 1 Int.one(spec_done None)ci) /\
 V293_changed_decode(V293_changed_encode(RDsnapshot 1(Int.repr Int.max_unsigned)(spec_done None)ci))=
 Some(RDsnapshot 1(Int.repr Int.max_unsigned)(spec_done None)ci) /\
 (JBstate(JBmemory 1(Int.repr Int.max_unsigned)old)ci(sched;;spec_done None)|=
 RDpre(RDlg 1(Int.repr Int.max_unsigned)(spec_done None)ci)) /\
 ~(JBstate(JBmemory 1(Int.repr Int.max_unsigned)old)ci(sched;;spec_done None)|=
 RDpre(RDlg 1 Int.one(spec_done None)ci)).
Proof.
 intros old ci;split;[apply V293_changed_codec_roundtrip| ];split;[apply V293_changed_codec_roundtrip| ].
 split;[apply RDchanged_nonempty;lia| ].
 intro Wrong;pose proof(RDcounter_load 1 Int.one(spec_done None)ci _ ltac:(lia)Wrong)as W.
 pose proof(RDcounter_load 1(Int.repr Int.max_unsigned)(spec_done None)ci _ ltac:(lia)
 (RDchanged_nonempty 1(Int.repr Int.max_unsigned)old(spec_done None)ci ltac:(lia)))as A.
 rewrite A in W;vm_compute in W;discriminate.
Qed.
Theorem RDzero_max_entry : forall(old:int32)ci aop,exists st,
 st|=RDpre(RDlg 0(Int.repr Int.max_unsigned)aop ci).
Proof.
 intros;exists(JBstate(JBmemory 0(Int.repr Int.max_unsigned)old)ci(sched;;aop));apply RDchanged_nonempty;lia.
Qed.
Lemma RDpost_forgets_counter : forall nest c c' aop ci result,
 RDpost(RDlg nest c aop ci)result=RDpost(RDlg nest c' aop ci)result.
Proof.
 intros;unfold RDpost,RDlg,RDfq,V293_ready_dynamic_exit_fpost,V293_exit_path,
 V293_ready_dynamic_changed_fpost;rewrite !V293_changed_codec_roundtrip;reflexivity.
Qed.
Lemma RDmalformed : forall t,
 V293_changed_decode nil=None /\
 getasrt(RDfp nil(logic_ie true::nil)t)=Afalse /\
 getasrt(RDfq nil None(logic_ie true::nil)t)=Afalse.
Proof. intro;repeat split;reflexivity. Qed.
Lemma RDpath_tag_reduces : forall vl lg t,
 RDfp vl(logic_ie false::lg)t=
 V293_unified_exit_fpre 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 110%Z 111%Z 112%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 96%positive 97%positive 99%positive V293_tcb_type V293_shared_li Aemp V293_switch_li_good I vl lg t.
Proof. intros;reflexivity. Qed.
