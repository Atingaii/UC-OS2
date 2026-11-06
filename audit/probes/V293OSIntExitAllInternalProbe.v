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
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitChangedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.audit.probes.V293OSIntExitChangedBodyProbe.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.certiucos.v293.proofs.V293SpecEmbedding.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedJoint.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitAllInternal.
Require Import CertiOS.audit.probes.V293OSIntExitChangedInternalProbe.
Require Import CertiOS.audit.probes.V293OSIntExitUnifiedInternalProbe.
Require Import CertiOS.audit.probes.V293OSIntExitSameInternalProbe.
Require Import CertiOS.audit.probes.V293OSIntExitSamePriorityProbe.
Require Import CertiOS.audit.probes.V293OSIntExitBuildersProbe.
Require Import CertiOS.audit.probes.V293OSSchedISRContextProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceCodec.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptExitEnvironment.
Require Import CertiOS.framework.proof.toptheorem.
Import ListNotations.
Local Open Scope nat_scope.
Definition ACfp:=V293_all_exit_fpre 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 113%Z 111%Z 114%Z 115%Z 116%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 11%positive 12%positive
 13%positive 14%positive 15%positive Tvoid 0 16 4 1(V293_current_mode_entries true)nil
 (V293_current_mode_tasks true)emp Int.zero(V293_byteval 0)(Vptr V293_idle_tid)Int.one
 (spec_done None)nil nil Aemp I.
Definition ACfq:=V293_all_exit_fpost 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 113%Z 111%Z 114%Z 115%Z 116%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 11%positive 12%positive
 13%positive 14%positive 15%positive Tvoid(V293_current_mode_entries true)nil
 (spec_done None)nil nil Aemp I.
Definition ACspec:=V293_all_exit_env_spec 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 113%Z 111%Z 114%Z 115%Z 116%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 11%positive 12%positive
 13%positive 14%positive 15%positive Tvoid 0 16 4 1(V293_current_mode_entries true)nil
 (V293_current_mode_tasks true)emp Int.zero(V293_byteval 0)(Vptr V293_idle_tid)Int.one
 (spec_done None)nil nil Aemp I 300%Z 301%Z 200%Z.
Definition ACprogram:=V293_exit_env_unit 300%Z 301%Z 200%Z 114%Z 115%Z
 100%Z 101%Z 102%Z 103%Z 104%Z 117%Z
 (V293_exit_boundary_body 114%Z 115%Z 116%Z 117%Z 106%Z 103%Z 107%Z 113%Z 111%Z 200%Z
 (V293_interrupt_handoff 103%Z 113%Z 107%Z)).
Definition ACpre lg:=V293_exit_builder_cells 117%Z **
 getasrt(ACfp nil lg V293_idle_tid) ** V293_exit_builder_domain 117%Z.
Definition ACpost lg result:=V293_exit_builder_cells 117%Z **
 getasrt(ACfq nil result lg V293_idle_tid) ** V293_exit_builder_domain 117%Z.
Theorem ACenvironment :
 WFFunEnv ACprogram ACspec V293_scheduler V293_shared_li(V293_storage_inv CXcells 107%Z Tvoid) /\
 WFIFun ACprogram ACspec V293_scheduler(V293_storage_inv CXcells 107%Z Tvoid)V293_shared_li.
Proof.
 split;unfold ACprogram,ACspec.
 - apply V293_all_exit_env_WFFunEnv;try discriminate;exact I.
 - apply V293_all_exit_env_WFIFun;try discriminate;exact I.
Qed.
Lemma ACbuilders : forall lg,
 BuildPreI ACprogram 300%Z nil lg ACfp V293_idle_tid=Some(ACpre lg) /\
 BuildRetI ACprogram 300%Z nil lg ACfq V293_idle_tid=Some(ACpost lg).
Proof. intros;split;reflexivity. Qed.
Theorem ACchanged_nonempty : forall old,
 CXstate 1 Int.one old(spec_done None)|=ACpre(logic_ie true::nil).
Proof. intro;change(CXstate 1 Int.one old(spec_done None)|=CBpre 117%Z 1 Int.one(spec_done None));apply CBpre_owned;lia. Qed.
Theorem ACactual_contract : forall lg,
 InfRules ACspec V293_scheduler V293_shared_li(V293_storage_inv CXcells 107%Z Tvoid)
 (ACpost lg)Afalse(ACpre lg)
 (V293_exit_boundary_body 114%Z 115%Z 116%Z 117%Z 106%Z 103%Z 107%Z 113%Z 111%Z 200%Z
 (V293_interrupt_handoff 103%Z 113%Z 107%Z))Afalse V293_idle_tid.
Proof.
 intro lg;eapply V293_OSIntExit_all_builder_contract with(P:=ACprogram)(f:=300%Z)(vl:=nil)(lg:=lg)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(bo:=10%positive)
 (lo:=0)(hi:=16)(nc:=4)(nest:=1)(tasks:=V293_current_mode_tasks true)(events:=emp)(now:=Int.zero)
 (hv:=V293_byteval 0)(out:=Vptr V293_idle_tid)(c:=Int.one)(aop:=spec_done None)
 (si:=nil)(ci:=nil)(extra:=Aemp)(EG:=I);try discriminate;try exact I;reflexivity.
Qed.
Definition AQfp:=V293_all_exit_fpre 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 112%Z 108%Z 109%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 13%positive 14%positive
 16%positive 11%positive 12%positive Tvoid 0 16 4 1(V293_current_mode_entries true)nil
 (V293_current_mode_tasks true)emp Int.zero(V293_byteval 0)Vnull Int.one
 (spec_done None)nil nil Atrue I.
Definition AQpre lg:=V293_exit_builder_cells 120%Z **
 getasrt(AQfp nil (logic_ie false::lg)V293_idle_tid) ** V293_exit_builder_domain 120%Z.
Theorem AQquiet_nonempty : forall enabled,
 UBstate enabled 1 2 0|=AQpre(UBlogic enabled 1 2 0).
Proof. intro;change(UBstate enabled 1 2 0|=UBpre(UBlogic enabled 1 2 0)V293_idle_tid);apply UBquiet_pre_nonempty;lia. Qed.
Theorem AQsame_nonempty : forall enabled,
 QPstate enabled(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one)|=
 AQpre(V293_exit_same_args(BIlogic enabled)).
Proof. intro;change(QPstate enabled(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one)|=
 UBpre(V293_exit_same_args(BIlogic enabled))V293_idle_tid);apply UBsame_pre_nonempty. Qed.

Definition AJfp Inv0:=V293_joint_sched_fpre 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive V293_shared_li V293_opened_inv Inv0 V293_switch_li_good.
Definition AJfq Inv0:=V293_joint_sched_fpost 100%Z 101%Z 102%Z 103%Z
 1%positive 2%positive 3%positive 4%positive V293_shared_li V293_opened_inv Inv0 V293_switch_li_good.
Lemma AJcritical_exact : forall Inv0 vl lg t result,
 getasrt(AJfp Inv0 vl(logic_ie true::lg)t)=
 getasrt(V293_critical_fpre 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
 V293_shared_li V293_opened_inv V293_switch_li_good vl lg t) /\
 getasrt(AJfq Inv0 vl result(logic_ie true::lg)t)=
 getasrt(V293_critical_fpost 100%Z 101%Z 102%Z 103%Z 1%positive 2%positive 3%positive 4%positive
 V293_shared_li V293_opened_inv V293_switch_li_good vl result lg t).
Proof. intros;split;reflexivity. Qed.
Theorem AJISR_nonempty : forall Inv0 hv out nc nest c,
 BLstate(BLmemory hv out nest 0 nc c)|=
 getasrt(AJfp Inv0 nil(logic_ie false::QSlg nil)V293_idle_tid) ** Atrue.
Proof. intros;change(BLstate(BLmemory hv out nest 0 nc c)|=QSselected Inv0 nil ** Atrue);apply QSselector_nonempty. Qed.
Lemma AJtag_control : forall Inv0,
 V293_exit_path(logic_ie false::QSlg nil)=Some(false,QSlg nil) /\
 V293_exit_path(logic_ie true::QSlg nil)=Some(true,QSlg nil) /\
 V293_ISR_sched_args(QSlg nil)=Some(0,16,spec_done None,false,(fun _=>false),nil,nil) /\
 getasrt(AJfp Inv0 nil(logic_ie true::QSlg nil)V293_idle_tid)=Afalse.
Proof. intro;repeat split;try reflexivity;apply V293_ISR_sched_args_roundtrip;lia. Qed.
Theorem AJtag_rejects_same_state : forall Inv0 hv out nc nest c,
 ~(BLstate(BLmemory hv out nest 0 nc c)|=
 getasrt(AJfp Inv0 nil(logic_ie true::QSlg nil)V293_idle_tid) ** Atrue).
Proof.
 intros Inv0 hv out nc nest c Bad;change(BLstate(BLmemory hv out nest 0 nc c)|=Afalse ** Atrue)in Bad;
 apply astar_l_afalse_elim in Bad;exact Bad.
Qed.
Lemma AJvalue_call_excluded : forall e f args,~V293_void_calls(scalle e f args).
Proof. intros;exact(fun H=>H). Qed.
Lemma AJactual_body_accepted : V293_void_calls
 (V293_exit_boundary_body 114%Z 115%Z 116%Z 117%Z 106%Z 103%Z 107%Z 113%Z 111%Z 200%Z
 (V293_interrupt_handoff 103%Z 113%Z 107%Z)).
Proof. apply V293_exit_handoff_void_calls. Qed.
