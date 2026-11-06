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
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCall.
Definition DPfp:=V293_dynamic_exit_fpre 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 113%Z 111%Z 114%Z 115%Z 116%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 11%positive 12%positive
 13%positive 14%positive 15%positive Tvoid(length(V293_current_mode_entries true))nil Aemp I.
Definition DPfq:=V293_dynamic_exit_fpost 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 113%Z 111%Z 114%Z 115%Z 116%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 11%positive 12%positive
 13%positive 14%positive 15%positive Tvoid nil Aemp I.
Definition DPspec:=V293_dynamic_exit_env_spec 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 113%Z 111%Z 114%Z 115%Z 116%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 11%positive 12%positive
 13%positive 14%positive 15%positive Tvoid(length(V293_current_mode_entries true))nil Aemp I 300%Z 301%Z 200%Z.
Definition DPprogram:=V293_exit_env_unit 300%Z 301%Z 200%Z 114%Z 115%Z
 100%Z 101%Z 102%Z 103%Z 104%Z 117%Z
 (V293_exit_boundary_body 114%Z 115%Z 116%Z 117%Z 106%Z 103%Z 107%Z 113%Z 111%Z 200%Z
 (V293_interrupt_handoff 103%Z 113%Z 107%Z)).
Definition DPpre lg:=V293_exit_builder_cells 117%Z **
 getasrt(DPfp nil lg V293_idle_tid) ** V293_exit_builder_domain 117%Z.
Definition DPpost lg result:=V293_exit_builder_cells 117%Z **
 getasrt(DPfq nil result lg V293_idle_tid) ** V293_exit_builder_domain 117%Z.
Definition DPsnapshot nest c aop:=V293_mk_changed_snapshot
 Int.zero(Int.repr 16)(Int.repr 4)(Int.repr(Z.of_nat nest))
 (V293_current_mode_entries true)(V293_current_mode_tasks true)emp Int.zero
 (V293_byteval 0)(Vptr V293_idle_tid)c aop nil nil.
Definition DPlg nest c aop:=logic_ie true::V293_changed_encode(DPsnapshot nest c aop).
Theorem DPenvironment :
 WFFunEnv DPprogram DPspec V293_scheduler V293_shared_li(V293_storage_inv CXcells 107%Z Tvoid) /\
 WFIFun DPprogram DPspec V293_scheduler(V293_storage_inv CXcells 107%Z Tvoid)V293_shared_li.
Proof.
 split;unfold DPprogram,DPspec.
 - apply V293_dynamic_exit_env_WFFunEnv;try discriminate;exact I.
 - apply V293_dynamic_exit_env_WFIFun;try discriminate;exact I.
Qed.
Lemma DPbuilders : forall lg,
 BuildPreI DPprogram 300%Z nil lg DPfp V293_idle_tid=Some(DPpre lg) /\
 BuildRetI DPprogram 300%Z nil lg DPfq V293_idle_tid=Some(DPpost lg).
Proof. intros;split;reflexivity. Qed.
Theorem DPactual_contract : forall lg,
 InfRules DPspec V293_scheduler V293_shared_li(V293_storage_inv CXcells 107%Z Tvoid)
 (DPpost lg)Afalse(DPpre lg)
 (V293_exit_boundary_body 114%Z 115%Z 116%Z 117%Z 106%Z 103%Z 107%Z 113%Z 111%Z 200%Z
 (V293_interrupt_handoff 103%Z 113%Z 107%Z))Afalse V293_idle_tid.
Proof.
 intro lg;eapply V293_OSIntExit_dynamic_builder_contract with(P:=DPprogram)(f:=300%Z)(vl:=nil)(lg:=lg)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(bo:=10%positive)
 (table_length:=length(V293_current_mode_entries true))(rest:=nil)(extra:=Aemp)(EG:=I);
 try discriminate;try exact I;reflexivity.
Qed.
Lemma DPpre_reduces : forall nest c aop,nest<256 ->
 DPpre(DPlg nest c aop)=
 V293_exit_builder_cells 117%Z **
 ([|length(V293_current_mode_entries true)=length(V293_current_mode_entries true)|] **
 getasrt(CBfp nest c aop nil nil V293_idle_tid)) ** V293_exit_builder_domain 117%Z.
Proof.
 intros nest c aop B;unfold DPpre,DPlg,DPfp,V293_dynamic_exit_fpre,V293_exit_path,
 V293_dynamic_changed_fpre;rewrite V293_changed_codec_roundtrip.
 cbn[DPsnapshot V293_clo V293_chi V293_ccurrent V293_cnest V293_centries V293_ctasks
 V293_cevents V293_cnow V293_chigh V293_cout V293_ccounter V293_caop V293_cstack V293_ccritical getasrt].
 rewrite V293_sched_snapshot_roundtrip by exact B;reflexivity.
Qed.
Theorem DPchanged_nonempty : forall nest c old aop,nest<=1 ->
 CXstate nest c old aop|=DPpre(DPlg nest c aop).
Proof.
 intros nest c old aop N;rewrite DPpre_reduces by lia.
 pose proof(CBpre_owned nest c old aop N)as Held.
 unfold CBpre in Held;clear -Held;sep auto.
Qed.
Lemma DPcounter_load : forall nest c aop st,nest<256 ->
 st|=DPpre(DPlg nest c aop) ->
 load Tint32(getmem st)(12%positive,0%Z)=Some(Vint32 c).
Proof.
 intros nest c aop st B Held;rewrite DPpre_reduces in Held by exact B.
 assert(P:st|=PV(12%positive,Int.zero)@Tint32|->Vint32 c ** Atrue).
 { unfold CBfp,V293_changed_builder_fpre,V293_changed_builder_pre,
   V293_changed_builder_external,V293_changed_builder_memory in Held;
   cbn[getasrt]in Held;clear -Held;sep auto. }
 eapply V293_star_load_l;[ |exact P];intros s[M _];eapply mapstoval_load;[reflexivity|exact M].
Qed.
Theorem DPcounter_dynamic_control : forall old,
 V293_changed_decode(V293_changed_encode(DPsnapshot 1 Int.one(spec_done None)))=
 Some(DPsnapshot 1 Int.one(spec_done None)) /\
 V293_changed_decode(V293_changed_encode(DPsnapshot 1(Int.repr Int.max_unsigned)(spec_done None)))=
 Some(DPsnapshot 1(Int.repr Int.max_unsigned)(spec_done None)) /\
 (CXstate 1 Int.one old(spec_done None)|=DPpre(DPlg 1 Int.one(spec_done None))) /\
 (CXstate 1(Int.repr Int.max_unsigned)old(spec_done None)|=
 DPpre(DPlg 1(Int.repr Int.max_unsigned)(spec_done None))) /\
 ~(CXstate 1(Int.repr Int.max_unsigned)old(spec_done None)|=DPpre(DPlg 1 Int.one(spec_done None))).
Proof.
 intro old;split;[apply V293_changed_codec_roundtrip| ];split;[apply V293_changed_codec_roundtrip| ].
 split;[apply DPchanged_nonempty;lia| ];split;[apply DPchanged_nonempty;lia| ].
 intro Wrong;pose proof(DPcounter_load 1 Int.one(spec_done None)_ ltac:(lia)Wrong)as W.
 pose proof(DPcounter_load 1(Int.repr Int.max_unsigned)(spec_done None)_ ltac:(lia)
 (DPchanged_nonempty 1(Int.repr Int.max_unsigned)old(spec_done None)ltac:(lia)))as A.
 rewrite A in W;vm_compute in W;discriminate.
Qed.
Lemma DPmalformed : forall t,
 V293_changed_decode nil=None /\
 getasrt(DPfp nil(logic_ie true::nil)t)=Afalse /\
 getasrt(DPfq nil None(logic_ie true::nil)t)=Afalse.
Proof. intro;repeat split;reflexivity. Qed.
Definition DQfp:=V293_dynamic_exit_fpre 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 112%Z 108%Z 109%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 13%positive 14%positive
 16%positive 11%positive 12%positive Tvoid(length(V293_current_mode_entries true))nil Atrue I.
Definition DQpre lg:=V293_exit_builder_cells 120%Z **
 getasrt(DQfp nil(logic_ie false::lg)V293_idle_tid) ** V293_exit_builder_domain 120%Z.
Theorem DQquiet_nonempty : forall enabled,
 UBstate enabled 1 2 0|=DQpre(UBlogic enabled 1 2 0).
Proof. intro;change(UBstate enabled 1 2 0|=UBpre(UBlogic enabled 1 2 0)V293_idle_tid);apply UBquiet_pre_nonempty;lia. Qed.
Theorem DQsame_nonempty : forall enabled,
 QPstate enabled(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one)|=
 DQpre(V293_exit_same_args(BIlogic enabled)).
Proof. intro;change(QPstate enabled(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one)|=
 UBpre(V293_exit_same_args(BIlogic enabled))V293_idle_tid);apply UBsame_pre_nonempty. Qed.
