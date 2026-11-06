Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameInternal.
Require Import CertiOS.audit.probes.V293OSIntExitResourceCodecProbe.
Require Import CertiOS.audit.probes.V293OSIntExitBuildersProbe.
Require Import CertiOS.audit.probes.V293OSSchedISRContextProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCriticalCalls.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedGuardsWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedISRExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactPrefix.
Require Import CertiOS.audit.probes.V293InterruptReadyEnvironmentProbe.
Require Import CertiOS.audit.probes.V293InterruptReadyLocalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedAllExactJoint.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.audit.probes.V293OSIntExitSameInternalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptExitEnvironment.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.audit.probes.V293InterruptBindingsProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitLocalDispatch.
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
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.audit.probes.V293OSIntExitLocalDispatchProbe.
Require Import CertiOS.audit.probes.V293OSIntExitExactProbe.
Require Import CertiOS.audit.probes.V293OSIntExitExactInternalProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyDynamicProbe.
Require Import CertiOS.audit.probes.V293OSIntExitBoundInternalProbe.
Require Import CertiOS.audit.probes.V293OSIntExitQuietExactProbe.
Require Import CertiOS.audit.probes.V293OSIntExitSameExactDynamicProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitAllExactDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitQuietExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameExactInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceCodec.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitLocalDispatch.
Definition BDfp:=V293_bound_dynamic_fpre
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil Aemp I.
Definition BDfq:=V293_bound_dynamic_fpost
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil Aemp I.
Definition BDspec:=V293_bound_dynamic_spec
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil Aemp I 300%Z 301%Z 200%Z.
Definition SDfp:=V293_bound_dynamic_fpre
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 112%Z 108%Z 109%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 13%positive 14%positive
 16%positive 11%positive 12%positive nil Aemp I.
Definition SDfq:=V293_bound_dynamic_fpost
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 112%Z 108%Z 109%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 13%positive 14%positive
 16%positive 11%positive 12%positive nil Aemp I.
Definition SDspec:=V293_bound_dynamic_spec
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 112%Z 108%Z 109%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 13%positive 14%positive
 16%positive 11%positive 12%positive nil Aemp I 300%Z 301%Z 200%Z.
Definition BDpre lg:=V293_exit_builder_cells 120%Z **
 getasrt(BDfp nil lg OwnershipWaiting) ** V293_exit_builder_domain 120%Z.
Definition BDpost lg result:=V293_exit_builder_cells 120%Z **
 getasrt(BDfq nil result lg OwnershipWaiting) ** V293_exit_builder_domain 120%Z.
Lemma BDbuilders : forall lg,
 BuildPreI RDprogram 300%Z nil lg BDfp OwnershipWaiting=Some(BDpre lg) /\
 BuildRetI RDprogram 300%Z nil lg BDfq OwnershipWaiting=Some(BDpost lg).
Proof. intros;split;reflexivity. Qed.
Theorem BDenvironment : WFFunEnv RDprogram BDspec V293_scheduler LDli RDinv /\
 WFIFun RDprogram BDspec V293_scheduler RDinv LDli.
Proof. split;unfold RDprogram,BDspec,RDinv,JBcells;
 [apply V293_bound_dynamic_WFFunEnv|apply V293_bound_dynamic_WFIFun];try discriminate;exact I. Qed.
Theorem BDactual_contract : forall lg,
 InfRules BDspec V293_scheduler LDli RDinv(BDpost lg)Afalse(BDpre lg)
 (V293_exit_boundary_body 112%Z 110%Z 111%Z 120%Z 105%Z 103%Z 106%Z 108%Z 109%Z 200%Z
 (V293_interrupt_handoff 103%Z 108%Z 106%Z))Afalse OwnershipWaiting.
Proof.
 intros;eapply V293_OSIntExit_bound_dynamic_contract with
 (P:=RDprogram)(f:=300%Z)(vl:=nil)(lg:=lg)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(bo:=93%positive)(rest:=nil)(extra:=Aemp)(EG:=I);
 try discriminate;try exact I;reflexivity.
Qed.
Theorem BDactual_call : forall lg RI r ri,
 InfRules BDspec V293_scheduler LDli RI r ri
 (getasrt(BDfp nil lg OwnershipWaiting) ** BIcallerframe)
 (scall 300%Z nil)(EX result:option val,getasrt(BDfq nil result lg OwnershipWaiting) ** BIcallerframe)OwnershipWaiting.
Proof.
 intros;unfold BDfp,BDfq;apply V293_OSIntExit_bound_dynamic_call with(EG:=I).
 - unfold BIcallerframe,V293_exit_builder_cells,V293_exit_builder_domain,Alvarmapsto,
 Alvarenv',Aptrmapsto;cbn[GoodFrm];tauto.
 - reflexivity.
Qed.
Lemma BDchanged_literal : forall nest c aop ci,nest<256 ->
 BDpre(RDlg nest c aop ci)=RBpre 120%Z nest c aop ci /\
 (forall result,BDpost(RDlg nest c aop ci)result=
 V293OSIntExitBoundInternalProbe.BIret aop ci result).
Proof.
 intros nest c aop ci N;split.
 - change(RDpre(RDlg nest c aop ci)=RBpre 120%Z nest c aop ci);apply RDpre_reduces;exact N.
 - intro result;unfold BDpost,BDfq,RDlg,V293_bound_dynamic_fpost,V293_exit_path,
 V293_bound_dynamic_changed_fpost;rewrite V293_changed_codec_roundtrip;reflexivity.
Qed.
Theorem BDchanged_nonempty : forall nest c old ci aop,nest<=1 ->
 JBstate(JBmemory nest c old)ci(sched;;aop)|=BDpre(RDlg nest c aop ci).
Proof. intros;rewrite(proj1(BDchanged_literal nest c aop ci ltac:(lia)));apply RBpre_owned;assumption. Qed.
Definition BDqexternal nest:=<||spec_done None||> ** OS[(fun _:hid=>false),false,nil,nil] **
 (V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive **
 (Amapsto(99%positive,0%Z)Tint8 false(V293_byteval 1) **
 V293_rdy_raw_cells(V293_exit_cells 96%positive 97%positive nest 0)
 (p_local LDli OwnershipWaiting nil ** Aemp))).
Lemma BDquiet_literal :
 getasrt(BDfp nil Qlg OwnershipWaiting)=[|V293_quiet_exit_valid 1 2 0 nil|] ** BDqexternal 2 /\
 (forall result,getasrt(BDfq nil result Qlg OwnershipWaiting)=[|result=None|] ** BDqexternal 1).
Proof. split;[ |intro result];reflexivity. Qed.
Lemma BDquiet_strengthen : Qpre ==>BDpre Qlg.
Proof.
 intros st H;unfold Qpre in H;rewrite(proj1 Qliteral)in H.
 unfold BDpre;rewrite(proj1 BDquiet_literal).
 assert(Names:st |=V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive ** Atrue)
 by(unfold Qexternal in H;clear -H;sep auto).
 pose proof(V293_bound_dispatch_add_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive _ st Names H)as T.
 unfold BDqexternal,Qexternal,V293_exit_cells,V293_interrupt_cells in *;cbn[V293_rdy_raw_cells]in *.
 unfold p_local,LINV,LDli,V293_irq_bound_li,V293_shared_li in *.
 clear -T;sep auto;apply V293_irq_bound_good.
Qed.
Theorem BDquiet_nonempty : Qstate Qmemory |=BDpre Qlg.
Proof. apply BDquiet_strengthen;apply Qentry_nonempty. Qed.
(* Only the local return conjunct is weakened; the program and all cells stay fixed. *)
Lemma BDquiet_return_forget : forall nest,BDqexternal nest ==>Qexternal nest.
Proof.
 intro nest;unfold BDqexternal,Qexternal,V293_exit_cells,V293_interrupt_cells;
 cbn[V293_rdy_raw_cells];repeat first[solve[intros s H;exact H]|
 solve[apply V293_bound_dispatch_forget]|apply astar_mono].
Qed.
Definition SDli:=V293_irq_bound_li 112%Z 108%Z 109%Z 16%positive 11%positive 12%positive.
Definition SDpre enabled:=V293_exit_builder_cells 120%Z **
 getasrt(SDfp nil(SElg enabled)V293_idle_tid) ** V293_exit_builder_domain 120%Z.
Definition SDpost enabled result:=V293_exit_builder_cells 120%Z **
 getasrt(SDfq nil result(SElg enabled)V293_idle_tid) ** V293_exit_builder_domain 120%Z.
Definition SDexternal enabled nest hv out := V293_same_exact_exit_external
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 108%Z 109%Z 112%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive
 13%positive 14%positive 11%positive 12%positive 16%positive V293_tcb_type SDli Aemp
 enabled(fun _=>false)(cons 0 nil)(cons false nil)0 16 V293_idle_entries V293_idle_tasks
 12 nest hv out Int.one(spec_done None)V293_idle_tid.
Lemma SDliteral : forall enabled,
 getasrt(SDfp nil(SElg enabled)V293_idle_tid)=
 [|V293_same_exit_valid(cons 0 nil)(RCsnapshot 12 1 Int.one)|] **
 (EX hv:val,SDexternal enabled 1 hv Vnull) /\
 (forall result,getasrt(SDfq nil result(SElg enabled)V293_idle_tid)=
 [|result=None|] **
 (EX selected:Modules.tid,[|V293_highest_ready V293_idle_tasks selected|] **
 SDexternal enabled 0(V293_byteval(V293_ready_select 0 16(V293_ready_group 0 16)))(Vptr selected))).
Proof.
 intro enabled;split;[ |intro result];unfold SDfp,SDfq,SElg,
 V293_bound_dynamic_fpre,V293_bound_dynamic_fpost,V293_exit_path,
 V293_same_exact_exit_fpre,V293_same_exact_exit_fpost,getasrt,
 V293_same_exact_exit_pre,V293_same_exact_exit_post;
 rewrite BIdecode;reflexivity.
Qed.
Lemma SDbuilders : forall enabled,
 BuildPreI SEprogram 300%Z nil(SElg enabled)SDfp V293_idle_tid=Some(SDpre enabled) /\
 BuildRetI SEprogram 300%Z nil(SElg enabled)SDfq V293_idle_tid=Some(SDpost enabled).
Proof. intro;split;reflexivity. Qed.
Theorem SDenvironment : WFFunEnv SEprogram SDspec V293_scheduler SDli SEinv /\
 WFIFun SEprogram SDspec V293_scheduler SEinv SDli.
Proof. split;unfold SEprogram,SDspec;
 [apply V293_bound_dynamic_WFFunEnv|apply V293_bound_dynamic_WFIFun];try discriminate;exact I. Qed.
Theorem SDactual_contract : forall enabled,
 InfRules SDspec V293_scheduler SDli SEinv(SDpost enabled) Afalse(SDpre enabled)
 (V293_exit_boundary_body 112%Z 108%Z 109%Z 120%Z 106%Z 103%Z 107%Z 110%Z 111%Z
 200%Z(V293_interrupt_handoff 103%Z 110%Z 107%Z)) Afalse V293_idle_tid.
Proof.
 intro enabled.
 eapply(V293_OSIntExit_bound_dynamic_contract
 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 112%Z 108%Z 109%Z 120%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive
 13%positive 14%positive 16%positive 11%positive 12%positive nil Aemp I
 SEprogram 300%Z SDspec 200%Z nil(SElg enabled)V293_idle_tid(SDpre enabled)(SDpost enabled));
 try discriminate;try reflexivity;exact I.
Qed.
Theorem SDactual_call : forall enabled RI r ri,
 InfRules SDspec V293_scheduler SDli RI r ri
 (getasrt(SDfp nil(SElg enabled)V293_idle_tid) ** BIcallerframe)
 (scall 300%Z nil)
 (EX result:option val,getasrt(SDfq nil result(SElg enabled)V293_idle_tid) ** BIcallerframe)V293_idle_tid.
Proof.
 intros;unfold SDfp,SDfq;apply V293_OSIntExit_bound_dynamic_call with(EG:=I).
 - unfold BIcallerframe,V293_exit_builder_cells,V293_exit_builder_domain,Alvarmapsto,
 Alvarenv',Aptrmapsto;cbn[GoodFrm];tauto.
 - reflexivity.
Qed.
Lemma SDstrengthen : forall enabled,SEbuilderpre enabled ==>SDpre enabled.
Proof.
 intros enabled st H;unfold SEbuilderpre in H;rewrite(proj1(SEliteral enabled))in H.
 unfold SDpre;rewrite(proj1(SDliteral enabled)).
 assert(Names:st |=SEglobals ** Atrue)
 by(unfold SEexternal,V293_same_exact_exit_external in H;clear -H;sep auto).
 assert(Globals:st |=V293_quiet_globals 112%Z 108%Z 109%Z 16%positive 11%positive 12%positive ** Atrue).
 { eapply astar_mono;[ |intros s G;exact G|exact Names].
   intros s G;unfold SEglobals,V293_exit_builder_globals in G.
   destruct G as[_[_[_[_[GN[GL GR]]]]]].
   unfold V293_quiet_globals;split;[exact GR|split;assumption]. }
 pose proof(V293_bound_dispatch_add_globals 112%Z 108%Z 109%Z 16%positive 11%positive 12%positive _ st Globals H)as T.
 unfold SDexternal,SEexternal,V293_same_exact_exit_external,V293_same_exact_exit_memory in *.
 unfold p_local,LINV,SDli,V293_irq_bound_li,V293_shared_li in *.
 clear -T;sep auto;apply V293_irq_bound_good.
Qed.
Theorem SDnonempty : forall enabled,
 SEstate enabled(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one) |=SDpre enabled.
Proof. intro;apply SDstrengthen;apply SEentry_nonempty. Qed.
Lemma SDreturn_forget : forall enabled nest hv out,SDexternal enabled nest hv out ==>SEexternal enabled nest hv out.
Proof.
 intros enabled nest hv out;
 unfold SDexternal,SEexternal,V293_same_exact_exit_external,V293_same_exact_exit_memory;
 repeat first[solve[intros s H;exact H]|
 solve[apply V293_bound_dispatch_forget]|apply astar_mono].
Qed.
Theorem BDcall_nonempty :
 (forall nest c old ci aop,nest<=1 ->JBstate(JBmemory nest c old)ci(sched;;aop)|=
 getasrt(BDfp nil(RDlg nest c aop ci)OwnershipWaiting) ** BIcallerframe) /\
 (Qstate Qmemory |=getasrt(BDfp nil Qlg OwnershipWaiting) ** BIcallerframe) /\
 (forall enabled,SEstate enabled(cons 0 nil)(cons false nil)1 Int.one(Vint32 Int.one)|=
 getasrt(SDfp nil(SElg enabled)V293_idle_tid) ** BIcallerframe).
Proof.
 split.
 - intros;pose proof(BDchanged_nonempty nest c old ci aop H)as T;unfold BDpre,BIcallerframe in *;clear -T;sep auto.
 - split.
   + pose proof BDquiet_nonempty as T;unfold BDpre,BIcallerframe in *;clear -T;sep auto.
   + intros;pose proof(SDnonempty enabled)as T;unfold SDpre,BIcallerframe in *;clear -T;sep auto.
Qed.
Lemma BDreturned_local : forall lg result,
 getasrt(BDfq nil result lg OwnershipWaiting) ==>CurLINV LDli OwnershipWaiting.
Proof. intros lg result;exact(V293_bound_dynamic_post_local 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil Aemp I nil result lg OwnershipWaiting). Qed.
Lemma SDreturned_local : forall enabled result,
 getasrt(SDfq nil result(SElg enabled)V293_idle_tid) ==>CurLINV SDli V293_idle_tid.
Proof. intros enabled result;exact(V293_bound_dynamic_post_local 100%Z 101%Z 102%Z 103%Z 106%Z 107%Z 110%Z 111%Z 112%Z 108%Z 109%Z
 1%positive 2%positive 3%positive 4%positive 8%positive 10%positive 13%positive 14%positive
 16%positive 11%positive 12%positive nil Aemp I nil result(SElg enabled)V293_idle_tid). Qed.
Theorem BDinvalid_paths : forall vl t result,
 Forall(fun lg=>getasrt(BDfp vl lg t)=Afalse /\ getasrt(BDfq vl result lg t)=Afalse)
 [nil;[logic_ie true];[logic_ie false];[logic_ie false;logic_ie true];[logic_ie false;logic_ie false]].
Proof. intros;repeat constructor. Qed.
Theorem BDreject_arguments : forall v vl lg,
 BuildPreI RDprogram 300%Z(v::vl)lg BDfp OwnershipWaiting=None.
Proof.
 intros;assert(E:dl_vl_match dnil(rev(v::vl))=false).
 { destruct(rev(v::vl))eqn:Rev;[ |reflexivity].
   apply(f_equal(@rev val))in Rev;rewrite rev_involutive in Rev;discriminate. }
 assert(Code:RDprogram 300%Z=Some(V293_exit_boundary_function
 112%Z 110%Z 111%Z 120%Z 105%Z 103%Z 106%Z 108%Z 109%Z 200%Z
 (V293_interrupt_handoff 103%Z 108%Z 106%Z)))by reflexivity.
 unfold BuildPreI;rewrite Code;unfold V293_exit_boundary_function;rewrite E;reflexivity.
Qed.
Lemma BDruntime_control : BIprogram=RDprogram /\
 RDprogram 300%Z=XIprogram 300%Z /\ RDprogram 200%Z=XEprogram 200%Z.
Proof. repeat split;reflexivity. Qed.
