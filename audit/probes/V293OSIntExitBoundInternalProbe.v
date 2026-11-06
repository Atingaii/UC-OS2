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
Definition BIfq aop ci:=V293_bound_builder_fpost
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil aop nil ci Aemp I.
Definition BIprogram:=V293_ready_irq_unit
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z 120%Z
 300%Z 301%Z 200%Z 104%Z.
Definition BIspec nest c aop ci:=V293_bound_irq_spec
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive 16 0 6 nest RTentries nil OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipWaiting)c aop nil ci Aemp I 300%Z 301%Z 200%Z.
(* A literal return boundary; the caller does not own the callee's saved cell. *)
Definition BIpost aop ci(result:option val):=
 [|result=None|] ** (<||aop||> **
 ((SWINV(V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells) **
 p_local LDli OwnershipWaiting nil) **
 ((Ais nil ** Acs ci) **
 (V293_sched_globals 100%Z 101%Z 102%Z 103%Z 92%positive 81%positive 80%positive 91%positive **
 (RBglobals ** Aemp))))).
Definition BIret aop ci result:=V293_exit_builder_cells 120%Z **
 BIpost aop ci result ** V293_exit_builder_domain 120%Z.
Definition BIcallerframe:=V293_exit_builder_cells 120%Z ** V293_exit_builder_domain 120%Z.
Lemma BIpost_identity : forall aop ci result,
 getasrt(BIfq aop ci nil result nil OwnershipWaiting)=BIpost aop ci result.
Proof. intros;reflexivity. Qed.
Theorem BIbuilders : forall nest c aop ci,
 BuildPreI BIprogram 300%Z nil nil(RBfp nest c aop ci)OwnershipWaiting=Some(RBpre 120%Z nest c aop ci) /\
 BuildRetI BIprogram 300%Z nil nil(BIfq aop ci)OwnershipWaiting=Some(BIret aop ci).
Proof. intros;split;reflexivity. Qed.
Theorem BIentry_owned : forall nest c old ci aop,nest<=1 ->
 JBstate(JBmemory nest c old)ci(sched;;aop)|=RBpre 120%Z nest c aop ci.
Proof. intros;apply RBpre_owned;assumption. Qed.
Theorem BIcall_entry_owned : forall nest c old ci aop,nest<=1 ->
 JBstate(JBmemory nest c old)ci(sched;;aop)|=
 getasrt(RBfp nest c aop ci nil nil OwnershipWaiting) ** BIcallerframe.
Proof.
 intros;pose proof(BIentry_owned nest c old ci aop H)as Entry;
 unfold RBpre,BIcallerframe in *;clear -Entry;sep auto.
Qed.
Theorem BIenvironment : forall nest c aop ci,
 WFFunEnv BIprogram(BIspec nest c aop ci)V293_scheduler LDli
 (V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells).
Proof.
 intros;unfold BIprogram,BIspec,JBcells;
 apply V293_bound_irq_WFFunEnv;try discriminate;exact I.
Qed.
Theorem BIactual_contract : forall nest c aop ci,
 InfRules(BIspec nest c aop ci)V293_scheduler LDli
 (V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells)
 (BIret aop ci)Afalse(RBpre 120%Z nest c aop ci)
 (V293_exit_boundary_body 112%Z 110%Z 111%Z 120%Z 105%Z 103%Z 106%Z 108%Z 109%Z 200%Z
 (V293_interrupt_handoff 103%Z 108%Z 106%Z))Afalse OwnershipWaiting.
Proof.
 intros;eapply V293_OSIntExit_bound_builder_contract with
 (P:=BIprogram)(f:=300%Z)(vl:=nil)(lg:=nil)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)
 (bo:=93%positive)(lo:=16)(hi:=0)(nc:=6)(nest:=nest)
 (entries:=RTentries)(tasks:=OwnershipTasks)(events:=emp)(now:=Int.zero)
 (hv:=V293_byteval 88)(out:=Vptr OwnershipWaiting)(c:=c)(aop:=aop)
 (si:=nil)(ci:=ci)(extra:=Aemp)(EG:=I);
 try discriminate;try exact I;reflexivity.
Qed.
Theorem BIactual_call : forall nest c aop ci RI r ri,
 InfRules(BIspec nest c aop ci)V293_scheduler LDli RI r ri
 (getasrt(RBfp nest c aop ci nil nil OwnershipWaiting) ** BIcallerframe)
 (scall 300%Z nil)(EX result:option val,BIpost aop ci result ** BIcallerframe)OwnershipWaiting.
Proof.
 intros;change(InfRules(BIspec nest c aop ci)V293_scheduler LDli RI r ri
 (getasrt(RBfp nest c aop ci nil nil OwnershipWaiting) ** BIcallerframe)
 (scall 300%Z nil)(EX result:option val,getasrt(BIfq aop ci nil result nil OwnershipWaiting) ** BIcallerframe)OwnershipWaiting).
 unfold RBfp,BIfq;apply V293_OSIntExit_bound_call with(EG:=I).
 - unfold BIcallerframe,V293_exit_builder_cells,V293_exit_builder_domain,Alvarmapsto,
 Alvarenv',Aptrmapsto;cbn[GoodFrm];tauto.
 - reflexivity.
Qed.
Definition BIbodypost aop ci:=
 <||aop||> **
 ((SWINV(V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells) **
   p_local LDli OwnershipWaiting nil) **
 ((Ais nil ** Acs ci) **
 (V293_counter_bindings 109%Z 95%positive **
 ((V293_handoff_binding 103%Z 91%positive ** V293_handoff_binding 108%Z 94%positive) **
 ((V293_sched_globals 100%Z 101%Z 102%Z 103%Z 92%positive 81%positive 80%positive 91%positive **
   V293_prefix_bindings 105%Z 103%Z 106%Z V293_tcb_type 82%positive 93%positive) **
 ((V293_handoff_binding 110%Z 96%positive ** V293_handoff_binding 111%Z 97%positive) **
 (V293_handoff_binding 112%Z 99%positive **
 (V293_time_cell true 120%Z 98%positive(Vint32 Int.zero) ** Aemp)))))))).

Theorem BIactual_body : forall nest c old ci aop,nest<=1 ->
 InfRules (BIspec nest c aop ci) V293_scheduler LDli
 (V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells)
 (fun v=>[|v=None|] ** BIbodypost aop ci)Afalse
 (<||sched;;aop||> ** OS[(fun _:hid=>false),false,nil,ci] ** JBdata nest c old)
 (V293_exit_boundary_body 112%Z 110%Z 111%Z 120%Z 105%Z 103%Z 106%Z 108%Z 109%Z 200%Z
 (V293_interrupt_handoff 103%Z 108%Z 106%Z))Afalse OwnershipWaiting.
Proof.
 intros;unfold JBcells,BIbodypost,JBdata;apply V293_OSIntExit_bound_body;try lia.
 - exists 4;vm_compute;intuition lia.
 - vm_compute;discriminate.
 - exact(proj1(proj2(proj2(proj2 RTliteral_rel)))).
 - exact(proj2(proj2(proj2(proj2 RTliteral_rel)))).
 - vm_compute;repeat constructor.
 - exists(Int.repr 6,wait(os_stat_sem(72%positive,Int.repr 5))Int.one,Vptr(120%positive,Int.repr 7));vm_compute;reflexivity.
 - exact I.
 - reflexivity.
Qed.
Lemma BIsame_program : BIprogram=RDprogram.
Proof. reflexivity. Qed.
Lemma BIsame_local : LDli=EBli.
Proof. reflexivity. Qed.
Theorem BIinternal_environment : forall nest c aop ci,
 WFIFun BIprogram(BIspec nest c aop ci)V293_scheduler
 (V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells)LDli.
Proof.
 intros;unfold BIprogram,BIspec,JBcells;apply V293_bound_irq_WFIFun;try discriminate;exact I.
Qed.
Theorem BIreject_arguments : forall nest c aop ci v vl lg,
 BuildPreI BIprogram 300%Z(v::vl)lg(RBfp nest c aop ci)OwnershipWaiting=None.
Proof.
 intros;assert(E:dl_vl_match dnil(rev(v::vl))=false).
 { destruct(rev(v::vl))eqn:Rev;[ |reflexivity].
   apply(f_equal(@rev val))in Rev;rewrite rev_involutive in Rev;discriminate. }
 assert(Code:BIprogram 300%Z=Some(V293_exit_boundary_function
 112%Z 110%Z 111%Z 120%Z 105%Z 103%Z 106%Z 108%Z 109%Z 200%Z
 (V293_interrupt_handoff 103%Z 108%Z 106%Z)))by reflexivity.
 unfold BuildPreI;rewrite Code;unfold V293_exit_boundary_function.
 rewrite E;reflexivity.
Qed.
Theorem BIbody_nonempty : forall nest c old ci aop,nest<=1 ->
 exists s,(s|=<||sched;;aop||> ** OS[(fun _:hid=>false),false,nil,ci] ** JBdata nest c old) /\
 V293_highest_ready OwnershipTasks OwnershipReady /\ OwnershipReady<>OwnershipWaiting.
Proof. intros;apply JBentry_nonempty;assumption. Qed.
Lemma BIreturned_local : forall aop ci result,
 BIpost aop ci result ==>CurLINV LDli OwnershipWaiting.
Proof.
 intros aop ci result st H;unfold BIpost in H.
 eapply V293_star_CurLINV_r;[ |exact H].
 eapply V293_star_CurLINV_r;
 eapply V293_star_CurLINV_l;eapply V293_star_CurLINV_r;apply V293_exact_local_weakens.
Qed.
Lemma BIsame_exit_shared_control : BIprogram 300%Z=XIprogram 300%Z.
Proof. reflexivity. Qed.
Lemma BIsame_sched_shared_control : BIprogram 200%Z=XEprogram 200%Z.
Proof. reflexivity. Qed.
Lemma BIbody_post_forget : forall aop ci,BIbodypost aop ci ==>XEpost aop ci.
Proof.
 intros aop ci;unfold BIbodypost,XEpost.
 apply astar_mono;[intros s H;exact H| ].
 apply astar_mono;[ |intros s H;exact H].
 apply astar_mono;[intros s H;exact H|apply V293_bound_dispatch_forget].
Qed.
