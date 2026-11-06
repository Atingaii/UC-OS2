(* Physical current-highest quiet entries; shared dispatch environment. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.audit.probes.V293InterruptReadyEnvironmentProbe.
(* A typed physical fixture for the same full ready/TCB/storage invariant. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterOpenExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitAllExactDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyLocal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHandoffHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnter.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.audit.probes.V293OSIntExitReadyDynamicProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.tactics.basetac.join_general.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Require Import CertiOS.audit.probes.V293InterruptQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyInternalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptChangedContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBuilders.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSameContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSameInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResourceCodec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefixWitness.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPrefix.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietSched.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBoundEntry.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBoundQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptCommonDispatch.
Require Import CertiOS.audit.probes.V293InterruptSameContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptCommonDispatchProbe.
Require Import CertiOS.audit.probes.V293InterruptBoundDispatchContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptBoundQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptQuietBuilderProbe.
Require Import CertiOS.audit.probes.V293OSIntExitBoundDynamicProbe.
Require Import CertiOS.audit.probes.V293OSIntExitLocalDispatchProbe.
Definition QSraw (nest:nat):=
 GV OSTCBCur@(Tptr V293_tcb_type)|->Vptr OwnershipReady **
 (SCkept **
 (V293_same_irq_read_full 92%positive 81%positive 80%positive 82%positive 94%positive 99%positive 16 0 4 RTentries **
 (Amapsto(96%positive,0%Z)Tint8 true(V293_byteval nest) **
 Amapsto(97%positive,0%Z)Tint8 true(V293_byteval 0)))).
Definition QSentry (nest:nat):=V293_same_irq_snapshot
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 16 0 4 RTentries OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipReady)Int.zero nest(sched;;spec_done None)
 (isrupd(fun _:hid=>false)0 true)[0]OwnershipReady.
Definition QSstate M O:RstateOP:=(JBge,emp,M,isrupd(fun _:hid=>false)0 true,
 (false,[0],nil),O,sched;;spec_done None).
Lemma QSraw_good : forall nest, GoodInvAsrt (QSraw nest) /\ GoodFrm (QSraw nest).
Proof.
 intro nest;assert(A:GoodInvAsrt(V293_array true 82%positive 0 4(Tptr V293_tcb_type)RTentries)).
 { unfold RTentries;cbn[V293_array GoodInvAsrt];tauto. }
 assert(F:GoodFrm(V293_array true 82%positive 0 4(Tptr V293_tcb_type)RTentries))by(apply V293_array_good).
 assert(O:GoodInvAsrt(V293_owned_task_records OwnershipTasks)).
 { unfold V293_owned_task_records;apply V293_task_list_good. }
 assert(OF:GoodFrm(V293_owned_task_records OwnershipTasks))by(apply V293_owned_tasks_frame).
 unfold QSraw,SCkept,RBglobals,V293_same_irq_read_full,V293_prefix_output,
 V293_shared_fields,V293_inputs_full,V293_exit_builder_globals,V293_sched_globals,
 Agvarmapsto,Agvarenv',Aptrmapsto.
 split;[cbn[GoodInvAsrt]|cbn[GoodFrm]];repeat split;try exact Logic.I;assumption.
Qed.
Lemma QSraw_heap : forall nest,nest<256 -> SCstate(SCmemory nest Int.zero Int.zero)nil(sched;;spec_done None)|=(QSraw nest) ** Atrue.
Proof.
 intros nest Bound;pose proof(SCheap_data nest Int.zero Int.zero nil(sched;;spec_done None)Bound)as Entry.
 assert(H:SCstate(SCmemory nest Int.zero Int.zero)nil(sched;;spec_done None)|=RBglobals **
 (<||sched;;spec_done None||> ** OS[(fun _:hid=>false),false,nil,nil] ** SCdata nest Int.zero Int.zero)).
 { unfold SCstate;eapply JBstar with(m1:=emp)(o1:=emp).
   - apply map_join_comm;apply map_join_emp.
   - apply map_join_comm;apply map_join_emp.
   - apply RBglobals_owned.
   - exact Entry. }
 unfold QSraw,SCkept,SCdata,RBglobals,V293_exit_ready_body_data,V293_exit_ready_body_core,
 V293_handoff_byte,V293_counter_cell,V293_time_cell,V293_time_binding,
 V293_exit_ready_body_bindings,V293_exit_builder_globals,V293_prefix_bindings,
 V293_prefix_output,V293_handoff_binding,V293_counter_bindings,Agvarmapsto,Agvarenv',Aptrmapsto,
 V293OSIntExitHoare.V293_exit_cells,V293OSIntEnterInternal.V293_interrupt_cells,
 V293_same_irq_read_full in *;cbn[V293_rdy_raw_cells addrval_to_addr]in *.
 clear Entry;sep normal in H;destruct H as[bcur[btarget H]].
 assert(bcur=1%positive /\ btarget=93%positive).
 { assert(B:SCstate(SCmemory nest Int.zero Int.zero)nil(sched;;spec_done None)|=
   Agvarenv OSTCBCur(Tptr V293_tcb_type)(bcur,0%Z) **
   (Agvarenv 106%Z(Tptr V293_tcb_type)(btarget,0%Z) ** Atrue)).
   { rewrite Int.unsigned_zero in H;sep auto. }
   apply astar_l_agvarenv_elim in B;destruct B as[BC B].
   apply astar_l_agvarenv_elim in B;destruct B as[BT B].
   vm_compute in BC,BT;destruct BC as[_ BC];destruct BT as[_ BT];split;congruence. }
 destruct H0;subst;sep auto.

Qed.
Theorem QSentry_nonempty : forall nest,nest<256 -> exists M Mf O Of,
 join M Mf(SCmemory nest Int.zero Int.zero) /\ join O Of(RIabstract OwnershipReady) /\
 QSstate M O|=(QSentry nest).
Proof.
 intros nest Bound;pose proof(QSraw_heap nest Bound)as H;unfold SCstate in H.
 assert(Moved:(JBge,emp,SCmemory nest Int.zero Int.zero,(fun _:hid=>false),
 (false,nil,nil),RIabstract OwnershipReady,sched;;spec_done None)|=(QSraw nest) ** Atrue).
 { eapply good_inv_prop;[split;[exact(proj1(QSraw_good nest))|exact Logic.I]|exact H]. }
 assert(New:QSstate(SCmemory nest Int.zero Int.zero)(RIabstract OwnershipReady)|=(QSraw nest) ** Atrue).
 { unfold QSstate;eapply goodfrm_prop;[split;[exact(proj2(QSraw_good nest))|exact Logic.I]|exact Moved]. }
 apply sat_split in New;destruct New as(M&Mf&O&Of&JM&JO&Owned&Extra).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ].
 unfold QSraw in Owned;eapply astar_mono in Owned;[ |apply GV_separate_rw|intros s K;exact K].
 apply astar_l_adomlenv_intro with(d:=nil)in Owned.
 2:{ intros x tau;split;[contradiction|intros[l E];discriminate]. }
 apply astar_l_aisr_intro with(i:=isrupd(fun _:hid=>false)0 true)in Owned;[ |reflexivity].
 apply astar_l_aie_intro with(i:=false)in Owned;[ |reflexivity].
 apply astar_l_ais_intro with(i:=[0])in Owned;[ |reflexivity].
 apply astar_l_acs_intro with(i:=nil)in Owned;[ |reflexivity].
 apply astar_l_aop'_intro with(aop:=sched;;spec_done None)in Owned;[ |reflexivity].
 unfold QSentry,V293_same_irq_snapshot,V293_same_irq_physical,V293_same_irq_payload,
 SCkept,p_local,LINV,V293_shared_li,CurTid in *;clear H Moved Extra;sep auto;
 apply V293_switch_li_good.
Qed.
Definition QSsnapshot nest:=BQsnapshot 1 nest 0(sched;;spec_done None)false
 (isrupd(fun _:hid=>false)0 true)[0]nil OwnershipReady.
Definition QSpre:=(CDpre //\\ QJfilter) //\\ V293_irq_sched_self_guard.
Lemma QSentry_snapshot : forall nest,QSentry nest ==>QSsnapshot nest.
Proof.
 intros nest st H;unfold QSsnapshot,BQsnapshot.
 apply V293_irq_bound_snapshot_pack.
 apply(V293_same_entry_kept 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil 16 0 4 RTentries OwnershipTasks emp Int.zero
 (V293_byteval 88)(Vptr OwnershipReady)Int.zero nest(sched;;spec_done None)
 (isrupd(fun _:hid=>false)0 true)[0]OwnershipReady);try exact H;try reflexivity;try lia.
 - exact RTliteral_rel.
 - vm_compute;repeat constructor.
Qed.
Lemma QSentry_guard : forall nest,QSentry nest ==>V293_irq_sched_self_guard.
Proof.
 intros nest st H;apply V293_irq_sched_self_guard_complete.
 unfold QSentry,V293_same_irq_snapshot in H.
 apply astar_l_aop'_elim in H;destruct H as[_ H].
 eapply V293_same_resources_sched;[exact RTliteral_rel|exact CDcurrent|reflexivity|exact H].
Qed.
Lemma QSentry_pre : forall nest,1<=nest ->nest<256 ->QSentry nest ==>QSpre.
Proof.
 intros nest Positive Bound st H;pose proof(QSentry_snapshot nest st H)as S.
 unfold QSpre;split;[split|apply QSentry_guard with(nest:=nest);exact H].
 - unfold CDpre;unfold QSsnapshot,BQsnapshot in S.
   apply(V293_bound_outer_snapshot_pre 106%Z 112%Z 110%Z 111%Z
    92%positive 81%positive 80%positive 91%positive 82%positive 94%positive 95%positive
    99%positive 96%positive 97%positive nil 1 nest 0(sched;;spec_done None)
    (fun _:hid=>false)nil OwnershipReady);try lia;exact S.
 - unfold QJfilter,V293_irq_quiet_filter;exists 1;exists nest;exists 0.
   apply astar_l_apure_intro;[ |repeat split;lia].
   unfold QSsnapshot,BQsnapshot in S;apply V293_irq_bound_snapshot_controls in S;exact S.
Qed.
Theorem QSfiltered_nonempty : forall nest,1<=nest ->nest<256 ->exists M Mf O Of,
 join M Mf(SCmemory nest Int.zero Int.zero) /\join O Of(RIabstract OwnershipReady) /\
 QSstate M O|=QSpre.
Proof.
 intros nest Positive Bound;destruct(QSentry_nonempty nest Bound)as(M&Mf&O&Of&JM&JO&H).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ].
 apply QSentry_pre with(nest:=nest);assumption.
Qed.
Theorem QStyped_pair :
 (exists M Mf O Of,join M Mf(SCmemory 1 Int.zero Int.zero) /\join O Of(RIabstract OwnershipReady) /\QSstate M O|=QSpre) /\
 (exists M Mf O Of,join M Mf(SCmemory 255 Int.zero Int.zero) /\join O Of(RIabstract OwnershipReady) /\QSstate M O|=QSpre).
Proof. split;apply QSfiltered_nonempty;lia. Qed.
Theorem QSbuilders :
 Some CDpre=BuildintPre 0 BCintspec(fun _:hid=>false)nil RDinv LDli OwnershipReady nil /\
 Some BSret=BuildintRet 0 BCintspec(fun _:hid=>false)nil RDinv LDli OwnershipReady nil.
Proof. split;reflexivity. Qed.
Theorem QSactual_wrapper :
 InfRules BDspec V293_scheduler LDli RDinv arfalse BSret
 QSpre(V293_irq_source_wrapper 301%Z 300%Z Int.zero)Afalse OwnershipReady.
Proof.
 unfold QSpre,CDpre,QJfilter;apply(V293_interrupt_quiet_sched_builder
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil BDspec 301%Z 300%Z BCintspec 0(fun _:hid=>false)nil
 OwnershipReady nil CDpre BSret Int.zero);try reflexivity.
 unfold INUM;rewrite Int.unsigned_zero;cbn;lia.
Qed.
(* The same exact intspec, function environment, Inv and LI as dispatch. *)
Theorem QScommon_environment :
 GoodI RDinv V293_scheduler LDli /\WFFunEnv RDprogram BDspec V293_scheduler LDli RDinv /\
 WFIFun RDprogram BDspec V293_scheduler RDinv LDli.
Proof. exact CDenvironment. Qed.
Theorem QSnegative_nonempty : forall nest,1<=nest ->nest<256 ->exists M Mf O Of,
 join M Mf(JBmemory nest Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 QCstate M O|=QJpre /\~QCstate M O|=V293_irq_sched_self_guard.
Proof.
 intros nest Positive Bound;destruct(QJfiltered_nonempty nest Positive Bound)as(M&Mf&O&Of&JM&JO&E&P).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ];split;[exact P| ].
 intro Guard;apply V293_irq_sched_self_guard_sound in Guard.
 destruct Guard as[t[C[ts[T Highest]]]];apply(proj2 CDcurrent_ablation).
 exists t;split;[ |exists ts;split;[ |exact Highest]].
 - eapply OSAbstMod.join_get_l;[exact JO|exact C].
 - eapply OSAbstMod.join_get_l;[exact JO|exact T].
Qed.
(* Only this abstract no-op control changes curtid, not two physical runs. *)
Theorem QSguard_ablation : forall M,
 QSstate M(RIabstract OwnershipReady)|=V293_irq_sched_self_guard /\
 ~QSstate M(RIabstract OwnershipWaiting)|=V293_irq_sched_self_guard.
Proof.
 intro M;split.
 - apply V293_irq_sched_self_guard_complete;exact(proj1 CDcurrent_ablation).
 - intro G;apply V293_irq_sched_self_guard_sound in G;exact(proj2 CDcurrent_ablation G).
Qed.
Theorem QSabstract_current_only : forall key,key<>curtid ->
 get(RIabstract OwnershipReady)key=get(RIabstract OwnershipWaiting)key.
Proof. exact CDcurrent_only. Qed.
Theorem QSprecise_steps :
 spec_stepstar V293_scheduler(sched;;spec_done None)(RIabstract OwnershipReady)
 (spec_done None)(RIabstract OwnershipReady).
Proof. exact CDsame_abstract_steps. Qed.
