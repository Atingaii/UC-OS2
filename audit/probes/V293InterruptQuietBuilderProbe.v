Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.audit.probes.V293InterruptBoundQuietContinuousProbe.
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
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBoundQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitLocalDispatch.
Require Import CertiOS.audit.probes.V293OSIntExitBoundDynamicProbe.
Require Import CertiOS.audit.probes.V293InterruptQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptEntryControlProbe.
Require Import CertiOS.audit.probes.V293OSIntExitLocalDispatchProbe.
Require Import CertiOS.audit.probes.V293OSIntExitExactInternalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Definition QJold (nest:nat):=V293_quiet_irq_snapshot
 106%Z 112%Z 110%Z 111%Z 92%positive 81%positive 80%positive 91%positive 82%positive
 94%positive 95%positive 99%positive 96%positive 97%positive nil
 1 nest 0(spec_done None)false(isrupd(fun _:hid=>false)0 true)[0]nil OwnershipWaiting.
Definition QJraw (nest:nat):=
 Amapsto(99%positive,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(96%positive,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(97%positive,0%Z)Tint8 true(V293_byteval 0) **
 (CurTid OwnershipWaiting ** QCkept))).
Lemma QJraw_good : forall nest, GoodInvAsrt(QJraw nest) /\ GoodFrm(QJraw nest).
Proof.
 intro nest;unfold QJraw;split.
 - split;[exact Logic.I| ];split;[exact Logic.I| ];split;[exact Logic.I| ];split.
   + unfold CurTid;intro tq;unfold Agvarmapsto,Agvarenv',Aptrmapsto;cbn[GoodInvAsrt];auto.
   + unfold QCkept,V293_quiet_irq_kept;split;[apply V293_ready_core_good| ];split.
     * unfold V293_dispatch_cell;intro v;cbn[GoodInvAsrt];split;[exact Logic.I| ];
     unfold Agvarmapsto,Agvarenv',Aptrmapsto;cbn[GoodInvAsrt];auto.
     * split;apply V293_storage_good.
 - split;[exact Logic.I| ];split;[exact Logic.I| ];split;[exact Logic.I| ];split.
   + unfold CurTid;intro tq;unfold Agvarmapsto,Agvarenv',Aptrmapsto;cbn[GoodFrm];auto.
   + apply V293_quiet_irq_kept_good.
Qed.
Lemma QJraw_heap : forall nest,nest<256 -> JBstate(JBmemory nest Int.zero Int.zero)nil(sched;;spec_done None)|=QJraw nest ** Atrue.
Proof.
 intros nest Bound;pose proof(JBentry nest Int.zero Int.zero nil(spec_done None)Bound)as Entry.
 assert(Pack:JBstate(JBmemory nest Int.zero Int.zero)nil(sched;;spec_done None)|=
 (V293_inputs_full 92%positive 81%positive 80%positive 16 0 **
 (V293_array true 82%positive 0 4(Tptr V293_tcb_type)RTentries **
 (V293_owned_task_records OwnershipTasks ** V293_storage nil))) **
 ((GV OSTCBCur@(Tptr V293_tcb_type)|->Vptr OwnershipWaiting) **
 (V293_shared_fields OwnershipWaiting OwnershipTasks(emp:EcbMod.map)Int.zero **
 ((GV 106%Z@(Tptr V293_tcb_type)|->Vptr OwnershipWaiting) **
 (PV(91%positive,Int.zero)@Tint8|->V293_byteval 88 **
 (Amapsto(94%positive,0%Z)Tint8 true(V293_byteval 6) **
 (PV(95%positive,Int.zero)@Tint32|->Vint32 Int.zero **
 (Amapsto(99%positive,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(96%positive,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(97%positive,0%Z)Tint8 true(V293_byteval 0) ** Atrue)))))))))).
 { unfold JBdata,V293_exit_ready_body_data,V293_exit_ready_body_core,
 V293_handoff_byte,V293_counter_cell,V293_time_cell,V293_exit_cells,V293_interrupt_cells in Entry;
 cbn[V293_rdy_raw_cells V293_storage]in *;sep auto. }
 eapply astar_mono in Pack;[ |apply V293_retained_arrays_ready;[exact RTliteral_rel|vm_compute;repeat constructor]|intros s H;exact H].
 assert(Storage:JBstate(JBmemory nest Int.zero Int.zero)nil(sched;;spec_done None)|=
 V293_storage REprefix **
 ((GV OSTCBCur@(Tptr V293_tcb_type)|->Vptr OwnershipWaiting) **
 (V293_shared_fields OwnershipWaiting OwnershipTasks(emp:EcbMod.map)Int.zero **
 ((GV 106%Z@(Tptr V293_tcb_type)|->Vptr OwnershipWaiting) **
 (V293_ready_payload 80%positive 81%positive 82%positive OwnershipTasks **
 (Amapsto(99%positive,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(96%positive,0%Z)Tint8 true(V293_byteval nest) **
 (Amapsto(97%positive,0%Z)Tint8 true(V293_byteval 0) ** Atrue)))))))).
 { unfold REprefix,V293_ready_irq_prefix;cbn[V293_storage];unfold V293_storage_cell;
 clear Entry;sep auto;try(apply V293_byte_type;lia). }
 eapply astar_mono in Storage;[ |intros s H;exact H|apply astar_mono;[apply GV_separate_rw|intros s H;exact H]].
 unfold QJraw,QCkept,V293_quiet_irq_kept,V293ReadyTaskInvariant.V293_ready_core,V293_shared_ready_records,
 V293_dispatch_cell,CurTid;cbn[V293_storage];clear Entry Pack;sep auto.
 all:reflexivity.
Qed.
Theorem QJentry_nonempty : forall nest,nest<256 -> exists M Mf O Of,
 join M Mf(JBmemory nest Int.zero Int.zero) /\ join O Of(RIabstract OwnershipWaiting) /\
 QCstate M O|=QJold nest.
Proof.
 intros nest Bound;pose proof(QJraw_heap nest Bound)as H;unfold JBstate in H.
 assert(Moved:(JBge,emp,JBmemory nest Int.zero Int.zero,(fun _:hid=>false),
 (false,nil,nil),RIabstract OwnershipWaiting,spec_done None)|=QJraw nest ** Atrue).
 { eapply good_inv_prop;[split;[exact(proj1(QJraw_good nest))|exact Logic.I]|exact H]. }
 assert(New:QCstate(JBmemory nest Int.zero Int.zero)(RIabstract OwnershipWaiting)|=QJraw nest ** Atrue).
 { unfold QCstate;eapply goodfrm_prop;[split;[exact(proj2(QJraw_good nest))|exact Logic.I]|exact Moved]. }
 apply sat_split in New;destruct New as(M&Mf&O&Of&JM&JO&Owned&Extra).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ].
 assert(G:(JBge,emp,empmem,isrupd(fun _:hid=>false)0 true,(false,[0],nil),empabst,spec_done None)|=
 V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive).
 { unfold V293_quiet_globals;repeat split;apply agvarenv_intro;
 split;reflexivity. }
 assert(Pack:QCstate M O|=V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive ** QJraw nest).
 { unfold QCstate;apply sat_split';exists empmem;exists M;exists empabst;exists O.
 split;[apply join_emp| ];split;[apply join_emp| ];split;assumption. }
 apply astar_l_adomlenv_intro with(d:=nil)in Pack.
 2:{ intros x tau;split;[contradiction|intros[l E];discriminate]. }
 apply astar_l_aisr_intro with(i:=isrupd(fun _:hid=>false)0 true)in Pack;[ |reflexivity].
 apply astar_l_aie_intro with(i:=false)in Pack;[ |reflexivity].
 apply astar_l_ais_intro with(i:=[0])in Pack;[ |reflexivity].
 apply astar_l_acs_intro with(i:=nil)in Pack;[ |reflexivity].
 apply astar_l_aop'_intro with(aop:=spec_done None)in Pack;[ |reflexivity].
 unfold QJold,V293_quiet_irq_snapshot,V293_enter_open_external,QJraw,QCkept,
 p_local,LINV,V293_shared_li in *;clear H Moved Owned Extra;sep auto;apply V293_switch_li_good.
Qed.
Lemma QJsnapshot_to_builder : forall nest M O,nest<256 -> QCstate M O|=QJold nest ->QCstate M O|=ECentry.
Proof.
 intros nest M O Bound H.
 unfold QJold,V293_quiet_irq_snapshot,V293_enter_open_external,V293_quiet_irq_kept in H.
 assert(P:QCstate M O|=
 (Amapsto(99%positive,0%Z)Tint8 true(V293_byteval 1) **
 (Amapsto(96%positive,0%Z)Tint8 true(V293_byteval nest) **
 Amapsto(97%positive,0%Z)Tint8 true(V293_byteval 0))) **
 (<||spec_done None||> ** OS[isrupd(fun _:hid=>false)0 true,false,[0],nil] **
 (V293ReadyTaskInvariant.V293_ready_core 80%positive 81%positive 82%positive **
 (V293_dispatch_cell 106%Z V293_tcb_type **
 (V293_storage(V293_ready_irq_prefix 92%positive 91%positive 94%positive 95%positive) **
 (V293_storage nil ** A_dom_lenv nil ** p_local V293_shared_li OwnershipWaiting nil ** ECglobals))))))by(unfold ECglobals;sep auto).
 eapply astar_mono in P;[ |apply astar_mono;[apply V293_storage_byte_close;lia|apply astar_mono;apply V293_storage_byte_close;lia]|intros s K;exact K].
 assert(P2:QCstate M O|=
 (V293_storage(V293_ready_irq_prefix 92%positive 91%positive 94%positive 95%positive) **
 V293_storage([((99%positive,0%Z),Tint8);((96%positive,0%Z),Tint8);((97%positive,0%Z),Tint8)]++nil)) **
 (<||spec_done None||> ** OS[isrupd(fun _:hid=>false)0 true,false,[0],nil] **
 (V293ReadyTaskInvariant.V293_ready_core 80%positive 81%positive 82%positive **
 (V293_dispatch_cell 106%Z V293_tcb_type **
 (A_dom_lenv nil ** p_local V293_shared_li OwnershipWaiting nil ** ECglobals)))))by(cbn[app V293_storage];clear H;sep auto).
 eapply astar_mono in P2;[ |apply V293_storage_append|intros s K;exact K].
 assert(Core:QCstate M O|=getinv(RDinv 0) **
 (<||spec_done None||> ** OS[isrupd(fun _:hid=>false)0 true,false,[0],nil] **
 (A_dom_lenv nil ** p_local V293_shared_li OwnershipWaiting nil ** ECglobals))).
 { change(getinv(RDinv 0))with(V293_ready_storage_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type JBcells).
   unfold V293_ready_storage_core,V293_ready_storage_extra,JBcells,V293_ready_irq_prefix in *.
   rewrite app_nil_r in P2;clear H P;sep auto. }
 assert(Z:(JBge,emp,empmem,isrupd(fun _:hid=>false)0 true,(false,[0],nil),empabst,spec_done None)|=isr_inv).
 { unfold isr_inv;exists(isrupd(fun _:hid=>false)0 true);split.
   - simpl;repeat split;reflexivity.
   - exists 0;split.
     + simpl;repeat split;reflexivity.
     + apply apure_intro;[split;reflexivity|intros;lia]. }
 assert(All:QCstate M O|=isr_inv ** (getinv(RDinv 0) **
 (<||spec_done None||> ** OS[isrupd(fun _:hid=>false)0 true,false,[0],nil] **
 (A_dom_lenv nil ** p_local V293_shared_li OwnershipWaiting nil ** ECglobals)))).
 { unfold QCstate;apply sat_split';exists empmem;exists M;exists empabst;exists O.
   split;[apply join_emp| ];split;[apply join_emp| ];split;assumption. }
 unfold ECentry,ECpre,ipreasrt',invlth_noisr;cbn[starinv_noisr Nat.sub].
 clear H P P2 Core Z;sep auto.
Qed.

Definition QJentry nest:=BQsnapshot 1 nest 0(spec_done None)false(isrupd(fun _:hid=>false)0 true)[0]nil OwnershipWaiting.
Definition QJfilter:=V293_irq_quiet_filter 99%positive 96%positive 97%positive.
Definition QJpre:=BQpre //\\ QJfilter.
Lemma QJentry_pack : forall nest,QJold nest ==>QJentry nest.
Proof. intro nest;unfold QJold,QJentry,BQsnapshot;apply V293_irq_bound_snapshot_pack. Qed.
Lemma QJentry_controls : forall nest,
 QJentry nest ==>V293_irq_controls 99%positive 96%positive 97%positive 1 nest 0.
Proof. intro nest;unfold QJentry,BQsnapshot;apply V293_irq_bound_snapshot_controls. Qed.
Lemma QJentry_filter : forall nest,1<=nest ->nest<256 ->QJentry nest ==>QJfilter.
Proof.
 intros nest Positive Bound st H;unfold QJfilter,V293_irq_quiet_filter.
 exists 1;exists nest;exists 0;apply astar_l_apure_intro;[apply QJentry_controls;exact H|repeat split;lia].
Qed.
Theorem QJfiltered_nonempty : forall nest,1<=nest ->nest<256 ->exists M Mf O Of,
 join M Mf(JBmemory nest Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 QCstate M O|=QJentry nest /\QCstate M O|=QJpre.
Proof.
 intros nest Positive Bound;destruct(QJentry_nonempty nest Bound)as(M&Mf&O&Of&JM&JO&Old).
 assert(Entry:QCstate M O|=QJentry nest)by(apply QJentry_pack;exact Old).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ];split;[exact Entry| ].
 split;[apply BQpre_pack;apply QJsnapshot_to_builder with(nest:=nest);assumption|apply QJentry_filter with(nest:=nest);assumption].
Qed.
Theorem QJactual_wrapper :
 InfRules BDspec V293_scheduler LDli RDinv arfalse BQret
 QJpre(V293_irq_source_wrapper 301%Z 300%Z Int.zero)Afalse OwnershipWaiting.
Proof.
 unfold QJpre,QJfilter;apply(V293_interrupt_quiet_builder_continuous
 100%Z 101%Z 102%Z 103%Z 105%Z 106%Z 108%Z 109%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 93%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil BDspec 301%Z 300%Z QCintspec 0(fun _:hid=>false)nil
 OwnershipWaiting nil BQpre BQret Int.zero);try reflexivity.
 all:unfold gettopis,INUM;rewrite ?Int.unsigned_zero;cbn;lia.
Qed.
Theorem QJtyped_pair :
 (exists M Mf O Of,join M Mf(JBmemory 1 Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\QCstate M O|=QJpre) /\
 (exists M Mf O Of,join M Mf(JBmemory 255 Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\QCstate M O|=QJpre).
Proof.
 split;[destruct(QJfiltered_nonempty 1 ltac:(lia) ltac:(lia))as(M&Mf&O&Of&JM&JO&E&P)|
 destruct(QJfiltered_nonempty 255 ltac:(lia) ltac:(lia))as(M&Mf&O&Of&JM&JO&E&P)];
 exists M;exists Mf;exists O;exists Of;auto.
Qed.
Theorem QJdepth_pair :
 V293_exit_quiet_depth 1(V293_interrupt_nest_after 1 1)=1 /\
 V293_exit_quiet_depth 1(V293_interrupt_nest_after 1 255)=254 /\
 V293_quiet_exit_valid 1(V293_interrupt_nest_after 1 255)0 [0].
Proof.
 split;[reflexivity| ];split;[reflexivity|apply V293_quiet_pair_valid_saturated;try lia].
 unfold gettopis,INUM;cbn;lia.
Qed.
Theorem QJdispatch_filter_rejected : forall st,
 st|=V293_irq_controls 99%positive 96%positive 97%positive 1 0 0 ->~st|=QJfilter.
Proof.
 intros st Controls Filter;destruct Filter as[run[nest[locked Filter]]].
 apply astar_l_apure_elim in Filter;destruct Filter as[[R[N[L Quiet]]]Filtered].
 destruct(V293_irq_controls_unique 99%positive 96%positive 97%positive
 1 0 0 run nest locked st ltac:(lia) ltac:(lia) ltac:(lia) R N L Controls Filtered)as[ER[EN EL]].
 subst run nest locked;specialize(Quiet eq_refl);lia.
Qed.
Lemma QJmerge_pointwise : forall (m n m' n':mem) a,
 get m a=get m' a ->get n a=get n' a ->get(merge m n)a=get(merge m' n')a.
Proof. intros m n m' n' a Left Right;repeat rewrite map_merge_semp by reflexivity;rewrite Left,Right;reflexivity. Qed.
Theorem QJonly_nesting_changes : forall x y b off,(b,off)<>(96%positive,0%Z) ->
 get(JBmemory x Int.zero Int.zero)(b,off)=get(JBmemory y Int.zero Int.zero)(b,off).
Proof.
 intros x y b off Other;unfold JBmemory,JBready,JBinner.
 apply QJmerge_pointwise;[reflexivity| ];apply QJmerge_pointwise;[reflexivity| ];apply QJmerge_pointwise;[reflexivity| ].
 unfold JBcontrols;cbn[OwnershipCellsMemory].
 do 6 (apply QJmerge_pointwise;[reflexivity| ]).
 apply QJmerge_pointwise;[ |reflexivity].
 unfold OwnershipCellMemory.
 repeat rewrite OwnershipBytesOutside;try reflexivity.
 all:unfold V293_byteval;cbn[encode_val OwnershipBytesAddresses];intros[E|E];[inversion E;congruence|contradiction].
Qed.
Theorem QJliteral_nesting_load : forall nest,nest<256 ->
 load Tint8(JBmemory nest Int.zero Int.zero)(96%positive,0%Z)=Some(V293_byteval nest).
Proof.
 intros nest Bound;destruct(QJentry_nonempty nest Bound)as(M&Mf&O&Of&JM&JO&Old).
 pose proof(QJentry_controls nest _ (QJentry_pack nest _ Old))as C.
 pose proof(proj1(proj2(V293_irq_controls_load 99%positive 96%positive 97%positive
 1 nest 0 _ ltac:(lia) Bound ltac:(lia) C)))as L.
 eapply load_mem_mono;[exact L|exists Mf;exact JM].
Qed.
Definition QJreturned depth:=BQsnapshot 1 depth 0(spec_done None)false(fun _:hid=>false)[0]nil OwnershipWaiting.
Theorem QJsaturated_return_literal : QJreturned 254 ==>BQret.
Proof.
 unfold QJreturned,BQsnapshot,BQret;apply V293_bound_quiet_return_resources;try reflexivity;lia.
Qed.
Definition QJreturned_old (depth:nat):=V293_quiet_irq_snapshot
 106%Z 112%Z 110%Z 111%Z 92%positive 81%positive 80%positive 91%positive 82%positive
 94%positive 95%positive 99%positive 96%positive 97%positive nil
 1 depth 0(spec_done None)false(fun _:hid=>false)[0]nil OwnershipWaiting.
Theorem QJreturned_old_nonempty : forall nest,nest<256 -> exists M Mf O Of,
 join M Mf(JBmemory nest Int.zero Int.zero) /\ join O Of(RIabstract OwnershipWaiting) /\
 BQreturned_state M O|=QJreturned_old nest.
Proof.
 intros nest Bound;pose proof(QJraw_heap nest Bound)as H;unfold JBstate in H.
 assert(Moved:(JBge,emp,JBmemory nest Int.zero Int.zero,(fun _:hid=>false),
 (false,nil,nil),RIabstract OwnershipWaiting,spec_done None)|=QJraw nest ** Atrue).
 { eapply good_inv_prop;[split;[exact(proj1(QJraw_good nest))|exact Logic.I]|exact H]. }
 assert(New:BQreturned_state(JBmemory nest Int.zero Int.zero)(RIabstract OwnershipWaiting)|=QJraw nest ** Atrue).
 { unfold BQreturned_state;eapply goodfrm_prop;[split;[exact(proj2(QJraw_good nest))|exact Logic.I]|exact Moved]. }
 apply sat_split in New;destruct New as(M&Mf&O&Of&JM&JO&Owned&Extra).
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ].
 assert(G:(JBge,emp,empmem,(fun _:hid=>false),(false,[0],nil),empabst,spec_done None)|=
 V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive).
 { unfold V293_quiet_globals;repeat split;apply agvarenv_intro;
 split;reflexivity. }
 assert(Pack:BQreturned_state M O|=V293_quiet_globals 112%Z 110%Z 111%Z 99%positive 96%positive 97%positive ** QJraw nest).
 { unfold BQreturned_state;apply sat_split';exists empmem;exists M;exists empabst;exists O.
 split;[apply join_emp| ];split;[apply join_emp| ];split;assumption. }
 apply astar_l_adomlenv_intro with(d:=nil)in Pack.
 2:{ intros x tau;split;[contradiction|intros[l E];discriminate]. }
 apply astar_l_aisr_intro with(i:=(fun _:hid=>false))in Pack;[ |reflexivity].
 apply astar_l_aie_intro with(i:=false)in Pack;[ |reflexivity].
 apply astar_l_ais_intro with(i:=[0])in Pack;[ |reflexivity].
 apply astar_l_acs_intro with(i:=nil)in Pack;[ |reflexivity].
 apply astar_l_aop'_intro with(aop:=spec_done None)in Pack;[ |reflexivity].
 unfold QJreturned_old,V293_quiet_irq_snapshot,V293_enter_open_external,QJraw,QCkept,
 p_local,LINV,V293_shared_li in *;clear H Moved Owned Extra;sep auto;apply V293_switch_li_good.
Qed.
Theorem QJsaturated_return_nonempty : exists M Mf O Of,
 join M Mf(JBmemory 254 Int.zero Int.zero) /\join O Of(RIabstract OwnershipWaiting) /\
 BQreturned_state M O|=QJreturned 254 /\BQreturned_state M O|=BQret.
Proof.
 destruct(QJreturned_old_nonempty 254 ltac:(lia))as(M&Mf&O&Of&JM&JO&Old).
 assert(New:BQreturned_state M O|=QJreturned 254).
 { unfold QJreturned_old in Old;unfold QJreturned,BQsnapshot;apply V293_irq_bound_snapshot_pack;exact Old. }
 exists M;exists Mf;exists O;exists Of;split;[exact JM| ];split;[exact JO| ];split;[exact New|apply QJsaturated_return_literal;exact New].
Qed.
