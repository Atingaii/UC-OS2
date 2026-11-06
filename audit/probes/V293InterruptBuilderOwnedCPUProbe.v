(* Strong CPU ownership on the same builder/switch/client execution. *)
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderDispatchSwitch.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderEnterResources.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlSwitchSimulation.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlScheduler.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFixedControlSpec.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietBuilder.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBindings.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnvironment.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyBoundary.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterInternal.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptSourceRoundtrip.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Require Import Coq.Relations.Relation_Operators.
Require Import CertiOS.audit.probes.V293InterruptQuietBuilderProbe.
Require Import CertiOS.audit.probes.V293InterruptBoundQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293InterruptQuietContinuousProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyDynamicProbe.
Require Import CertiOS.audit.probes.V293OSIntExitLocalDispatchProbe.
Require Import CertiOS.audit.probes.V293InterruptReadyEnvironmentProbe.
Require Import CertiOS.audit.probes.V293OSIntExitReadyBodyProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptQuietISRReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedStateWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTargetHandoff.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.audit.probes.V293ReadyTargetHandoffProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchExecution.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.audit.probes.V293OSIntExitDispatchExecutionProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCallExecution.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.
Require Import CertiOS.audit.probes.V293OSIntExitDispatchCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSwitchEntry.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.audit.probes.V293OSIntExitSwitchEntryProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitInterruptGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import CertiOS.audit.probes.V293OSIntExitInterruptGlobalProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCacheContract.
Require Import CertiOS.audit.probes.V293OSIntExitBoundarySwitchProbe.
Require Import CertiOS.audit.probes.V293InterruptControlSchedulerProbe.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntEnterOpenExact.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitAllExactDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyLocal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitUnifiedInternal.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitNondispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedExactLocal.
Require Import CertiOS.tactics.sepauto.sep_combine_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickDelayHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyBody.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHandoffHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeAccess.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptReadyEnter.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyDispatch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedSwitch.
Require Import CertiOS.framework.proof.toptheorem.
Require Import CertiOS.tactics.basetac.join_general.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBoundQuietContinuous.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundDynamic.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitLocalDispatch.
Require Import CertiOS.audit.probes.V293OSIntExitBoundDynamicProbe.
Require Import CertiOS.audit.probes.V293InterruptEntryControlProbe.
Require Import CertiOS.audit.probes.V293OSIntExitExactInternalProbe.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.audit.probes.V293InterruptBuilderDispatchSwitchProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderDispatchGlobal.
Require Import CertiOS.audit.probes.V293InterruptBuilderDispatchGlobalProbe.
Require Import CertiOS.audit.probes.V293SelectedScalarTaskSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293SelectedScalarTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptBuilderOwnedCPU.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickReturnTail.
Definition OCrest bs:=
 V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Atrue)).
Definition OCowned bs:=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_irq_controls 99%positive 96%positive 97%positive 1 0 0 **OCrest bs).
Definition OCframe bs:=V293_irq_controls 99%positive 96%positive 97%positive 1 0 0 **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 4) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Atrue)).
Definition OCpacket(bs:block)(M:mem):Prop:=exists Ms Mt Mf Mtail Os Ot Of Otail,
 join Mt Mf Mtail /\join Ms Mtail M /\join Ot Of Otail /\join Os Otail CSnext /\
 satp(JBge,emp,Ms,(fun _=>false),(true,nil,nil))Os(INV SCinv) /\
 satp(JBge,emp,Mt,(fun _=>false),(true,nil,nil))Ot(RDYINV SCinv OwnershipReady **LINV V293_shared_li OwnershipReady nil) /\
 (JBge,emp,Mf,(fun _=>false),(true,nil,nil),Of,spec_done None)|=OCframe bs /\
 TaskSim BGglobal CSready(JBge,emp,Mt,(fun _=>false),(true,nil,nil))
 BDhigh CSready Ot V293_shared_li SCinv
 (fun s=>satp(fst s)(snd s)(RDYINV SCinv OwnershipReady **LINV V293_shared_li OwnershipReady nil))OwnershipReady.

Theorem OCprepare : forall cst,exists M frame bs Ms,
 join M frame(JBmemory 0 Int.zero Int.zero) /\ QCstate M CSO|=BQpre /\
 (match BGentered M with(Ti,Si,ti)=>lpstep BGglobal BGinput cst
 (JBge,BGenvironments,M,(fun _=>false),BGauxinput)OwnershipWaiting Ti cst Si ti end) /\
 V293_global_steps BGglobal cst(BGentered M)(BGcut bs Ms) /\
 BDpost bs Ms|=OCowned bs /\
 load(Tptr V293_tcb_type)Ms(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load Tint8 Ms(94%positive,0%Z)=Some(V293_byteval 4).
Proof.
 intro cst;
 destruct(QJentry_nonempty 0 ltac:(lia))as(M&frame&O&Of&JM&JO&Old).
 assert(Core:QCstate M O|=V293_shared_core **Atrue).
 { unfold QJold,V293_quiet_irq_snapshot,V293_enter_open_external,V293_quiet_irq_kept,
   V293ReadyTaskInvariant.V293_ready_core,V293_shared_ready_records in Old;unfold V293_shared_core;sep auto. }
 assert(Empty:Of=emp)by(eapply V293_shared_no_abstract_frame;[exact Core|exact JO]).
 subst Of;apply map_join_emp' in JO;subst O.
 assert(Pre:QCstate M CSO|=BQpre).
 { apply BQpre_pack;apply QJsnapshot_to_builder with(nest:=0);[lia|exact Old]. }
 assert(Snapshot:QCstate M CSO|=BQsnapshot 1 0 0(spec_done None)false
 (isrupd(fun _:hid=>false)0 true)(cons 0 nil)nil OwnershipWaiting).
 { apply QJentry_pack;exact Old. }
 assert(Capture:V293_control_capture 99%positive 96%positive 97%positive(QCstate M CSO)=Some(CSO,V293_control 1 0 0)).
 { apply V293_control_capture_owned;try lia;apply QJentry_controls;exact Snapshot. }
 assert(CacheCell:QCstate M CSO|=V293_storage_cell(94%positive,0%Z)Tint8 **Atrue).
 { clear -Old;unfold QJold,V293_quiet_irq_snapshot,V293_enter_open_external,V293_quiet_irq_kept,
   V293_ready_irq_prefix in Old;cbn[V293_storage]in Old;sep auto. }
 assert(Table:QCstate M CSO|=V293_storage(V293_array_cells 92%positive 0 1 Tint8 256) **Atrue).
 { clear -Old;unfold QJold,V293_quiet_irq_snapshot,V293_enter_open_external,V293_quiet_irq_kept,
   V293_ready_irq_prefix in Old;cbn[V293_storage]in Old;sep auto. }
 assert(Cache:load Tint8 M(94%positive,0%Z)=Some(V293_byteval 6)).
 { eapply BDsubheap_read;[exact JM|exact(proj1 BDcanonical_reads)|exact CacheCell]. }
 assert(Lookup:forall n,n<256 ->load Tint8 M(92%positive,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))).
 { intros n Bound;eapply BDsubheap_read with(ge:=JBge)(le:=emp)(ir:=isrupd(fun _:hid=>false)0 true)(aux:=(false,(cons 0 nil),nil))(O:=CSO)(op:=spec_done None);[exact JM|exact(proj2 BDcanonical_reads n Bound)| ].
   eapply astar_mono in Table;[ |apply BDstorage_focus;replace(Z.of_nat n)with(0+Z.of_nat n)%Z by lia;apply BDarray_member;exact Bound|intros s H;exact H].
   clear -Table;unfold QCstate in Table;sep auto. }
 destruct(V293_builder_dispatch_owned_cpu_prefix 106%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil QCintspec 0 nil OwnershipWaiting nil BQpre
 (spec_done None)(QCstate M CSO)(pumerge RDprogram GXempty) V293_scheduler
 301%Z 300%Z Int.zero 120%Z 105%Z 103%Z 108%Z 109%Z 200%Z 100%Z 101%Z 102%Z 104%Z
 93%positive OwnershipTasks 6
 eq_refl eq_refl Pre Capture
 ltac:(rewrite BGprogram_merge;reflexivity)ltac:(rewrite BGprogram_merge;reflexivity)
 ltac:(rewrite BGprogram_merge;reflexivity)
 ltac:(vm_compute;intuition congruence)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 (RIfixed_tasks OwnershipWaiting)SXcurrent SXnot_highest Cache Lookup eq_refl
 ltac:(change(0<=0<2)%Z;lia))
 as(bs&next&nh&Ms&Different&Changed&Highest&Current&LocalTrace&Post&Pointer&CacheF&Captured).
 pose proof(V293_interrupt_local_steps_global GXempty RDprogram GXempty BGip _ _ _ _ LocalTrace
 BGinterrupted CSke BGcaller CSks BGinput BGenvironments BGauxinput OwnershipWaiting cst ltac:(exact I))as Trace.
 assert(Entry:match BGentered M with(Ti,Si,ti)=>lpstep BGglobal BGinput cst
 (JBge,BGenvironments,M,(fun _=>false),BGauxinput)OwnershipWaiting Ti cst Si ti end).
 { eapply V293_interrupt_source_enter;try apply map_get_set;try reflexivity.
   - intros j H;reflexivity.
   - change(0<2);lia. }
 assert(Next:next=OwnershipReady).
 { destruct RTliteral_rel as(Lo&Hi&Nonempty&Bitmap&TableRel).
   eapply V293_highest_unique;[exact TableRel|exact Highest|exact FXhighest]. }
 subst next.
 assert(Priority:nh=4).
 { destruct Current as[Bound[st[m Task]]].
   assert(Ready:get OwnershipTasks OwnershipReady=Some(Int.repr 4,rdy,Vnull))by reflexivity.
   unfold get,TcbMap in Task,Ready;rewrite Ready in Task.
   apply V293_priority_repr_injective;[exact Bound|lia| ].
   symmetry;exact(f_equal(fun x=>match x with Some(p,_,_)=>p |None=>Int.zero end)Task). }
 subst nh;exists M;exists frame;exists bs;exists Ms.
 split;[exact JM| ];split;[exact Pre| ];split;[exact Entry| ];split;[exact Trace| ];
 split;[exact Post| ];split;assumption.
Qed.

Lemma OCafter_core : forall bs M,
 (JBge,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,(cons 0 nil),(cons false nil)),CSnext,spec_done None)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipReady **
 (V293_irq_controls 99%positive 96%positive 97%positive 1 0 0 **OCrest bs) ->
 (JBge,emp,M,(fun _=>false),(true,nil,nil),CSnext,spec_done None)|=
 SCcore **(CurTid OwnershipReady **(OCframe bs)).
Proof.
 intros bs M Held.
 unfold SWINVt in Held;fold(CurTid OwnershipReady)in Held.
 eapply astar_mono in Held;[ |eapply astar_mono;[apply V293ReadyTaskInvariant.V293_ready_switch_open|intros s H;exact H]|intros s H;exact H].
 assert(Target:forall m o,
 (JBge,V293_cpu_lenv 120%Z bs,m,(fun _=>false),(false,(cons 0 nil),(cons false nil)),o,spec_done None)|=
 V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) ->
 (JBge,V293_cpu_lenv 120%Z bs,m,(fun _=>false),(false,(cons 0 nil),(cons false nil)),o,spec_done None)|=V293_dispatch_cell 106%Z V293_tcb_type).
 { intros m o H;unfold V293_dispatch_cell.
   apply astar_l_apure_elim in H;destruct H as[Typed H].
   exists(Vptr OwnershipReady);apply astar_l_apure_intro;[ |exact Typed].
   exists 93%positive;unfold Agvarenv',Aptrmapsto;cbn[addrval_to_addr].
   apply astar_l_agvarenv_intro;[exact H|split;reflexivity]. }
 assert(Pack:(JBge,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,(cons 0 nil),(cons false nil)),CSnext,spec_done None)|=
 V293_ready_storage_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type nil **
 (CurTid OwnershipReady **(OCframe bs))).
 { unfold OCrest in Held;unfold V293_ready_storage_core,V293_ready_storage_extra;cbn[V293_storage].
   assert(Reorder:(JBge,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,(cons 0 nil),(cons false nil)),CSnext,spec_done None)|=
   V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
   (V293ReadyTaskInvariant.V293_ready_core 80%positive 81%positive 82%positive **
   (CurTid OwnershipReady **(OCframe bs))))by(unfold OCframe;sep auto).
   apply sat_split in Reorder;destruct Reorder as(mt&mr&ot&orr&JM&JO&Cell&Rest).
   apply Target in Cell.
   assert(Named:(JBge,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,(cons 0 nil),(cons false nil)),CSnext,spec_done None)|=
   V293_dispatch_cell 106%Z V293_tcb_type **
   (V293ReadyTaskInvariant.V293_ready_core 80%positive 81%positive 82%positive **(CurTid OwnershipReady **(OCframe bs)))).
   { apply sat_split';exists mt;exists mr;exists ot;exists orr;split;[exact JM| ];split;[exact JO| ];split;assumption. }
   clear Held;sep auto. }
 assert(Self:sched_self V293_scheduler CSnext).
 { exists OwnershipReady;split;[apply map_get_set|exists OwnershipTasks;split;[reflexivity|exact FXhighest]]. }
 apply V293_current_core_highest_frame with(bc:=94%positive)in Pack;[ |exact Self].
 fold SCcore in Pack.
 apply sat_split in Pack;destruct Pack as(mc&mr&oc&orr&JM&JO&Core&Rest).
 assert(CoreLocal:(JBge,emp,mc,(fun _=>false),(false,(cons 0 nil),(cons false nil)),oc,spec_done None)|=SCcore).
 { unfold SCcore in *;eapply good_inv_prop;[apply V293_current_core_good|exact Core]. }
 assert(CoreReady:(JBge,emp,mc,(fun _=>false),(true,nil,nil),oc,spec_done None)|=SCcore).
 { unfold SCcore in *;eapply V293_current_core_aux;exact CoreLocal. }
 assert(RestReady:(JBge,emp,mr,(fun _=>false),(true,nil,nil),orr,spec_done None)|=CurTid OwnershipReady **(OCframe bs)).
 { exact Rest. }
 apply sat_split';exists mc;exists mr;exists oc;exists orr.
 split;[exact JM| ];split;[exact JO| ];split;assumption.
Qed.

Lemma OCpartition : forall bs M,
 (JBge,emp,M,(fun _=>false),(true,nil,nil),CSnext,spec_done None)|=
 SCcore **(CurTid OwnershipReady **(OCframe bs)) ->OCpacket bs M.
Proof.
 intros bs M Held;unfold OCpacket.
 assert(Local:Aemp ==>LINV V293_shared_li OwnershipReady nil)by(apply V293_switch_local_empty).
 assert(Pack:(JBge,emp,M,(fun _=>false),(true,nil,nil),CSnext,spec_done None)|=
 SCcore **(CurTid OwnershipReady **(LINV V293_shared_li OwnershipReady nil **(OCframe bs)))).
 { assert(E:(JBge,emp,M,(fun _=>false),(true,nil,nil),CSnext,spec_done None)|=
 Aemp **(SCcore **(CurTid OwnershipReady **(OCframe bs))))by(sep auto).
   eapply astar_mono in E;[ |exact Local|intros s H;exact H];sep auto. }
 exact(V293_scalar_current_TaskSim 80%positive 81%positive 82%positive 106%Z V293_tcb_type nil 94%positive
 GXempty RDprogram GXempty BGip((fun _=>None),(fun _=>None),V293_scheduler)CSready
 V293_shared_li nil OwnershipReady (OCframe bs) JBge emp M(fun _=>false)true nil nil CSnext(spec_done None)
 SCshape ltac:(reflexivity)ltac:(discriminate)Pack).
Qed.

Theorem OCcompleted_owned : forall cst,exists M frame bs Ms Mf,
 join M frame(JBmemory 0 Int.zero Int.zero) /\
 V293_global_steps BGglobal cst
 (BGinput,(JBge,BGenvironments,M,(fun _=>false),BGauxinput),OwnershipWaiting)
 (BGnextT,BGcutS bs Mf,OwnershipReady) /\
 lpstep BGglobal BGcutT cst(BGcutS bs Ms)OwnershipWaiting BGnextT cst(BGcutS bs Mf)OwnershipReady /\
 hpstep BDhigh CST cst CSO CSTnext cst CSnext /\
 OCpacket bs Mf /\
 (JBge,emp,Mf,(fun _=>false),(true,nil,nil),CSnext,spec_done None)|=
 SCcore **(CurTid OwnershipReady **OCframe bs) /\
 get BGnextT OwnershipWaiting=Some(SKIP,(kenil,BDK ## kint BGinterrupted CSke BGcaller CSks)) /\
 get BGnextT OwnershipReady=Some CSready /\
 get(BGcutL bs)OwnershipReady=Some emp /\
 @get tid localst ltaskstset TaskLStMap BGcutA OwnershipReady=Some(true,nil,nil).
Proof.
 intro cst;destruct(OCprepare cst)as(M&frame&bs&Ms&JM&Pre&Entry&Prefix&Owned&Read&OldCache).
 destruct(V293_control_switch_forward 80%positive 81%positive 82%positive
 99%positive 96%positive 97%positive GXempty RDprogram GXempty BGip
 (fun _=>None)(fun _=>None)V293_scheduler BGcutT CST cst OwnershipWaiting OwnershipReady
 106%Z BGtail CSke CSks(spec_done None)JBge(V293_cpu_lenv 120%Z bs)(BGcutL bs)Ms
 (fun _=>false)BGcutA (cons 0 nil)(cons false nil)93%positive 1%positive V293_tcb_type CSO(spec_done None)(OCrest bs) 1 0 0
 ltac:(lia)ltac:(lia)ltac:(lia)(map_get_set _ _ _)(map_get_set _ _ _)(map_get_set _ _ _)
 eq_refl Read eq_refl eq_refl CSchosen(map_get_set _ _ _)Owned)
 as(Mf&Low&Store&High&Event&After&Captured&Physical&Observed&All&Output&NoAbort&Frames).
 assert(Core:(JBge,emp,Mf,(fun _=>false),(true,nil,nil),CSnext,spec_done None)|=
 SCcore **(CurTid OwnershipReady **OCframe bs))by(apply OCafter_core with(bs:=bs);exact After).
 assert(Packet:OCpacket bs Mf)by(apply OCpartition;exact Core).
 assert(Full:V293_global_steps BGglobal cst
 (BGinput,(JBge,BGenvironments,M,(fun _=>false),BGauxinput),OwnershipWaiting)
 (BGnextT,BGcutS bs Mf,OwnershipReady)).
 { eapply rt1n_trans with(y:=BGentered M);[exact Entry| ].
   eapply V293_global_trans;[exact Prefix| ].
   eapply rt1n_trans with(y:=(BGnextT,BGcutS bs Mf,OwnershipReady));[exact Low|apply rt1n_refl]. }
 exists M;exists frame;exists bs;exists Ms;exists Mf.
 split;[exact JM| ];split;[exact Full| ];split;[exact Low| ];split;[exact High| ];split;[exact Packet| ];split;[exact Core| ].
 repeat first[split|solve[vm_compute;reflexivity]].
Qed.


Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.

(* Capability, not an execution of the suspended Waiting task. The residual
   assertion describes the exact heap returned by the original free function. *)
Lemma OCrelease_capability : forall bs M,
 (JBge,emp,M,(fun _=>false),(true,nil,nil),CSnext,spec_done None)|=
 SCcore **(CurTid OwnershipReady **OCframe bs) ->
 exists Mr byte,
 free Tint32 bs M=Some Mr /\
 (JBge,emp,Mr,(fun _=>false),(true,nil,nil),CSnext,spec_done None)|=
 SCcore **(CurTid OwnershipReady **SCframe) /\
 (forall k,k<4 ->get Mr(bs,Z.of_nat k)=None) /\
 (forall b i,b<>bs \/(i<0)%Z \/(4<=i)%Z ->get Mr(b,i)=get M(b,i)) /\
 get M(bs,0%Z)=Some(true,byte) /\
 load Tint32 M(bs,0%Z)=Some(Vint32 Int.zero) /\
 load Tint32(set M(bs,0%Z)(false,byte))(bs,0%Z)=Some(Vint32 Int.zero) /\
 free Tint32 bs(set M(bs,0%Z)(false,byte))=None /\
 (forall a,a<>(bs,0%Z) ->get(set M(bs,0%Z)(false,byte))a=get M a).
Proof.
 intros bs M Core.
 assert(Owned:(JBge,emp,M,(fun _=>false),(true,nil,nil),CSnext,spec_done None)|=
 Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (SCcore **(CurTid OwnershipReady **SCframe))).
 { unfold OCframe in Core;unfold SCframe;sep auto. }
 pose proof(V293_tick_raw_owned_writable _ _ _ _ _ _ _ _ _ _ _ Owned)as W.
 destruct(W 0 ltac:(change(0<4);lia))as(byte&Byte).
 change(get M(bs,0%Z)=Some(true,byte))in Byte.
 assert(Read:load Tint32 M(bs,0%Z)=Some(Vint32 Int.zero)).
 { eapply V293_record_star_load_l with
 (s:=(JBge,emp,M,(fun _=>false),(true,nil,nil),CSnext,spec_done None))
 (P:=Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero))(Q:=SCcore **(CurTid OwnershipReady **SCframe)).
 - intros s [Points Empty];eapply mapstoval_load;[reflexivity|exact Points].
 - exact Owned. }
 destruct(V293_tick_free_owned _ _ _ _ _ _ _ _ _ _ _ Owned)as(Mr&Free&Rest).
 destruct(V293_cpu_first_permission M bs byte Byte)as(Same&Denied&Other).
 exists Mr;exists byte.
 split;[exact Free| ];split;[exact Rest| ];split.
 - intros k K;replace(Z.of_nat k)with(0+Z.of_nat k)%Z by lia.
   eapply V293_freeb_removed;[exact Free|exact K].
 - split.
   + intros b i Away;eapply V293_freeb_outside;[exact Free|exact Away].
   + split;[exact Byte| ];split;[exact Read| ];split;[rewrite Same;exact Read| ];split;assumption.
Qed.

(* The selected client really takes three steps on both semantics. Its OS
   state is unchanged, so the allocated CPU cell remains available afterwards. *)
Theorem OCcompleted_client_cpu : exists M frame bs Ms Mf Mr byte,
 join M frame(JBmemory 0 Int.zero Int.zero) /\
 V293_global_steps BGglobal SCclient
 (BGinput,(JBge,BGenvironments,M,(fun _=>false),BGauxinput),OwnershipWaiting)
 (SCT3,BGcutS bs Mf,OwnershipReady) /\
 lpstep BGglobal BGcutT SCclient(BGcutS bs Ms)OwnershipWaiting BGnextT SCclient(BGcutS bs Mf)OwnershipReady /\
 hpstep BDhigh CST SCclient CSO CSTnext SCclient CSnext /\
 OCpacket bs Mf /\
 get SCT3 OwnershipWaiting=Some(SKIP,(kenil,BDK ## kint BGinterrupted CSke BGcaller CSks)) /\
 get SCT3 OwnershipReady=Some SCend /\
 free Tint32 bs Mf=Some Mr /\
 (JBge,emp,Mr,(fun _=>false),(true,nil,nil),CSnext,spec_done None)|=
 SCcore **(CurTid OwnershipReady **SCframe) /\
 (forall k,k<4 ->get Mr(bs,Z.of_nat k)=None) /\
 (forall b i,b<>bs \/(i<0)%Z \/(4<=i)%Z ->get Mr(b,i)=get Mf(b,i)) /\
 get Mf(bs,0%Z)=Some(true,byte) /\
 load Tint32 Mf(bs,0%Z)=Some(Vint32 Int.zero) /\
 load Tint32(set Mf(bs,0%Z)(false,byte))(bs,0%Z)=Some(Vint32 Int.zero) /\
 free Tint32 bs(set Mf(bs,0%Z)(false,byte))=None /\
 (forall a,a<>(bs,0%Z) ->get(set Mf(bs,0%Z)(false,byte))a=get Mf a).
Proof.
 destruct(OCcompleted_owned SCclient)as(M&frame&bs&Ms&Mf&JM&Prefix&Low&High&Packet&Core&Saved&Selected&Env&Aux).
 destruct(SCthree_steps bs Mf)as(L1&L2&L3&H1&H2&H3&N1&N2&N3&SavedFinal&End).
 destruct(OCrelease_capability bs Mf Core)as(Mr&byte&Free&Rest&Removed&Outside&Byte&Read&ReadOnly&Denied&Other).
 assert(Full:V293_global_steps BGglobal SCclient
 (BGinput,(JBge,BGenvironments,M,(fun _=>false),BGauxinput),OwnershipWaiting)
 (SCT3,BGcutS bs Mf,OwnershipReady)).
 { eapply V293_global_trans;[exact Prefix| ].
   eapply rt1n_trans with(y:=(SCT1,BGcutS bs Mf,OwnershipReady));[exact L1| ];
   eapply rt1n_trans with(y:=(SCT2,BGcutS bs Mf,OwnershipReady));[exact L2| ];
   eapply rt1n_trans with(y:=(SCT3,BGcutS bs Mf,OwnershipReady));[exact L3|apply rt1n_refl]. }
 exists M;exists frame;exists bs;exists Ms;exists Mf;exists Mr;exists byte.
 repeat first[assumption|split].
Qed.
