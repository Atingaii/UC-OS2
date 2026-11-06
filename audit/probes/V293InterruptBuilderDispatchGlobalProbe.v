(* Same nonempty builder heap; actual pint, globally lifted prefix and switch. *)
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

Definition BGinterrupted:=cure(econst32(Int.repr 37)).
Definition BGcaller:env:=set emp 108%Z(999%positive,Tint32).
Definition BGint:=kint BGinterrupted CSke BGcaller CSks.
Definition BGtail:=BDK ## BGint.
Definition BGinput:tasks:=set(set emp OwnershipReady CSready)OwnershipWaiting(BGinterrupted,(CSke,CSks)).
Definition BGenvironments:cltenvs:=set(set emp OwnershipReady emp)OwnershipWaiting BGcaller.
Definition BGauxinput:ltaskstset:=set(set emp OwnershipReady((true,nil,nil):localst))OwnershipWaiting(true,nil,nil).
Definition BGhandler:=V293_irq_source_wrapper 301%Z 300%Z Int.zero.
Definition BGip:intunit:=fun i=>if Nat.eqb i 0 then Some BGhandler else None.
Definition BGglobal:lprog:=(GXempty,(RDprogram,GXempty,BGip)).
Definition BGentered (M:mem):=
 (set BGinput OwnershipWaiting(curs BGhandler,(kenil,BGint)),
 (JBge,set BGenvironments OwnershipWaiting emp,M,isrupd(fun _=>false)0 true,
 set BGauxinput OwnershipWaiting(false,[0],nil)),OwnershipWaiting).
Definition BGcutT:=set BGinput OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,BGtail)).
Definition BGcutL bs:=set BGenvironments OwnershipWaiting(V293_cpu_lenv 120%Z bs).
Definition BGcutA:=set BGauxinput OwnershipWaiting(false,[0],[false]).
Definition BGcutS bs M:osstate:=(JBge,BGcutL bs,M,(fun _=>false),BGcutA).
Definition BGcut bs M:=(BGcutT,BGcutS bs M,OwnershipWaiting).
Definition BGnextT:=set BGcutT OwnershipWaiting(SKIP,(kenil,BGtail)).

Lemma BGprogram_merge : pumerge RDprogram GXempty=RDprogram.
Proof. apply functional_extensionality;intro f;unfold pumerge,GXempty;destruct(RDprogram f);reflexivity. Qed.

Theorem BGprepare : forall cst,exists M frame bs Ms,
 join M frame(JBmemory 0 Int.zero Int.zero) /\ QCstate M CSO|=BQpre /\
 (match BGentered M with(Ti,Si,ti)=>lpstep BGglobal BGinput cst
 (JBge,BGenvironments,M,(fun _=>false),BGauxinput)OwnershipWaiting Ti cst Si ti end) /\
 V293_global_steps BGglobal cst(BGentered M)(BGcut bs Ms) /\
 BDpost bs Ms|=BDowned /\
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
 (isrupd(fun _:hid=>false)0 true)[0]nil OwnershipWaiting).
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
 { intros n Bound;eapply BDsubheap_read with(ge:=JBge)(le:=emp)(ir:=isrupd(fun _:hid=>false)0 true)(aux:=(false,[0],nil))(O:=CSO)(op:=spec_done None);[exact JM|exact(proj2 BDcanonical_reads n Bound)| ].
   eapply astar_mono in Table;[ |apply BDstorage_focus;replace(Z.of_nat n)with(0+Z.of_nat n)%Z by lia;apply BDarray_member;exact Bound|intros s H;exact H].
   clear -Table;unfold QCstate in Table;sep auto. }
 destruct(V293_builder_dispatch_global_prefix 106%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil QCintspec 0 nil OwnershipWaiting nil BQpre
 (spec_done None)JBge M CSO GXempty RDprogram GXempty BGip BGinput BGenvironments BGauxinput cst
 BGinterrupted CSke BGcaller CSks V293_scheduler
 301%Z 300%Z Int.zero 120%Z 105%Z 103%Z 108%Z 109%Z 200%Z 100%Z 101%Z 102%Z 104%Z
 93%positive OwnershipTasks 6
 (map_get_set _ _ _)(map_get_set _ _ _)(map_get_set _ _ _)
 ltac:(exact I)ltac:(intros j H;reflexivity)ltac:(change(0<2);lia)eq_refl
 eq_refl eq_refl Pre Capture
 ltac:(rewrite BGprogram_merge;reflexivity)ltac:(rewrite BGprogram_merge;reflexivity)
 ltac:(rewrite BGprogram_merge;reflexivity)
 ltac:(vm_compute;intuition congruence)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 (RIfixed_tasks OwnershipWaiting)SXcurrent SXnot_highest Cache Lookup eq_refl
 ltac:(change(0<=0<2)%Z;lia))
 as(bs&next&nh&Ms&Different&Changed&Highest&Current&Entry&Trace&Post&Pointer&CacheF&Captured).
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

(* The switch is taken from the exact endpoint of the preceding GLOBAL trace. *)
Theorem BGcompleted_match : forall cst,exists M frame bs Ms Mf,
 join M frame(JBmemory 0 Int.zero Int.zero) /\ QCstate M CSO|=BQpre /\
 (match BGentered M with(Ti,Si,ti)=>lpstep BGglobal BGinput cst
 (JBge,BGenvironments,M,(fun _=>false),BGauxinput)OwnershipWaiting Ti cst Si ti end) /\
 V293_global_steps BGglobal cst(BGentered M)(BGcut bs Ms) /\
 lpstep BGglobal BGcutT cst(BGcutS bs Ms)OwnershipWaiting BGnextT cst(BGcutS bs Mf)OwnershipReady /\
 hpstep BDhigh CST cst CSO CSTnext cst CSnext /\
 V293_global_steps BGglobal cst
 (BGinput,(JBge,BGenvironments,M,(fun _=>false),BGauxinput),OwnershipWaiting)
 (BGnextT,BGcutS bs Mf,OwnershipReady) /\
 load(Tptr V293_tcb_type)Mf(1%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load Tint8 Mf(94%positive,0%Z)=Some(V293_byteval 4) /\
 get CSnext curtid=Some(oscurt OwnershipReady) /\
 V293_control_capture 99%positive 96%positive 97%positive
 (JBge,V293_cpu_lenv 120%Z bs,Mf,(fun _=>false),(false,[0],[false]),CSnext,spec_done None)=
 Some(CSnext,V293_control 1 0 0) /\
 (forall T' cst' S' t',lpstep BGglobal BGcutT cst(BGcutS bs Ms)OwnershipWaiting T' cst' S' t' ->
 T'=BGnextT /\cst'=cst /\S'=BGcutS bs Mf /\t'=OwnershipReady) /\
 ~lpstepabt BGglobal BGcutT cst(BGcutS bs Ms)OwnershipWaiting /\
 get BGnextT OwnershipWaiting=Some(SKIP,(kenil,BGtail)) /\
 get BGnextT OwnershipReady=Some CSready /\
 get(BGcutL bs)OwnershipWaiting=Some(V293_cpu_lenv 120%Z bs) /\
 get(BGcutL bs)OwnershipReady=Some emp /\
 @get tid localst ltaskstset TaskLStMap BGcutA OwnershipWaiting=Some(false,[0],[false]) /\
 get BGcaller 108%Z=Some(999%positive,Tint32).
Proof.
 intro cst;destruct(BGprepare cst)as(M&frame&bs&Ms&JM&Pre&Entry&Prefix&Owned&Read&OldCache).
 destruct(V293_control_switch_forward 80%positive 81%positive 82%positive
 99%positive 96%positive 97%positive GXempty RDprogram GXempty BGip
 (fun _=>None)(fun _=>None)V293_scheduler BGcutT CST cst OwnershipWaiting OwnershipReady
 106%Z BGtail CSke CSks(spec_done None)JBge(V293_cpu_lenv 120%Z bs)(BGcutL bs)Ms
 (fun _=>false)BGcutA [0][false]93%positive 1%positive V293_tcb_type CSO(spec_done None)BDrest 1 0 0
 ltac:(lia)ltac:(lia)ltac:(lia)(map_get_set _ _ _)(map_get_set _ _ _)(map_get_set _ _ _)
 eq_refl Read eq_refl eq_refl CSchosen(map_get_set _ _ _)Owned)
 as(Mf&Low&Store&High&Event&After&Captured&Physical&Observed&All&Output&NoAbort&Frames).
 assert(Cache:load Tint8 Mf(94%positive,0%Z)=Some(V293_byteval 4)).
 { eapply V293_record_star_load_l with
 (s:=(JBge,V293_cpu_lenv 120%Z bs,Mf,(fun _=>false),(false,[0],[false]),CSnext,spec_done None))
 (P:=V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 4))(Q:=Atrue).
 - apply V293_owned_record_cell_load.
 - clear -After;unfold BDrest in After;sep auto. }
 assert(Full:V293_global_steps BGglobal cst
 (BGinput,(JBge,BGenvironments,M,(fun _=>false),BGauxinput),OwnershipWaiting)
 (BGnextT,BGcutS bs Mf,OwnershipReady)).
 { eapply rt1n_trans with(y:=BGentered M);[exact Entry| ].
   eapply V293_global_trans;[exact Prefix| ].
   eapply rt1n_trans with(y:=(BGnextT,BGcutS bs Mf,OwnershipReady));[exact Low|apply rt1n_refl]. }
 exists M;exists frame;exists bs;exists Ms;exists Mf.
 repeat first[assumption|split|solve[apply map_get_set]|solve[vm_compute;reflexivity]].
Qed.

(* These observations are made AFTER actual entry/prefix/low/high execution. *)
Theorem BGcompleted_saved_context : forall cst,exists M frame bs Ms Mf,
 join M frame(JBmemory 0 Int.zero Int.zero) /\
 V293_global_steps BGglobal cst
 (BGinput,(JBge,BGenvironments,M,(fun _=>false),BGauxinput),OwnershipWaiting)
 (BGnextT,BGcutS bs Mf,OwnershipReady) /\
 lpstep BGglobal BGcutT cst(BGcutS bs Ms)OwnershipWaiting BGnextT cst(BGcutS bs Mf)OwnershipReady /\
 hpstep BDhigh CST cst CSO CSTnext cst CSnext /\
 load(Tptr V293_tcb_type)Mf(1%positive,0%Z)=Some(Vptr OwnershipReady) /\
 get CSnext curtid=Some(oscurt OwnershipReady) /\
 get BGnextT OwnershipWaiting=Some(SKIP,(kenil,
 BDK ## kint BGinterrupted CSke BGcaller CSks)).
Proof.
 intro cst;destruct(BGcompleted_match cst)
 as(M&frame&bs&Ms&Mf&JM&Pre&Entry&Prefix&Low&High&Full&Physical&Cache&Observed&Captured&All&NoAbort&Saved&Rest).
 exists M;exists frame;exists bs;exists Ms;exists Mf.
 split;[exact JM| ];split;[exact Full| ];split;[exact Low| ];split;[exact High| ];
 split;[exact Physical| ];split;[exact Observed|exact Saved].
Qed.
