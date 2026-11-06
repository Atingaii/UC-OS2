(* Closed canonical builder heap; same program and same successor memory. *)
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

Lemma BDstorage_focus : forall cells a tp,
 In(a,tp)cells ->V293_storage cells ==>V293_storage_cell a tp ** Atrue.
Proof.
 induction cells as [ | [b tau] tail IH];intros a tp Member s Held;[contradiction| ].
 cbn[In]in Member;cbn[V293_storage]in Held.
 destruct Member as[Equal|Member].
 - inversion Equal;subst;sep auto.
 - eapply astar_mono in Held;[ |intros st H;exact H|apply IH;exact Member].
   sep auto.
Qed.
Lemma BDarray_member : forall len b off tp n,n<len ->
 In((b,(off+Z.of_nat n)%Z),tp)(V293_array_cells b off 1 tp len).
Proof.
 induction len;intros b off tp n Bound;[lia| ];destruct n.
 - replace(off+Z.of_nat 0)%Z with off by lia;left;reflexivity.
 - right;replace(off+Z.of_nat(S n))%Z with(off+1+Z.of_nat n)%Z by lia.
   apply IHlen;lia.
Qed.
Lemma BDsubheap_read : forall a tp v ge le M whole frame ir aux O op,
 join M frame whole ->load tp whole a=Some v ->
 (ge,le,M,ir,aux,O,op)|=V293_storage_cell a tp ** Atrue ->
 load tp M a=Some v.
Proof.
 intros a tp v ge le M whole frame ir aux O op JM Full Held.
 unfold V293_storage_cell in Held;sep normal in Held;sep destruct Held.
 assert(Read:load tp M a=Some x).
 { eapply V293_record_star_load_l with(s:=(ge,le,M,ir,aux,O,op))
   (P:=V293_owned_record_cell(a,tp,x))(Q:=Atrue).
   - apply V293_owned_record_cell_load.
   - unfold V293_owned_record_cell;sep auto. }
 assert(FullRead:load tp whole a=Some x).
 { eapply load_mem_mono;[exact Read|exists frame;exact JM]. }
 congruence.
Qed.
Lemma BDcanonical_reads :
 load Tint8(JBmemory 0 Int.zero Int.zero)(94%positive,0%Z)=Some(V293_byteval 6) /\
 (forall n,n<256 ->load Tint8(JBmemory 0 Int.zero Int.zero)(92%positive,Z.of_nat n)=
 Some(V293_byteval(V293_ready_lookup n))).
Proof.
 pose proof(JBentry 0 Int.zero Int.zero nil(spec_done None)ltac:(lia))as Entry.
 assert(Cache:JBstate(JBmemory 0 Int.zero Int.zero)nil(sched;;spec_done None)|=
 V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) ** Atrue).
 { unfold JBdata,V293_exit_ready_body_data,V293_exit_ready_body_core,
   V293_handoff_byte,V293_counter_cell,V293_time_cell,V293_exit_cells,V293_interrupt_cells in Entry;
   cbn[V293_rdy_raw_cells V293_storage]in Entry;unfold V293_owned_record_cell;sep auto;
   apply V293_byte_type;lia. }
 assert(Inputs:JBstate(JBmemory 0 Int.zero Int.zero)nil(sched;;spec_done None)|=
 V293_inputs_full 92%positive 81%positive 80%positive 16 0 ** Atrue).
 { unfold JBdata,V293_exit_ready_body_data,V293_exit_ready_body_core,
 V293_handoff_byte,V293_counter_cell,V293_time_cell,V293_exit_cells,V293_interrupt_cells in Entry;
 cbn[V293_rdy_raw_cells V293_storage]in Entry;clear Cache;sep auto. }
 eapply astar_mono in Inputs;[ |apply V293_inputs_borrow|intros s H;exact H].
 assert(Borrowed:JBstate(JBmemory 0 Int.zero Int.zero)nil(sched;;spec_done None)|=
 V293_sched_inputs 92%positive 81%positive 80%positive 16 0(V293_ready_group 16 0) ** Atrue)by(sep auto).
 split.
 - eapply V293_record_star_load_l with(s:=JBstate(JBmemory 0 Int.zero Int.zero)nil(sched;;spec_done None));[apply V293_owned_record_cell_load|exact Cache].
 - pose proof(V293_star_reads_l _ _ _ _ _ _ _ _
   (V293_sched_inputs_load 92%positive 81%positive 80%positive 16 0(V293_ready_group 16 0)
    ltac:(lia)ltac:(lia)ltac:(vm_compute;lia)) _ Borrowed)as Reads.
   exact(proj1(proj2 Reads)).
Qed.

Definition BDK:=kseq(sprim excrit)(kseq sret(kcall 300%Z
 (V293_exit_boundary_body 112%Z 110%Z 111%Z 120%Z 105%Z 103%Z 106%Z 108%Z 109%Z 200%Z
 (V293_interrupt_handoff 103%Z 108%Z 106%Z))emp(kseq(sprim exint)kstop))).
Definition BDpost bs M:RstateOP:=
 (JBge,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,[0],[false]),CSO,spec_done None).
Definition BDrest:=V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **Atrue).
Definition BDowned:=SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_irq_controls 99%positive 96%positive 97%positive 1 0 0 **BDrest).
Definition BDprefix M bs Mf:=
 QCstate M CSO|=BQpre /\
 V293_local_steps RDprogram
 (curs(V293_irq_source_wrapper 301%Z 300%Z Int.zero),(kenil,kstop))(gettaskst(QCstate M CSO))
 (curs(sprim(switch 106%Z)),(kenil,BDK))(gettaskst(BDpost bs Mf)).

(* Initial cache and all 256 lookup entries are derived on the OWNED
   builder subheap, not substituted with unrelated whole-fixture reads. *)
Theorem BDprepare : exists M frame bs Mf,
 join M frame(JBmemory 0 Int.zero Int.zero) /\BDprefix M bs Mf /\
 BDpost bs Mf|=BDowned /\
 load(Tptr V293_tcb_type)Mf(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load Tint8 Mf(94%positive,0%Z)=Some(V293_byteval 4).
Proof.
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
 destruct(V293_builder_dispatch_prefix 106%Z 112%Z 110%Z 111%Z
 92%positive 81%positive 80%positive 91%positive 82%positive 94%positive 95%positive
 99%positive 96%positive 97%positive nil QCintspec 0 nil OwnershipWaiting nil BQpre
 (spec_done None)(QCstate M CSO)RDprogram V293_scheduler 301%Z 300%Z Int.zero
 120%Z 105%Z 103%Z 108%Z 109%Z 200%Z 100%Z 101%Z 102%Z 104%Z 93%positive OwnershipTasks 6
 eq_refl eq_refl Pre Capture eq_refl eq_refl eq_refl
 ltac:(vm_compute;intuition congruence)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
 (RIfixed_tasks OwnershipWaiting)SXcurrent SXnot_highest Cache Lookup eq_refl
 ltac:(change(0<=0<2)%Z;lia))as(bs&next&nh&Mf&Different&Changed&Highest&Current&Trace&Post&Pointer&CacheF&Captured).
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
 subst nh;exists M;exists frame;exists bs;exists Mf.
 split;[exact JM| ];split;[split;[exact Pre|exact Trace]| ];split;[exact Post| ];split;assumption.
Qed.

Definition BDT:tasks:=set(set emp OwnershipReady CSready)OwnershipWaiting
 (curs(sprim(switch 106%Z)),(kenil,BDK)).
Definition BDTnext:tasks:=set BDT OwnershipWaiting(SKIP,(kenil,BDK)).
Definition BDL bs:cltenvs:=set(set emp OwnershipReady emp)OwnershipWaiting(V293_cpu_lenv 120%Z bs).
Definition BDA:ltaskstset:=set(set emp OwnershipReady((true,nil,nil):localst))OwnershipWaiting(false,[0],[false]).
Definition BDS bs M:osstate:=(JBge,BDL bs,M,(fun _=>false),BDA).
Definition BDglobal:lprog:=(GXempty,(RDprogram,GXempty,(fun _=>None))).
Definition BDhigh:hprog:=(GXempty,((fun _=>None),(fun _=>None),V293_scheduler)).

(* Finite LOCAL handler prefix followed by an original GLOBAL switch match.
   No claim that this is a lifted global handler trace or a full ProgSim. *)
Theorem BDcompleted_match : forall cst,exists M frame bs Ms Mf,
 join M frame(JBmemory 0 Int.zero Int.zero) /\BDprefix M bs Ms /\
 lpstep BDglobal BDT cst(BDS bs Ms)OwnershipWaiting BDTnext cst(BDS bs Mf)OwnershipReady /\
 hpstep BDhigh CST cst CSO CSTnext cst CSnext /\
 load(Tptr V293_tcb_type)Mf(1%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load Tint8 Mf(94%positive,0%Z)=Some(V293_byteval 4) /\
 get CSnext curtid=Some(oscurt OwnershipReady) /\
 V293_control_capture 99%positive 96%positive 97%positive
 (JBge,V293_cpu_lenv 120%Z bs,Mf,(fun _=>false),(false,[0],[false]),CSnext,spec_done None)=
 Some(CSnext,V293_control 1 0 0) /\
 (forall T' cst' S' t',lpstep BDglobal BDT cst(BDS bs Ms)OwnershipWaiting T' cst' S' t' ->
 T'=BDTnext /\cst'=cst /\S'=BDS bs Mf /\t'=OwnershipReady) /\
 ~lpstepabt BDglobal BDT cst(BDS bs Ms)OwnershipWaiting /\
 get BDTnext OwnershipWaiting=Some(SKIP,(kenil,BDK)) /\
 get BDTnext OwnershipReady=Some CSready /\
 get(BDL bs)OwnershipWaiting=Some(V293_cpu_lenv 120%Z bs) /\
 @get tid localst ltaskstset TaskLStMap BDA OwnershipWaiting=Some(false,[0],[false]).
Proof.
 intro cst;destruct BDprepare as(M&frame&bs&Ms&JM&Prefix&Owned&Read&OldCache).
 destruct(V293_control_switch_forward 80%positive 81%positive 82%positive
 99%positive 96%positive 97%positive GXempty RDprogram GXempty((fun _=>None):intunit)
 (fun _=>None)(fun _=>None)V293_scheduler BDT CST cst OwnershipWaiting OwnershipReady
 106%Z BDK CSke CSks(spec_done None)JBge(V293_cpu_lenv 120%Z bs)(BDL bs)Ms
 (fun _=>false)BDA [0][false]93%positive 1%positive V293_tcb_type CSO(spec_done None)BDrest 1 0 0
 ltac:(lia)ltac:(lia)ltac:(lia)(map_get_set _ _ _)(map_get_set _ _ _)(map_get_set _ _ _)
 eq_refl Read eq_refl eq_refl CSchosen(map_get_set _ _ _)Owned)
 as(Mf&Low&Store&High&Event&After&Captured&Physical&Observed&All&Output&NoAbort&Frames).
 assert(Cache:load Tint8 Mf(94%positive,0%Z)=Some(V293_byteval 4)).
 { eapply V293_record_star_load_l with
 (s:=(JBge,V293_cpu_lenv 120%Z bs,Mf,(fun _=>false),(false,[0],[false]),CSnext,spec_done None))
 (P:=V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 4))(Q:=Atrue).
 - apply V293_owned_record_cell_load.
 - clear -After;unfold BDrest in After;sep auto. }
 exists M;exists frame;exists bs;exists Ms;exists Mf.
 repeat first[assumption|split|solve[apply map_get_set]|solve[vm_compute;reflexivity]].
Qed.

(* The completed actual execution witness is retained before changing only
   the expected final abstract-current observation: Ready -> Waiting. *)
Theorem BDcompleted_observation : forall cst,exists M frame bs Ms Mf,
 join M frame(JBmemory 0 Int.zero Int.zero) /\BDprefix M bs Ms /\
 lpstep BDglobal BDT cst(BDS bs Ms)OwnershipWaiting BDTnext cst(BDS bs Mf)OwnershipReady /\
 hpstep BDhigh CST cst CSO CSTnext cst CSnext /\
 load(Tptr V293_tcb_type)Mf(1%positive,0%Z)=Some(Vptr OwnershipReady) /\
 get CSnext curtid=Some(oscurt OwnershipReady) /\
 ~get CSnext curtid=Some(oscurt OwnershipWaiting).
Proof.
 intro cst;destruct(BDcompleted_match cst)as(M&frame&bs&Ms&Mf&JM&Prefix&Low&High&Physical&Cache&Observed&Rest).
 exists M;exists frame;exists bs;exists Ms;exists Mf.
 repeat first[assumption|split].
 rewrite Observed;intro Wrong;inversion Wrong.
Qed.
