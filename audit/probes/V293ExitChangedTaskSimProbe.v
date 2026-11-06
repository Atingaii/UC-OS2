(* Same original allocated call, now observed before comparison/counting. *)
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewInternal.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Lia.
Require Import CertiOS.certiucos.v293.proofs.V293SwitchProgSim.
Require Import CertiOS.audit.probes.V293CurrentHandoffPrefixProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCurrentInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293CurrentHandoffPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitReadyHandoff.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293OSIntExitReadyHandoffProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293ReadyFullCallProbe.
Require Import CertiOS.audit.probes.V293ReadyGlobalTraceProbe.
Require Import CertiOS.audit.probes.V293ReadySwitchStepProbe.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.audit.probes.V293SwitchProgSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ClientSkipTaskSim.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.framework.proof.step_prop.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import CertiOS.audit.probes.V293HandoffProgSimProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293ReadySourceTailProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitDispatchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySourceTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchCall.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Local Open Scope nat_scope.
Require Import CertiOS.audit.probes.V293ExitDispatchProgSimProbe.
Require Import CertiOS.audit.probes.V293SchedCallProgSimProbe.
Require Import CertiOS.audit.probes.V293SchedCallEntryProgSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitCallDispatchProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTarget.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.framework.auxlibs.MapLib.
Require Import CertiOS.audit.probes.V293ExitCallDispatchProgSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitNestingProgSim.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturnProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.audit.probes.V293ExitNestingProgSimProbe.
Require Import CertiOS.audit.probes.V293CriticalReturnProgSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ResumedReturnProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitResumedReturn.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import Coq.Relations.Relation_Operators.

Require Import CertiOS.audit.probes.V293ResumedReturnProgSimProbe.

Local Open Scope nat_scope.
Require Import CertiOS.certiucos.v293.proofs.V293ExitActiveCallProgSim.
Require Import CertiOS.audit.probes.V293ExitQuietCallProgSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.framework.proof.join_prop.

Require Import CertiOS.audit.probes.V293ActiveCallWitnessProbe.

(* Explicit SOURCE-LEVEL interrupt-switch boundary, not a CPU-port body.
   Original call model and original framework semantics remain unchanged. *)
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitDispatchExecution.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitCallExecution.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitInterruptGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCacheContract.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.


(* The SAME allocated full call, seven C steps before its old switch. *)
Require Import CertiOS.audit.probes.V293ActiveCallTraceProbe.
Require Import CertiOS.audit.probes.V293OSIntExitDispatchCallProbe.
Require Import CertiOS.audit.probes.V293OSIntExitSwitchEntryProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSharedReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSharedReclose.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.audit.probes.V293SharedSwitchReturnProbe.
Require Import CertiOS.audit.probes.V293SwitchReturnTaskSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293StorageSwitchPre.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.memory_prop.

Require CertiOS.tactics.hoareforward.symbolic_lemmas.

Import ListNotations.
Local Open Scope nat_scope.
Local Ltac st_env := cbn[getgenv];unfold QPge;
 rewrite map_get_set' by discriminate;reflexivity.

Require Import CertiOS.audit.probes.V293OldSwitchPacketProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293StoragePendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293CurrentReturnInvariant.

Require Import CertiOS.certiucos.v293.proofs.V293StorageSwitchTaskSim.
Require Import CertiOS.audit.probes.V293InvariantPendingTaskSimProbe.

Require Import CertiOS.certiucos.v293.proofs.V293HandoffTaskSim.
Import ListNotations.
Local Open Scope nat_scope.


Require Import CertiOS.certiucos.v293.proofs.V293ExitChangedTaskSim.
Definition ECbranch := sif(V293_OSSched_different 103%Z 108%Z)
 (sseq(V293_OSSched_increment 109%Z)(sseq(sskip None)(V293_interrupt_handoff 103%Z 108%Z 106%Z)))(sskip None).
Definition ECrest_raw br bs : asrt :=
 V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((97%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((br,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **RCframe))))).
Definition ECpre br bs : asrt :=
 SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) ** ECrest_raw br bs))).

Lemma ECbody_prefix :
 forall br bg bp P ge caller M ir enabled si ci O op ct R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter handoff
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget bs,
 fresh M bs ->
 P f=Some(V293_exit_boundary_function running nesting lock saved table high target current counter sched_id handoff) ->
 P sched_id=Some(V293_OSSchedNew_function unmap group rows high y) ->
 ~In saved [unmap;group;rows;high;table;target;nesting;lock;running;current;counter] ->
 y<>unmap ->y<>group ->y<>rows ->y<>high ->y<>table ->bh<>bp ->bn<>bt ->
 get ge unmap=Some(bt,Tarray Tint8 256) ->get ge group=Some(bg,Tint8) ->
 get ge rows=Some(br,Tarray Tint8 2) ->get ge high=Some(bh,Tint8) ->
 get ge table=Some(bp,Tarray(Tptr V293_tcb_type)13) ->get ge target=Some(bo,Tptr V293_tcb_type) ->
 get ge nesting=Some(bn,Tint8) ->get ge lock=Some(bl,Tint8) ->
 get ge running=Some(brun,Tint8) ->get ge current=Some(bc,Tint8) ->get ge counter=Some(bcount,Tint32) ->
 get O abstcblsid=Some(abstcblist tasks) ->V293_current_task tasks ct nc ->
 ~V293_highest_ready tasks ct ->GoodInvAsrt R ->
 (forall n,n<256 ->load Tint8 M(bt,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))) ->
 (ge,caller,M,ir,(false,si,ci),O,op)|=SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **R))))))) ->
 exists next nh Mf,next<>ct /\ nh<>nc /\
 V293_highest_ready tasks next /\V293_current_task tasks next nh /\
 V293_local_steps P
 (curs(V293_exit_boundary_body running nesting lock saved table high target current counter sched_id handoff),(kenil,kstop))
 ((ge,V293_cpu_lenv saved bs,allocb M bs 0%Z 4),ir,(enabled,si,ci))
 (curs(sif(V293_OSSched_different high current)
 (sseq(V293_OSSched_increment counter)(sseq(sskip None)handoff))(sskip None)),(kenil,
   kseq(sprim excrit)(kseq sret kstop)))
 ((ge,V293_cpu_lenv saved bs,Mf),ir,(false,si,enabled::ci)) /\
 (ge,V293_cpu_lenv saved bs,Mf,ir,(false,si,enabled::ci),O,op)|=
 SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval nh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **R)))))))).
Proof.
 intros br bg bp P ge caller M ir enabled si ci O op ct R tasks nc
 f sched_id unmap group rows high y table target nesting lock running saved current counter handoff
 bt bh bo bn bl brun bc bcount c oldhigh oldtarget bs Fresh
 Program Scheduler SavedNames YU YG YR YH YT HP NT GU GG GR GH GT GO GN GL GRun GC GCount
 Map Current NotHighest Good Lookup Held.
 assert(NC:nc<256)by(destruct Current as[Bound _];lia).
 assert(BT:bs<>bt).
 { eapply V293_success_load_not_fresh;[exact Fresh|exact(Lookup 0 ltac:(lia))]. }
 set(le:=V293_cpu_lenv saved bs).
 assert(Names:forall x,In x [unmap;group;rows;high;table;target;nesting;lock;running;current;counter] ->get le x=None).
 { intros x Member;unfold le,V293_cpu_lenv;rewrite map_get_set'.
   - apply map_emp_get.
   - intro E;apply SavedNames;subst;exact Member. }
 assert(GoodAll:GoodInvAsrt
 (V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **R)))))))).
 { repeat split;try exact I;exact Good. }
 pose proof(V293_ready_critical_stack br bg bp ct _ ge caller M ir si ci(enabled::ci)O op GoodAll Held)as Stacked.
 pose proof(V293_ready_lenv_frame br bg bp ct _ ge caller M ir(false,si,enabled::ci)O op le GoodAll Stacked)as Local.
 destruct(V293_success_scheduler_storage M bs Fresh)as(Ms&Init&Writable&InitialFree&InitFrame).
 pose proof(V293_cpu_initialized_frame ge le M ir(false,si,enabled::ci)O op bs Ms _ Fresh Local Init)as Allocated.
 assert(Entry:(ge,le,Ms,ir,(false,si,enabled::ci),O,op)|=SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,oldhigh) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,oldtarget) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **R))))))))).
 { clear Held Stacked Local;sep auto. }
 assert(Run:load Tint8 Ms(brun,0%Z)=Some(V293_byteval 1)).
 { eapply V293_record_star_load_l with(s:=(ge,le,Ms,ir,(false,si,enabled::ci),O,op))
   (P:=V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1))(Q:=Atrue).
   - intros st H;apply V293_owned_record_cell_load;exact H.
   - clear Held Stacked Local Allocated;sep auto. }
 assert(LookupS:forall n,n<256 ->load Tint8 Ms(bt,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))).
 { intros n N;etransitivity;[apply V293_load_block_frame;intro i;apply InitFrame;congruence|apply Lookup;exact N]. }
 assert(GoodFrame:GoodInvAsrt(Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **R))))).
 { repeat split;try exact I;exact Good. }
 set(body:=V293_exit_boundary_body running nesting lock saved table high target current counter sched_id handoff).
 set(K:=kseq(sprim excrit)(kseq sret kstop)).
 destruct(V293_exit_boundary_dispatch_prefix br bg bp P K ge le Ms ir(false,si,enabled::ci)O op ct
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **R))))
 sched_id unmap group rows high y table target nesting lock current counter handoff
 bt bh bo bn bl oldhigh oldtarget Scheduler YU YG YR YH YT HP NT GU GG GR GH GT
 (Names high ltac:(cbn;tauto))(Names table ltac:(cbn;tauto))(Names target ltac:(cbn;tauto))GO
 (Names nesting ltac:(cbn;tauto))GN(Names lock ltac:(cbn;tauto))GL GoodFrame LookupS Entry)
 as(ts&lo&hi&entries&next&message&M0&b&My&Mskip&Mmid&Store&FY&FreeY&DeadY&Map'&Rel&Task&Middle&After&TargetLoad&Sched&MidFrame).
 assert(TS:ts=tasks)by congruence;subst ts.
 destruct Sched as(ts'&Map''&NextHighest);assert(TS:ts'=tasks)by congruence;subst ts'.
 destruct Rel as[Lo[Hi[Nonempty[Bitmap Table]]]].
 assert(Next:next<>ct)by(intro E;apply NotHighest;rewrite <-E;exact NextHighest).
 assert(Different:V293_ready_select lo hi(V293_ready_group lo hi)<>nc).
 { intro E;apply Next;apply(proj2(V293_OSSched_current_target lo hi entries tasks ct nc next
     Lo Hi Nonempty Bitmap Table Current NextHighest));exact E. }
 assert(Range:V293_ready_select lo hi(V293_ready_group lo hi)<13)
   by(eapply V293_ready_selection_range;[exact Lo|exact Hi|reflexivity|exact Nonempty]).
 assert(HighLoad:load Tint8 Mmid(bh,0%Z)=Some(V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi)))).
 { eapply V293_record_star_load_l with(s:=(ge,le,Mmid,ir,(false,si,enabled::ci),O,op))
   (P:=V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi))))(Q:=Atrue).
   - intros st H;apply V293_owned_record_cell_load;exact H.
   - clear Held Stacked Local Allocated Entry;sep auto. }
 assert(CurrentLoad:load Tint8 Mmid(bc,0%Z)=Some(V293_byteval nc)).
 { eapply V293_record_star_load_l with(s:=(ge,le,Mmid,ir,(false,si,enabled::ci),O,op))
   (P:=V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc))(Q:=Atrue).
   - intros st H;apply V293_owned_record_cell_load;exact H.
   - clear Held Stacked Local Allocated Entry;sep auto. }
 set(F:=SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi))) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **R)))))))).
 assert(CounterEntry:(ge,le,Mmid,ir,(false,si,enabled::ci),O,op)|=
 V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **F).
 { unfold F;clear Held Stacked Local Allocated Entry;sep auto. }
 assert(Post:(ge,le,Mmid,ir,(false,si,enabled::ci),O,op)|=
 SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi))) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32 c) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **R))))))))).
 { unfold F in CounterEntry;clear Held Stacked Local Allocated Entry After;sep auto. }
 exists next;exists(V293_ready_select lo hi(V293_ready_group lo hi));exists Mmid.
 split;[exact Next| ];split;[exact Different| ];split;[exact NextHighest| ];split.
 { split;[exact Range| ];exists rdy;exists message;exact Task. }
 split.
 - unfold V293_exit_boundary_body.
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_trans.
   { apply V293_csteps_local;eapply V293_success_assign_zero;[unfold le,V293_cpu_lenv;apply map_get_set|exact Init]. }
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_trans.
   { apply V293_csteps_local;eapply V293_entry_if_select with(flag:=true).
     unfold V293_OSIntEnter_running;change Int.one with(Int.repr(Z.of_nat 1)).
     exact(V293_success_global_byte_eq ge le Ms running brun 1 1 ltac:(lia)ltac:(lia)
       (Names running ltac:(cbn;tauto))GRun Run). }
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   eapply V293_local_cons;[apply encrit_step;reflexivity| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sskip_step]| ].
   eapply V293_local_cons;[apply ostc_step;eapply stmt_step;[reflexivity|apply sseq_step]| ].
   apply V293_csteps_local;exact Middle.
 - exact Post.
Qed.

Local Ltac ec_env := unfold QPge;rewrite map_get_set' by discriminate;reflexivity.
Lemma ECfixed_prefix : forall br bs cs,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->
 exists M,
 V293_local_steps(pumerge CPpo CGempty)
 (curs CPfullbody,(kenil,kstop))
 ((QPge br,V293_cpu_lenv 120%Z bs,allocb(QPmemory br 1 1)bs 0%Z 4),(fun _=>false),(false,nil,cs))
 (curs ECbranch,(kenil,kseq(sprim excrit)(kseq sret kstop)))
 ((QPge br,V293_cpu_lenv 120%Z bs,M),(fun _=>false),(false,nil,false::cs)) /\
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),RIabstract OwnershipWaiting,spec_done None)|=ECpre br bs.
Proof.
 intros br bs cs FR FS.
 pose proof(FWinitial_owned br(emp:env)FR)as Initial.
 assert(Entry: (QPge br,(emp:env),QPmemory br 1 1,(fun _=>false),(false,nil,cs),RIabstract OwnershipWaiting,spec_done None)|=
 SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((97%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((br,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **RCframe))))))))).
 { eapply V293_ready_critical_stack with(ci:=nil).
   - repeat split;try exact I;apply RCframe_good.
   - unfold FWstate,CPother in Initial;unfold V293_owned_record_cell in *;clear -Initial;sep auto. }
 assert(Lookup:forall n,n<256 ->load Tint8(QPmemory br 1 1)(92%positive,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))).
 { intros n Bound.
   eapply V293_record_star_load_l with(s:=FWstate(QPge br)(emp:env)(QPmemory br 1 1))
    (P:=V293_read_bytes 92%positive 0 V293_ready_table)(Q:=Atrue).
   - intros st H;replace(Z.of_nat n)with(0+Z.of_nat n)%Z by lia.
     apply V293_read_bytes_load.
     + change(n<256);exact Bound.
     + pose proof(proj1(V293_ready_row_spec n Bound));unfold V293_ready_lookup in *;lia.
     + exact H.
   - unfold CPother,RCframe in Initial;clear -Initial;sep auto. }
 assert(Current:V293_current_task OwnershipTasks OwnershipWaiting 6).
 { split;[lia|exists(wait(os_stat_sem(72%positive,Int.repr 5))Int.one);exists(Vptr(120%positive,Int.repr 7));reflexivity]. }
 assert(NotHighest:~V293_highest_ready OwnershipTasks OwnershipWaiting).
 { intros(p&m&Task&Minimum);vm_compute in Task;discriminate. }
 destruct(ECbody_prefix 80%positive 81%positive 82%positive(pumerge CPpo CGempty)
 (QPge br)(emp:env)(QPmemory br 1 1)(fun _=>false)false nil cs
 (RIabstract OwnershipWaiting)(spec_done None)OwnershipWaiting
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **RCframe)OwnershipTasks 6
 114%Z 107%Z 100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z 110%Z 111%Z 112%Z 120%Z 108%Z 109%Z
 (V293_interrupt_handoff 103%Z 108%Z 106%Z)
 92%positive 91%positive 93%positive 96%positive 97%positive br 94%positive 95%positive
 Int.mone(V293_byteval 88)(Vptr OwnershipWaiting)bs FS
 ltac:(vm_compute;reflexivity)ltac:(vm_compute;reflexivity)
 ltac:(cbn;intuition discriminate)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)
 ltac:(ec_env)ltac:(ec_env)ltac:(ec_env)ltac:(ec_env)ltac:(ec_env)ltac:(ec_env)
 ltac:(ec_env)ltac:(ec_env)ltac:(unfold QPge;apply map_get_set)ltac:(ec_env)ltac:(ec_env)
 (RIfixed_tasks OwnershipWaiting)Current NotHighest ltac:(split;[exact I|apply RCframe_good])Lookup Entry)
 as(next&nh&M&Different&PrioDifferent&Highest&Next&Trace&Post).
 destruct Next as[Range[st[msg Task]]].
 destruct Highest as[p[m[Ready Minimum]]].
 change(get OwnershipTasks next=Some(p,rdy,m))in Ready.
 rewrite Task in Ready;inversion Ready;subst st.
 destruct(RTonly_ready nh next msg Range Task)as[Priority[Selected Message]].
 subst nh next.

 exists M;split;[exact Trace| ]. unfold ECpre,ECrest_raw.
 clear -Post;sep auto.
Qed.

Definition ECrest br : list(addr*type) :=
 ((96%positive,0%Z),Tint8)::((97%positive,0%Z),Tint8)::
  ((br,0%Z),Tint8)::nil.
Definition ECcells br := ((94%positive,0%Z),Tint8)::((91%positive,0%Z),Tint8)::((95%positive,0%Z),Tint32)::ECrest br.
Definition ECinv br :=V293_ready_storage_inv 80%positive 81%positive 82%positive
 106%Z V293_tcb_type(ECcells br).
Definition ECowned br bs :=Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **V293_storage(ECrest br)))))).
Definition ECpacket br bs M cs ip A : Prop :=exists Mt Mf Ot Of,
 join Mt Mf M /\join Ot Of(RIabstract OwnershipWaiting) /\
 (QPge br,V293_cpu_lenv 120%Z bs,Mt,(fun _=>false),(false,nil,false::cs),Ot,spec_done None)|=ECowned br bs /\
 (QPge br,V293_cpu_lenv 120%Z bs,Mf,(fun _=>false),(false,nil,false::cs),Of,spec_done None)|=IWframe /\
 TaskSim(RCprogram,(CPpo,CGempty,ip))
 (curs ECbranch,(kenil,FTpending))
 (QPge br,V293_cpu_lenv 120%Z bs,Mt,(fun _=>false),(false,nil,false::cs))
 (RCprogram,A)(curs(hapi_code(spec_seq sched(spec_done None))),(kenil,kstop))Ot V293_shared_li(ECinv br)
 (fun st=>satp(fst st)(snd st)(RDYINV(ECinv br)OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.

Lemma ECpartition : forall br bs cs M ip A,
 getsched(RCprogram,A)=V293_scheduler ->
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=ECpre br bs ->
 ECpacket br bs M cs ip A.
Proof.
 intros br bs cs M ip A Sched Held.
 assert(Cells:V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((97%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((br,0%Z),Tint8,V293_byteval 1) **Aemp)) ==>
 V293_storage(ECrest br)).
 { cbn[ECrest V293_storage];repeat apply astar_mono;
   try(intros st H;exact H);apply V293_exit_cell_to_storage. }
 assert(Parts:(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=
 (V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((97%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((br,0%Z),Tint8,V293_byteval 1) **Aemp))) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **IWframe))))))).
 { unfold ECpre,ECrest_raw,IWframe in *;sep auto. }
 eapply astar_mono in Parts;[ |exact Cells|intros st H;exact H].
 assert(Packed:(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=ECowned br bs **IWframe)
 by(unfold ECowned;clear Held;sep auto).
 apply sat_split in Packed;destruct Packed as(Mt&Mf&Ot&Of&JM&JO&Owned&Frame).
 assert(Fields:(QPge br,V293_cpu_lenv 120%Z bs,Mt,(fun _=>false),(false,nil,false::cs),Ot,spec_done None)|=
 V293_shared_core **Atrue).
 { unfold ECowned,SWINVt in Owned.
   assert(Open:(QPge br,V293_cpu_lenv 120%Z bs,Mt,(fun _=>false),(false,nil,false::cs),Ot,spec_done None)|=
   SWINV(V293_ready_inv 80%positive 81%positive 82%positive) **Atrue)by(sep auto).
   eapply astar_mono in Open;[ |apply V293_ready_switch_open|intros st H;exact H].
   unfold V293_ready_core,V293_shared_ready_records,V293_shared_core in *;
   sep normal in Open;sep destruct Open;clear Parts Held;sep normal;
   exists x;exists x0;exists x1;exists x2;sep auto. }
 assert(Empty:Of=emp)by(eapply V293_shared_no_abstract_frame;[exact Fields|exact JO]).
 subst Of;apply map_join_emp' in JO;subst Ot.
 unfold ECpacket;exists Mt;exists Mf;exists(RIabstract OwnershipWaiting);exists(emp:osabst).
 split;[exact JM| ];split;[apply map_join_emp| ];split;[exact Owned| ];split;[exact Frame| ].
 unfold ECowned,ECinv,ECcells,FTpending,CPcall,ECbranch in *.
 eapply V293_exit_changed_TaskSim with(nh:=4)(nc:=6)(bc:=94%positive)(bh:=91%positive)(bo:=93%positive)
 (bk:=95%positive)(next:=OwnershipReady)(saved_value:=Vint32 Int.zero)(c:=Int.mone);
 [exact Sched|exact RPbinding|right;right;reflexivity|lia|lia|lia| | | | | | | |exact(RIfixed_tasks OwnershipWaiting)| |exact RIhighest|exact Owned].
 - unfold V293_cpu_lenv;rewrite map_get_set' by discriminate;apply map_emp_get.
 - unfold V293_cpu_lenv;rewrite map_get_set' by discriminate;apply map_emp_get.
 - unfold V293_cpu_lenv;rewrite map_get_set' by discriminate;apply map_emp_get.
 - st_env.
 - st_env.
 - st_env.
 - st_env.
 - exists(Int.repr 6,wait(os_stat_sem(72%positive,Int.repr 5))Int.one,Vptr(120%positive,Int.repr 7));reflexivity.
Qed.

Theorem ECactual_changed : forall br bs cs ncs ip A,
 getsched(RCprogram,A)=V293_scheduler ->
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->exists M,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (set FWtasks OwnershipWaiting(curs ECbranch,(kenil,FTpending)),
 (QPge br,FTenvs bs,M,(fun _=>false),FTaux cs ncs),OwnershipWaiting) /\
 ECpacket br bs M cs ip A /\
 load Tint32 M(bs,0%Z)=Some(Vint32 Int.zero) /\
 load Tint8 M(94%positive,0%Z)=Some(V293_byteval 6) /\
 load Tint32 M(95%positive,0%Z)=Some(Vint32 Int.mone).
Proof.
 intros br bs cs ncs ip A Sched FR FS.
 destruct(ECfixed_prefix br bs cs FR FS)as(M&Prefix&Held).
 pose proof(V293_local_steps_global RCprogram CPpo CGempty ip _ _ _ _ Prefix
 114%Z CPfullbody(emp:env)kstop Tvoid dnil(dcons 120%Z Tint32 dnil)
 FWtasks RPenvs(RPaux cs ncs)OwnershipWaiting HPcst RPbinding
 ltac:(change(goodks(RCprogram,(CPpo,CGempty,ip))CPcall);unfold CPcall;cbn[goodks];unfold pumerge;rewrite RPbinding;exact I))as Global.
 cbn[V293_enclose AddKsToTail]in Global.
 exists M;split.
 - eapply V293_global_trans;[apply FTenter;exact FS|exact Global].
 - split;[eapply ECpartition;[exact Sched|exact Held]| ];split.
   + apply(FTsaved_load bs (QPge br)(V293_cpu_lenv 120%Z bs)M(fun _=>false)
     (false,nil,false::cs)(RIabstract OwnershipWaiting)(spec_done None));
     unfold ECpre,ECrest_raw in Held;sep auto.
   + split.
     * eapply V293_record_star_load_l with
     (s:=(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),RIabstract OwnershipWaiting,spec_done None))
     (P:=V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6))(Q:=Atrue).
       -- intros st H;apply V293_owned_record_cell_load;exact H.
       -- unfold ECpre in Held;sep auto.
     * eapply V293_record_star_load_l with
       (s:=(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),RIabstract OwnershipWaiting,spec_done None))
       (P:=V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone))(Q:=Atrue).
       -- intros st H;apply V293_owned_record_cell_load;exact H.
       -- unfold ECpre,ECrest_raw in Held;sep auto.
Qed.

Theorem ECnonvacuous : exists br bs,
 fresh(NPinitial 1)br /\fresh(QPmemory br 1 1)bs /\
 forall cs (ncs:list bool) ip,exists M,
 ECpacket br bs M cs ip(snd V293SwitchProgSimProbe.SPph).
Proof.
 destruct(memory_has_fresh_block(NPinitial 1))as[br FR].
 destruct(memory_has_fresh_block(QPmemory br 1 1))as[bs FS].
 exists br;exists bs;split;[exact FR| ];split;[exact FS| ];intros.
 destruct(ECactual_changed br bs cs ncs ip(snd V293SwitchProgSimProbe.SPph)eq_refl FR FS)
 as(M&Trace&Packet&Saved&Cache&Counter);exists M;exact Packet.
Qed.

(* Controls concern the local comparison suffix, not full-entry simulation. *)
Lemma ECequal_no_count : forall P ks ge le M e yes,
 evalval e(ge,le,M)=Some(Vint32 Int.zero) ->
 cstepstar P(curs(sif e yes(sskip None)),(kenil,ks))(ge,le,M)
 (curs(sskip None),(kenil,ks))(ge,le,M).
Proof.
 intros P ks ge le M e yes E.
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sif_step]| ].
 eapply V293_cstepstar_trans;[apply V293_expr_steps;apply evalval_imply_estepstar;exact E| ].
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sviff_step;reflexivity]|apply c_stepstar0].
Qed.

Lemma ECwithout_increment : forall P ks ge le M e handoff,
 evalval e(ge,le,M)=Some(Vint32 Int.one) ->
 cstepstar P(curs(sif e(sseq(sskip None)handoff)(sskip None)),(kenil,ks))(ge,le,M)
 (curs handoff,(kenil,ks))(ge,le,M).
Proof.
 intros P ks ge le M e handoff E.
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sif_step]| ].
 eapply V293_cstepstar_trans;[apply V293_expr_steps;apply evalval_imply_estepstar;exact E| ].
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply svift_step;reflexivity]| ].
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sseq_step]| ].
 eapply c_stepstarn;[eapply stmt_step;[reflexivity|apply sskip_step]|apply c_stepstar0].
Qed.

Theorem ECactual_wrap_and_ablation : forall br bs cs,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->exists M Mf,
 V293_local_steps(pumerge CPpo CGempty)(curs CPfullbody,(kenil,kstop))
 (QPge br,V293_cpu_lenv 120%Z bs,allocb(QPmemory br 1 1)bs 0%Z 4,
 (fun _=>false),(false,nil,cs))
 (curs ECbranch,(kenil,kseq(sprim excrit)(kseq sret kstop)))
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs)) /\
 cstepstar(pumerge CPpo CGempty)
 (curs ECbranch,(kenil,kseq(sprim excrit)(kseq sret kstop)))(QPge br,V293_cpu_lenv 120%Z bs,M)
 (curs(V293_interrupt_handoff 103%Z 108%Z 106%Z),(kenil,kseq(sprim excrit)(kseq sret kstop)))
 (QPge br,V293_cpu_lenv 120%Z bs,Mf) /\
 load Tint32 M(95%positive,0%Z)=Some(Vint32 Int.mone) /\
 load Tint32 Mf(95%positive,0%Z)=Some(Vint32 Int.zero) /\
 cstepstar(pumerge CPpo CGempty)
 (curs(sif(V293_OSSched_different 103%Z 108%Z)
 (sseq(sskip None)(V293_interrupt_handoff 103%Z 108%Z 106%Z))(sskip None)),
 (kenil,kseq(sprim excrit)(kseq sret kstop)))(QPge br,V293_cpu_lenv 120%Z bs,M)
 (curs(V293_interrupt_handoff 103%Z 108%Z 106%Z),(kenil,kseq(sprim excrit)(kseq sret kstop)))
 (QPge br,V293_cpu_lenv 120%Z bs,M).
Proof.
 intros br bs cs FR FS.
 destruct(ECfixed_prefix br bs cs FR FS)as(M&Prefix&Held).
 assert(Counter:(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),
 RIabstract OwnershipWaiting,spec_done None)|=
 V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **Atrue)
 by(unfold ECpre,ECrest_raw in Held;sep auto).
 assert(High:load Tint8 M(91%positive,0%Z)=Some(V293_byteval 4)).
 { eapply V293_record_star_load_l with
 (s:=(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),RIabstract OwnershipWaiting,spec_done None))
 (P:=V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - clear -Held;unfold ECpre in Held;sep auto. }
 assert(Cache:load Tint8 M(94%positive,0%Z)=Some(V293_byteval 6)).
 { eapply V293_record_star_load_l with
 (s:=(QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),RIabstract OwnershipWaiting,spec_done None))
 (P:=V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - clear -Held;unfold ECpre in Held;sep auto. }
 assert(HN:get(V293_cpu_lenv 120%Z bs)103%Z=None)
 by(unfold V293_cpu_lenv;rewrite map_get_set' by discriminate;apply map_emp_get).
 assert(CN:get(V293_cpu_lenv 120%Z bs)108%Z=None)
 by(unfold V293_cpu_lenv;rewrite map_get_set' by discriminate;apply map_emp_get).
 assert(NN:get(V293_cpu_lenv 120%Z bs)109%Z=None)
 by(unfold V293_cpu_lenv;rewrite map_get_set' by discriminate;apply map_emp_get).
 destruct(V293_exit_boundary_tail(pumerge CPpo CGempty)(kseq(sprim excrit)(kseq sret kstop))
 (QPge br)(V293_cpu_lenv 120%Z bs)M(fun _=>false)(false,nil,false::cs)
 (RIabstract OwnershipWaiting)(spec_done None)Atrue
 103%Z 108%Z 109%Z(V293_interrupt_handoff 103%Z 108%Z 106%Z)
 91%positive 94%positive 95%positive 4 6 Int.mone
 ltac:(lia)ltac:(lia)ltac:(lia) HN CN NN ltac:(st_env)ltac:(st_env)ltac:(st_env)
 High Cache Counter)as(Mf&Trace&Store&After&Frame).
 assert(Wrap:Int.add Int.mone Int.one=Int.zero)by(vm_compute;apply Int.mkint_eq;reflexivity).
 rewrite Wrap in After.
 exists M;exists Mf;split;[exact Prefix| ];split;[exact Trace| ];split.
 - exact(V293_record_star_load_l _ Atrue _ _ _
    (V293_owned_record_cell_load(95%positive,0%Z)Tint32(Vint32 Int.mone)) _ Counter).
 - split.
   + exact(V293_record_star_load_l _ Atrue _ _ _
      (V293_owned_record_cell_load(95%positive,0%Z)Tint32(Vint32 Int.zero)) _ After).
   + apply ECwithout_increment.
     destruct(V293_OSSched_byte_comparison_eval(QPge br)(V293_cpu_lenv 120%Z bs)M
      103%Z 108%Z 91%positive 94%positive 4 6 ltac:(lia)ltac:(lia) HN CN
      ltac:(st_env)ltac:(st_env)High Cache)as[Guard GuardType].
     exact Guard.
Qed.

Theorem ECequal_priorities : forall P ks ge le M bh bc n,
 n<256 ->get le 103%Z=None ->get le 108%Z=None ->
 get ge 103%Z=Some(bh,Tint8) ->get ge 108%Z=Some(bc,Tint8) ->
 load Tint8 M(bh,0%Z)=Some(V293_byteval n) ->
 load Tint8 M(bc,0%Z)=Some(V293_byteval n) ->
 cstepstar P(curs ECbranch,(kenil,ks))(ge,le,M)
 (curs(sskip None),(kenil,ks))(ge,le,M).
Proof.
 intros P ks ge le M bh bc n Range HN CN HG CG High Cache.
 unfold ECbranch;apply ECequal_no_count.
 destruct(V293_OSSched_byte_comparison_eval ge le M 103%Z 108%Z bh bc n n
 Range Range HN CN HG CG High Cache)as[Guard GuardType].
 rewrite Nat.eqb_refl in Guard;exact Guard.
Qed.
