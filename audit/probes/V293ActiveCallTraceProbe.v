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
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
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
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
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
Require Import CertiOS.audit.probes.V293ReadyFullCallProbe.
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
Require Import CertiOS.certiucos.v293.proofs.V293ReadyFullCall.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCriticalGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedCurrent.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSSchedChange.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitExecution.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySchedCall.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.code.V293OSIntExit.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.code.V293OSSchedNew.
Require Import CertiOS.certiucos.v293.model.V293ReadyBitmap.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.cstepLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.

Require Import CertiOS.certiucos.v293.proofs.V293ReadySourceTail.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedPointerCompare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitInterruptGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCacheContract.
Require Import Coq.Relations.Relation_Operators.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.framework.proof.join_prop.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.certiucos.v293.proofs.V293ReadySwitchStep.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyGlobalTrace.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCallGlobal.
Require Import CertiOS.certiucos.v293.code.V293OSSchedDispatch.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.


(* The same allocated entry heap, with the outer call frame left for the
   existing local-to-global lifting theorem rather than fabricated here. *)
Lemma FTbody_prefix :
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
 (curs handoff,(kenil,
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
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32(Int.add c Int.one)) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **R)))))))) /\
 load(Tptr V293_tcb_type)Mf(bo,0%Z)=Some(Vptr next) /\
 load Tint32 Mf(bcount,0%Z)=Some(Vint32(Int.add c Int.one)) /\
 load Tint8 Mf(bc,0%Z)=Some(V293_byteval nc) /\
 (forall k,k<4 ->exists v,get Mf(bs,Z.of_nat k)=Some(true,v)) /\
 (forall block i,block<>bs ->block<>bo ->(block,i)<>(bh,0%Z) ->(block,i)<>(bn,0%Z) ->
   (block<>bcount \/(i<0)%Z \/(4<=i)%Z) ->get Mf(block,i)=get M(block,i)).
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
 destruct(V293_exit_boundary_tail P K ge le Mmid ir(false,si,enabled::ci)O op F
 high current counter handoff bh bc bcount
 (V293_ready_select lo hi(V293_ready_group lo hi))nc c ltac:(lia) NC Different
 (Names high ltac:(cbn;tauto))(Names current ltac:(cbn;tauto))(Names counter ltac:(cbn;tauto))
 GH GC GCount HighLoad CurrentLoad CounterEntry)as(Mf&Tail&CounterStore&Final&CountFrame).
 assert(Post:(ge,le,Mf,ir,(false,si,enabled::ci),O,op)|=
 SWINVt(V293_ready_inv br bg bp)ct **
 (V293_owned_record_cell((bh,0%Z),Tint8,V293_byteval(V293_ready_select lo hi(V293_ready_group lo hi))) **
 (V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next) **
 (V293_owned_record_cell((bn,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bl,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc) **
 (V293_owned_record_cell((brun,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((bcount,0%Z),Tint32,Vint32(Int.add c Int.one)) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **R))))))))).
 { unfold F in Final;clear Held Stacked Local Allocated Entry After CounterEntry;sep auto. }
 exists next;exists(V293_ready_select lo hi(V293_ready_group lo hi));exists Mf.
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
   eapply V293_local_trans;[apply V293_csteps_local;exact Middle| ].
   apply V293_csteps_local;exact Tail.
 - split;[exact Post| ];split.
   + eapply V293_record_star_load_l with(s:=(ge,le,Mf,ir,(false,si,enabled::ci),O,op))
     (P:=V293_owned_record_cell((bo,0%Z),Tptr V293_tcb_type,Vptr next))(Q:=Atrue).
     * intros st H;apply V293_owned_record_cell_load;exact H.
     * clear Held Stacked Local Allocated Entry After CounterEntry Final;sep auto.
   + split.
     * eapply V293_record_star_load_l with(s:=(ge,le,Mf,ir,(false,si,enabled::ci),O,op))
       (P:=V293_owned_record_cell((bcount,0%Z),Tint32,Vint32(Int.add c Int.one)))(Q:=F).
       -- intros st H;apply V293_owned_record_cell_load;exact H.
       -- exact Final.
     * split.
       -- eapply V293_record_star_load_l with(s:=(ge,le,Mf,ir,(false,si,enabled::ci),O,op))
          (P:=V293_owned_record_cell((bc,0%Z),Tint8,V293_byteval nc))(Q:=Atrue).
          ++ intros st H;apply V293_owned_record_cell_load;exact H.
          ++ clear Held Stacked Local Allocated Entry After CounterEntry Final;sep auto.
       -- split.
          ++ assert(SavedCell:(ge,le,Mf,ir,(false,si,enabled::ci),O,op)|=Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Atrue).
             { clear Held Stacked Local Allocated Entry After CounterEntry Final;sep auto. }
             intros k Bound.
             pose proof(V293_tick_raw_owned_writable bs Tint32 (Vint32 Int.zero) _ _ _ _ _ _ _ _ SavedCell)as W.
             apply W;cbn;lia.
          ++ intros block i NS NO NH NN Outside;rewrite CountFrame by exact Outside.
             rewrite MidFrame by assumption;apply InitFrame;exact NS.
Qed.

Definition FTrest br bs : asrt :=
 V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((97%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((br,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.zero) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **RCframe))))).
Definition FTpre_copy br bs : asrt :=
 SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) ** FTrest br bs))).
Definition FTafter_copy br bs ct : asrt :=
 SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)ct **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) ** FTrest br bs))).

Local Ltac ft_env := unfold QPge;rewrite map_get_set' by discriminate;reflexivity.

Lemma FTfixed_prefix : forall br bs cs,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->
 exists M,
 V293_local_steps(pumerge CPpo CGempty)
 (curs CPfullbody,(kenil,kstop))
 ((QPge br,V293_cpu_lenv 120%Z bs,allocb(QPmemory br 1 1)bs 0%Z 4),(fun _=>false),(false,nil,cs))
 (curs(V293_interrupt_handoff 103%Z 108%Z 106%Z),(kenil,kseq(sprim excrit)(kseq sret kstop)))
 ((QPge br,V293_cpu_lenv 120%Z bs,M),(fun _=>false),(false,nil,false::cs)) /\
 (QPge br,V293_cpu_lenv 120%Z bs,M,(fun _=>false),(false,nil,false::cs),RIabstract OwnershipWaiting,spec_done None)|=FTpre_copy br bs.
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
 destruct(FTbody_prefix 80%positive 81%positive 82%positive(pumerge CPpo CGempty)
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
 ltac:(ft_env)ltac:(ft_env)ltac:(ft_env)ltac:(ft_env)ltac:(ft_env)ltac:(ft_env)
 ltac:(ft_env)ltac:(ft_env)ltac:(unfold QPge;apply map_get_set)ltac:(ft_env)ltac:(ft_env)
 (RIfixed_tasks OwnershipWaiting)Current NotHighest ltac:(split;[exact I|apply RCframe_good])Lookup Entry)
 as(next&nh&M&Different&PrioDifferent&Highest&Next&Trace&Post&Target&Count&Cache&Alive&Frame).
 destruct Next as[Range[st[msg Task]]].
 destruct Highest as[p[m[Ready Minimum]]].
 change(get OwnershipTasks next=Some(p,rdy,m))in Ready.
 rewrite Task in Ready;inversion Ready;subst st.
 destruct(RTonly_ready nh next msg Range Task)as[Priority[Selected Message]].
 subst nh next.
 assert(Wrap:Int.add Int.mone Int.one=Int.zero)by(vm_compute;apply Int.mkint_eq;reflexivity).
 rewrite Wrap in Post.
 exists M;split;[exact Trace| ]. unfold FTpre_copy,FTrest.
 clear -Post;sep auto.
Qed.
Lemma FTenter : forall br bs cs ncs ip,
 fresh(QPmemory br 1 1)bs ->
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (V293_local_global_at FWtasks RPenvs(RPaux cs ncs)OwnershipWaiting
 (curs CPfullbody,(kenil,CPcall))
 ((QPge br,V293_cpu_lenv 120%Z bs,allocb(QPmemory br 1 1)bs 0%Z 4),(fun _=>false),(false,nil,cs))).
Proof.
 intros br bs cs ncs ip Fresh.
 assert(Bind:=RPbinding).
 assert(Program:pumerge CPpo CGempty 114%Z=Some(Tvoid,dnil,dcons 120%Z Tint32 dnil,CPfullbody)).
 { unfold pumerge;rewrite Bind;reflexivity. }
 assert(Start:V293_local_global_at FWtasks RPenvs(RPaux cs ncs)OwnershipWaiting
 (curs(sfexec 114%Z nil nil),(kenil,kstop))
 ((QPge br,(emp:env),QPmemory br 1 1),(fun _=>false),(false,nil,cs))=
 (FWtasks,FWos br cs ncs,OwnershipWaiting)).
 { cbn[V293_local_global_at V293_global_at]. unfold FWos.
   assert(TC:set FWtasks OwnershipWaiting(curs(sfexec 114%Z nil nil),(kenil,kstop))=FWtasks).
   { apply get_set_same;unfold FWtasks;apply map_get_set. }
   assert(EC:set RPenvs OwnershipWaiting(emp:env)=RPenvs).
   { apply get_set_same;unfold RPenvs;apply map_get_set. }
   assert(AC:set(RPaux cs ncs)OwnershipWaiting(false,nil,cs)=RPaux cs ncs).
   { apply get_set_same;unfold RPaux;apply map_get_set. }
   change((set FWtasks OwnershipWaiting(curs(sfexec 114%Z nil nil),(kenil,kstop)),
   (QPge br,set RPenvs OwnershipWaiting(emp:env),QPmemory br 1 1,((fun _=>false):isr),
   set(RPaux cs ncs)OwnershipWaiting(false,nil,cs)),OwnershipWaiting)=
   (FWtasks,(QPge br,RPenvs,QPmemory br 1 1,((fun _=>false):isr),RPaux cs ncs),OwnershipWaiting)).
   rewrite TC,EC,AC;reflexivity. }
 rewrite <-Start.
 eapply V293_global_trans with(b:=V293_local_global_at FWtasks RPenvs(RPaux cs ncs)OwnershipWaiting
 (curs(salloc nil(dcons 120%Z Tint32 dnil)),(kenil,CPcall))
 ((QPge br,(emp:env),QPmemory br 1 1),(fun _=>false),(false,nil,cs))).
 - apply V293_loststep_global_single.
   + exists(curs(sfexec 114%Z nil nil));exists kenil;exists kstop;split;[reflexivity|left].
     exists 114%Z;exists(@nil val);exists(Tvoid,dnil,dcons 120%Z Tint32 dnil,CPfullbody).
     exists(@nil type);split;[reflexivity|exact Program].
   + apply ostc_step;eapply stmt_step;[reflexivity| ].
     eapply sfexec_step with(d1:=dnil)(d2:=dcons 120%Z Tint32 dnil);
     [reflexivity|reflexivity|exact Program|exact I|reflexivity].
 - eapply V293_global_trans with(b:=V293_local_global_at FWtasks RPenvs(RPaux cs ncs)OwnershipWaiting
   (curs(salloc nil dnil),(kenil,CPcall))
   ((QPge br,V293_cpu_lenv 120%Z bs,allocb(QPmemory br 1 1)bs 0%Z 4),(fun _=>false),(false,nil,cs))).
   + apply V293_loststep_global_single.
     * eapply V293_bound_call_inos;exact Bind.
     * apply ostc_step;eapply stmt_step;[reflexivity| ].
       eapply salloclv_step;[reflexivity|reflexivity| ];exists bs.
       split;[exact Fresh| ];split;[reflexivity| ];split.
       -- intros[v E];rewrite map_emp_get in E;discriminate.
       -- reflexivity.
   + apply V293_loststep_global_single.
     * eapply V293_bound_call_inos;exact Bind.
     * apply ostc_step;eapply stmt_step;[reflexivity|apply sallocend_step].
Qed.

Definition FTpending : stmtcont := kseq(sprim excrit)(kseq sret CPcall).
Definition FTsuspended : tasks := set FWtasks OwnershipWaiting RPpending.
Definition FTreturned : tasks := set FTsuspended OwnershipReady(SKIP,(kenil,kstop)).
Definition FTenvs bs : cltenvs := set RPenvs OwnershipWaiting(V293_cpu_lenv 120%Z bs).
Definition FTaux cs ncs : ltaskstset := set(RPaux cs ncs)OwnershipWaiting(false,nil,false::cs).
Definition FTreturnstate br bs M cs ncs : osstate :=
 (QPge br,set(FTenvs bs)OwnershipReady(emp:env),M,(fun _=>false),
 set(FTaux cs ncs)OwnershipReady(false,nil,ncs)).

Lemma FTto_switch : forall br bs cs ncs ip,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->
 exists Mc,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (set FWtasks OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,FTpending)),
 (QPge br,FTenvs bs,Mc,(fun _=>false),FTaux cs ncs),OwnershipWaiting) /\
 (QPge br,V293_cpu_lenv 120%Z bs,Mc,(fun _=>false),(false,nil,false::cs),RIabstract OwnershipWaiting,spec_done None)|=
 FTafter_copy br bs OwnershipWaiting.
Proof.
 intros br bs cs ncs ip FR FS.
 destruct(FTfixed_prefix br bs cs FR FS)as(M&Prefix&Held).
 destruct(V293_handoff_copy_execution 80%positive 81%positive 82%positive
 (pumerge CPpo CGempty)(kseq(sprim excrit)(kseq sret kstop))
 (QPge br)(V293_cpu_lenv 120%Z bs)M(fun _=>false)(false,nil,false::cs)
 (RIabstract OwnershipWaiting)(spec_done None)OwnershipWaiting(FTrest br bs)
 103%Z 108%Z 106%Z 91%positive 94%positive 93%positive 4 6 OwnershipReady
 ltac:(lia)ltac:(unfold V293_cpu_lenv;rewrite map_get_set' by discriminate;apply map_emp_get)
 ltac:(unfold V293_cpu_lenv;rewrite map_get_set' by discriminate;apply map_emp_get)
 ltac:(ft_env)ltac:(ft_env)Held)as(Mc&Copy&Store&After&Frame).
 assert(Local:V293_local_steps(pumerge CPpo CGempty)
 (curs CPfullbody,(kenil,kstop))
 ((QPge br,V293_cpu_lenv 120%Z bs,allocb(QPmemory br 1 1)bs 0%Z 4),(fun _=>false),(false,nil,cs))
 (curs(sprim(switch 106%Z)),(kenil,kseq(sprim excrit)(kseq sret kstop)))
 ((QPge br,V293_cpu_lenv 120%Z bs,Mc),(fun _=>false),(false,nil,false::cs))).
 { eapply V293_local_trans;[exact Prefix|apply V293_csteps_local;exact Copy]. }
 pose proof(V293_local_steps_global RCprogram CPpo CGempty ip _ _ _ _ Local
 114%Z CPfullbody(emp:env)kstop Tvoid dnil(dcons 120%Z Tint32 dnil)
 FWtasks RPenvs(RPaux cs ncs)OwnershipWaiting HPcst RPbinding
 ltac:(change(goodks(RCprogram,(CPpo,CGempty,ip))CPcall);unfold CPcall;cbn[goodks];unfold pumerge;rewrite RPbinding;exact I))as Global.
 cbn[V293_enclose AddKsToTail]in Global.
 exists Mc;split;[ |exact After].
 eapply V293_global_trans;[apply FTenter;exact FS|exact Global].
Qed.
Lemma FTsaved_load : forall b ge le M ir aux O op,
 (ge,le,M,ir,aux,O,op)|=Amapsto(b,0%Z)Tint32 true(Vint32 Int.zero) **Atrue ->
 load Tint32 M(b,0%Z)=Some(Vint32 Int.zero).
Proof.
 intros b ge le M ir aux O op Held.
 eapply V293_record_star_load_l with(s:=(ge,le,M,ir,aux,O,op))
 (P:=Amapsto(b,0%Z)Tint32 true(Vint32 Int.zero))(Q:=Atrue).
 - intros st Cell;apply V293_owned_record_cell_load.
   unfold V293_owned_record_cell;apply astar_l_apure_intro;[exact Cell|reflexivity].
 - exact Held.
Qed.

Theorem FTfinite_call : forall br bs cs ncs ip,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->
 exists Msw Mret,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (FTreturned,FTreturnstate br bs Mret cs ncs,OwnershipReady) /\
 free Tint32 98%positive Msw=Some Mret /\
 (forall i,(0<=i<4)%Z ->get Mret(98%positive,i)=None) /\
 load Tint32 Mret(bs,0%Z)=Some(Vint32 Int.zero) /\
 load Tint8 Mret(94%positive,0%Z)=Some(V293_byteval 4) /\
 load Tint32 Mret(95%positive,0%Z)=Some(Vint32 Int.zero) /\
 load(Tptr V293_tcb_type)Mret(1%positive,0%Z)=Some(Vptr OwnershipReady) /\
 load Tint8 Mret(96%positive,0%Z)=Some(V293_byteval 0) /\
 load Tint8 Mret(br,0%Z)=Some(V293_byteval 1).
Proof.
 intros br bs cs ncs ip FR FS.
 destruct(FTto_switch br bs cs ncs ip FR FS)as(Mc&Prefix&Held).
 assert(Target:load(Tptr V293_tcb_type)Mc(93%positive,0%Z)=Some(Vptr OwnershipReady)).
 { eapply V293_record_star_load_l with
 (s:=(QPge br,V293_cpu_lenv 120%Z bs,Mc,(fun _=>false),(false,nil,false::cs),RIabstract OwnershipWaiting,spec_done None))
 (P:=V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - unfold FTafter_copy in Held;sep auto. }
 destruct(V293_ready_switch_step 80%positive 81%positive 82%positive
 RCprogram CPpo CGempty ip
 (set FWtasks OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,FTpending)))HPcst FTpending
 OwnershipWaiting OwnershipReady 106%Z 93%positive 1%positive
 (QPge br)(V293_cpu_lenv 120%Z bs)(FTenvs bs)Mc(fun _=>false)(false,nil,false::cs)
 (FTaux cs ncs)(RIabstract OwnershipWaiting)(spec_done None)
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **FTrest br bs)))
 V293_tcb_type ltac:(unfold FTenvs;apply map_get_set)ltac:(unfold FTaux;apply map_get_set)
 ltac:(apply map_get_set)ltac:(ft_env)Target ltac:(ft_env)Held)
 as(Msw&Switch&Store&Post&Current&OldCode&Others&Outside).
 assert(TMerge:set(set FWtasks OwnershipWaiting(curs(sprim(switch 106%Z)),(kenil,FTpending)))
 OwnershipWaiting(SKIP,(kenil,FTpending))=FTsuspended).
 { unfold FTsuspended,RPpending,FTpending;symmetry;apply set_set_eq. }
 rewrite TMerge in Switch.
 assert(NextCode:get FTsuspended OwnershipReady=Some RPpending).
 { unfold FTsuspended,FWtasks,RPtasks;repeat rewrite map_get_set' by discriminate;apply map_get_sig. }
 assert(NextEnv:get(FTenvs bs)OwnershipReady=Some(V293_cpu_lenv 120%Z 98%positive)).
 { unfold FTenvs,RPenvs;repeat rewrite map_get_set' by discriminate;apply map_get_sig. }
 assert(NextAux:get(FTaux cs ncs)OwnershipReady=Some(false,nil,false::ncs)).
 { unfold FTaux,RPaux;repeat rewrite map_get_set' by discriminate;apply map_get_sig. }
 assert(Saved:(QPge br,V293_cpu_lenv 120%Z 98%positive,Msw,(fun _=>false),(false,nil,false::ncs),SPOf,spec_done None)|=
 Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Atrue)).
 { unfold SPOf;eapply good_inv_prop with(le:=V293_cpu_lenv 120%Z bs)(ie:=false)(cs:=false::cs)(op:=spec_done None);
   [repeat split;exact I| ]. unfold FTrest in Post;clear -Post;sep auto. }
 destruct(V293_int_exit_pending_return RCprogram CPpo CGempty ip FTsuspended
 (FTenvs bs)(FTaux cs ncs)OwnershipReady HPcst(QPge br)Msw(fun _=>false)
 false false nil ncs SPOf(spec_done None)
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **Atrue)
 114%Z CPfullbody(emp:env)kstop Tvoid dnil(dcons 120%Z Tint32 dnil)120%Z 98%positive(Vint32 Int.zero)
 RPbinding ltac:(split;exact I)NextCode NextEnv NextAux Saved)
 as(Mret&Return&Free&Rest&Removed&Frame).
 exists Msw;exists Mret;split.
 - eapply V293_global_trans;[exact Prefix| ].
   unfold V293_global_steps;eapply rt1n_trans with(y:=
   (FTsuspended,(QPge br,FTenvs bs,Msw,((fun _=>false):isr),FTaux cs ncs),OwnershipReady));
   [exact Switch|exact Return].
 - split;[exact Free| ];split;[exact Removed| ];split.
   + eapply FTsaved_load;exact Rest.
   + assert(Loads:
     load Tint8 Msw(94%positive,0%Z)=Some(V293_byteval 4) /\
     load Tint32 Msw(95%positive,0%Z)=Some(Vint32 Int.zero) /\
     load Tint8 Msw(96%positive,0%Z)=Some(V293_byteval 0) /\
     load Tint8 Msw(br,0%Z)=Some(V293_byteval 1)).
     { repeat split;eapply V293_record_star_load_l with
       (s:=(QPge br,V293_cpu_lenv 120%Z bs,Msw,(fun _=>false),(false,nil,false::cs),set(RIabstract OwnershipWaiting)curtid(oscurt OwnershipReady),spec_done None))
       (Q:=Atrue);try(intros st H;apply V293_owned_record_cell_load;exact H);
       unfold FTrest in Post;clear -Post;sep auto. }
     destruct Loads as[Cache[Counter[Nesting Running]]].
     assert(RunningApart:br<>98%positive).
     { pose proof(CPtyped_updated 1 nil ltac:(lia))as BaseOwned.
       assert(Cell:CGstate OwnershipWaiting(NPinitial 1)nil|=
       Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **Atrue).
       { unfold CPother,V293_owned_record_cell in BaseOwned;clear -BaseOwned;sep auto. }
       destruct(V293_tick_raw_owned_writable 98%positive Tint32(Vint32 Int.zero)
       _ _ _ _ _ _ _ _ Cell 0 ltac:(cbn;lia))as(v&Byte).
       eapply FWfresh_present;[exact FR|exact Byte]. }
     split.
     * etransitivity;[apply V293_load_block_frame;intro i;apply Frame;discriminate|exact Cache].
     * split.
       -- etransitivity;[apply V293_load_block_frame;intro i;apply Frame;discriminate|exact Counter].
       -- split.
          ++ etransitivity;[apply V293_load_block_frame;intro i;apply Frame;discriminate|exact Current].
          ++ split.
             ** etransitivity;[apply V293_load_block_frame;intro i;apply Frame;discriminate|exact Nesting].
             ** etransitivity;[apply V293_load_block_frame;intro i;apply Frame;exact RunningApart|exact Running].
Qed.

Theorem FTendpoint_metadata : forall bs cs ncs,
 get FTreturned OwnershipWaiting=Some RPpending /\
 get FTreturned OwnershipReady=Some(SKIP,(kenil,kstop)) /\
 get(set(FTenvs bs)OwnershipReady(emp:env))OwnershipWaiting=
 Some(V293_cpu_lenv 120%Z bs) /\
 get(set(FTenvs bs)OwnershipReady(emp:env))OwnershipReady=Some(emp:env) /\
 get(set(FTaux cs ncs)OwnershipReady(false,nil,ncs))OwnershipWaiting=
 Some(false,nil,false::cs) /\
 get(set(FTaux cs ncs)OwnershipReady(false,nil,ncs))OwnershipReady=
 Some(false,nil,ncs).
Proof.
 intros bs cs ncs;unfold FTreturned,FTsuspended,FTenvs,FTaux.
 repeat split;repeat rewrite map_get_set' by discriminate;apply map_get_set.
Qed.

Theorem FTsame_entry : forall br bs cs ncs ip,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->
 ProgSim(RCprogram,(CPpo,CGempty,ip))FWtasks(FWos br cs ncs)
 SPph HPTh(RIabstract OwnershipWaiting)HPcst OwnershipWaiting /\
 exists Mret,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (FTreturned,FTreturnstate br bs Mret cs ncs,OwnershipReady) /\
 load Tint32 Mret(bs,0%Z)=Some(Vint32 Int.zero) /\
 (forall i,(0<=i<4)%Z ->get Mret(98%positive,i)=None).
Proof.
 intros br bs cs ncs ip FR FS;split.
 - apply FWcomplete_active_simulation;exact FR.
 - destruct(FTfinite_call br bs cs ncs ip FR FS)
   as(Msw&Mret&Trace&Free&Removed&Saved&Reads).
   exists Mret;split;[exact Trace| ];split;[exact Saved|exact Removed].
Qed.

Theorem FTnonvacuous : exists br bs,
 fresh(NPinitial 1)br /\fresh(QPmemory br 1 1)bs /\
 forall cs ncs ip,
 ProgSim(RCprogram,(CPpo,CGempty,ip))FWtasks(FWos br cs ncs)
 SPph HPTh(RIabstract OwnershipWaiting)HPcst OwnershipWaiting /\
 exists Mret,
 V293_global_steps(RCprogram,(CPpo,CGempty,ip))HPcst
 (FWtasks,FWos br cs ncs,OwnershipWaiting)
 (FTreturned,FTreturnstate br bs Mret cs ncs,OwnershipReady) /\
 load Tint32 Mret(bs,0%Z)=Some(Vint32 Int.zero) /\
 (forall i,(0<=i<4)%Z ->get Mret(98%positive,i)=None).
Proof.
 destruct(memory_has_fresh_block(NPinitial 1))as[br FR].
 destruct(memory_has_fresh_block(QPmemory br 1 1))as[bs FS].
 exists br;exists bs;split;[exact FR| ];split;[exact FS| ].
 intros cs ncs ip;apply FTsame_entry;assumption.
Qed.
