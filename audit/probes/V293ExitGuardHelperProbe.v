(* Full decoder ownership and two extra guards, not the old call heap. *)
Require Import CertiOS.audit.probes.V293ExitHelperTargetProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitGuardHelperTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitCriticalPrefixTaskSim.
(* Constructed helper-call cut with full decoder ownership.
   This fixture does not establish outer-entry reachability. *)
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

Require Import CertiOS.certiucos.v293.proofs.V293TimeTickCountdown.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitInterruptGlobal.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyCacheContract.
Require Import CertiOS.framework.proof.auxdef.
Require Import CertiOS.tactics.basetac.join_lib.
Require Import CertiOS.certiucos.v293.proofs.V293LocalGlobalTrace.


Require Import CertiOS.audit.probes.V293ActiveCallTraceProbe.
Require Import CertiOS.audit.probes.V293OSIntExitDispatchCallProbe.
Require Import CertiOS.audit.probes.V293OSIntExitSwitchEntryProbe.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSharedReturn.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSharedReclose.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.

Require Import CertiOS.audit.probes.V293SharedSwitchReturnProbe.
Require Import CertiOS.audit.probes.V293SwitchReturnTaskSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293StorageSwitchPre.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.proof.memory_prop.

Require CertiOS.tactics.hoareforward.symbolic_lemmas.


Require Import CertiOS.audit.probes.V293OldSwitchPacketProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InvariantPendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293StoragePendingTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293CurrentReturnInvariant.

Require Import CertiOS.certiucos.v293.proofs.V293StorageSwitchTaskSim.
Require Import CertiOS.audit.probes.V293InvariantPendingTaskSimProbe.

Require Import CertiOS.certiucos.v293.proofs.V293HandoffTaskSim.


Require Import CertiOS.certiucos.v293.proofs.V293ExitChangedTaskSim.
Require Import CertiOS.audit.probes.V293ExitChangedTaskSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitTargetTaskSim.

Require Import CertiOS.certiucos.v293.proofs.V293ExitHelperTargetTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperBodyTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefixWitness.

Require Import CertiOS.audit.probes.V293ReadyTargetHandoffProbe.
Local Open Scope nat_scope.
Definition GHge : env := set(set HTge 130%Z(150%positive,Tint8))131%Z(151%positive,Tint8).
Definition GHle := V293_cpu_lenv 120%Z 98%positive.
Section GuardHeap.
Variable n:nat.
Definition GHcells : list V293_record_cell :=
 (((150%positive,0%Z),Tint8,V293_byteval n)::
  ((151%positive,0%Z),Tint8,V293_byteval 0)::
  ((98%positive,0%Z),Tint32,Vint32 Int.zero)::
  ((94%positive,0%Z),Tint8,V293_byteval 6)::
  ((91%positive,0%Z),Tint8,V293_byteval 88)::
  ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)::
  ((95%positive,0%Z),Tint32,Vint32 Int.mone)::nil).
Definition GHoutputs := OwnershipCellsMemory GHcells.
Definition GHdecoder := V293_full_array_memory 92%positive 0%Z Tint8(map V293_byteval V293_ready_table).
Definition GHextra := merge GHoutputs GHdecoder.
Definition GHmemory := merge(RTfull OwnershipWaiting)GHextra.
Definition GHframe := V293_exit_helper_frame 92%positive 94%positive 93%positive 95%positive
 98%positive nil 6(Vint32 Int.zero)(Vptr OwnershipWaiting)Int.mone.
Definition GHresource := V293_helper_resource 80%positive 81%positive 82%positive
 92%positive 91%positive OwnershipWaiting GHframe(V293_byteval 88).
Definition GHrest := V293_array_cells 92%positive 0%Z 1%Z Tint8(length V293_ready_table)++
 [((150%positive,0%Z),Tint8);((151%positive,0%Z),Tint8)].
Definition GHinv := V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type
 (((94%positive,0%Z),Tint8)::((91%positive,0%Z),Tint8)::((95%positive,0%Z),Tint32)::GHrest).
Lemma GHextra_join : join GHoutputs GHdecoder GHextra.
Proof.
 apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 92%positive)as[E|NE].
 - subst b;left;unfold GHoutputs;apply OwnershipCellsOutside;vm_compute;intuition congruence.
 - right;left;apply V293_full_array_outside;left;exact NE.
Qed.
Lemma GHjoin : join(RTfull OwnershipWaiting)GHextra GHmemory.
Proof.
 apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 92%positive)as[E|N92].
 - subst b;left;apply RToutside;discriminate.
 - destruct(in_dec Pos.eq_dec b [150%positive;151%positive;98%positive;94%positive;91%positive;93%positive;95%positive])as[E|NE].
   + left;repeat destruct E as[<-|E];try(apply RToutside;discriminate);contradiction.
   + right;left;unfold GHextra;rewrite map_merge_semp by reflexivity.
     unfold GHoutputs;rewrite OwnershipCellsOutside by (vm_compute in NE|-*;intuition congruence).
     assert(Empty:get GHdecoder(b,i)=None).
     { unfold GHdecoder;apply V293_full_array_outside;left;exact N92. }
     change(match get GHdecoder(b,i) with Some v=>Some v|None=>None end=None).
     rewrite Empty;reflexivity.
Qed.
Lemma GHbase : n<256 ->V293_target_wstate GHge GHle GHmemory(RIabstract OwnershipWaiting)|=V293_exit_guard_resource 150%positive 151%positive n GHresource.
Proof.
 intro Range.
 assert(Outputs:V293_target_wstate GHge GHle GHoutputs emp|=V293_owned_record_cells GHcells).
 { apply OwnershipCellsSpatial;[vm_compute;repeat split;intros;intuition congruence|
   constructor;[apply V293_byte_type;exact Range|repeat constructor;vm_compute;reflexivity]]. }
 assert(Decoder:V293_target_wstate GHge GHle GHdecoder emp|=
 V293_read_bytes 92%positive 0%Z V293_ready_table **V293_read_bytes 92%positive 0%Z V293_ready_table).
 { rewrite !V293_read_bytes_array;apply V293_array_borrow.
   pose proof(V293_full_array_witness(map V293_byteval V293_ready_table)GHge GHle 92%positive 0%Z Tint8)as H.
   exact H. }
 assert(Extra:V293_target_wstate GHge GHle GHextra emp|=
 V293_owned_record_cells GHcells **
 (V293_read_bytes 92%positive 0%Z V293_ready_table **V293_read_bytes 92%positive 0%Z V293_ready_table)).
 { eapply V293_target_wstate_star;[exact GHextra_join|apply map_join_emp|exact Outputs|exact Decoder]. }
 assert(Ready:V293_target_wstate GHge GHle(RTfull OwnershipWaiting)(RIabstract OwnershipWaiting)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting).
 { apply RTenv_spatial;reflexivity. }
 assert(All:V293_target_wstate GHge GHle GHmemory(RIabstract OwnershipWaiting)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cells GHcells **
 (V293_read_bytes 92%positive 0%Z V293_ready_table **V293_read_bytes 92%positive 0%Z V293_ready_table))).
 { eapply V293_target_wstate_star;[exact GHjoin|apply map_join_emp|exact Ready|exact Extra]. }
 unfold V293_exit_guard_resource,GHresource,V293_helper_resource,GHframe,V293_exit_helper_frame.
 cbn[GHcells V293_owned_record_cells V293_storage]in All|-*.
 unfold V293_owned_record_cell in All|-*;clear -All;sep auto.
Qed.
End GuardHeap.

Definition GHcritical:=sseq(sprim encrit)
 (sseq(V293_OSIntExit_nesting_dispatch 130%Z 131%Z
 (V293_exit_boundary_dispatch 105%Z 103%Z 106%Z 108%Z 109%Z 107%Z
 (V293_interrupt_handoff 103%Z 108%Z 106%Z)))(sprim excrit)).
Theorem GHnonempty_critical_cut : forall n ip A,
 n<=1 ->getsched(RCprogram,A)=V293_scheduler ->
 TaskSim(RCprogram,(CPpo,CGempty,ip))(curs GHcritical,(kenil,kseq sret CPcall))
 (GHge,GHle,GHmemory n,(fun _=>false),(false,nil,nil))
 (RCprogram,A)(curs(hapi_code(spec_seq sched(spec_done None))),(kenil,kstop))
 (RIabstract OwnershipWaiting)V293_shared_li GHinv
 (fun st=>satp(fst st)(snd st)(RDYINV GHinv OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.
Proof.
 intros n ip A Bound Sched;unfold GHcritical,GHinv,GHrest,CPcall,GHle.
 eapply V293_exit_guard_helper_TaskSim with(nc:=6)(bc:=94%positive)(bo:=93%positive)
 (saved_value:=Vint32 Int.zero)(oldtarget:=Vptr OwnershipWaiting)(c:=Int.mone)
 (oldhigh:=V293_byteval 88)(tasks:=OwnershipTasks)(rest:=nil)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(y:=104%Z).
 - exact Sched.
 - exact RPbinding.
 - right;right;reflexivity.
 - vm_compute;reflexivity.
 - discriminate.
 - discriminate.
 - discriminate.
 - discriminate.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - exact(RIfixed_tasks OwnershipWaiting).
 - split;[lia|exists(wait(os_stat_sem(72%positive,Int.repr 5))Int.one);exists(Vptr(120%positive,Int.repr 7));reflexivity].
 - intros(p&m&Task&Minimum);vm_compute in Task;discriminate.
 - exact Bound.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - apply GHbase;lia.
Qed.

(* Delete only full-write permission on the nesting byte. Both reads still
   succeed; the very same decrement value cannot be stored with read share. *)
Definition GHone permission:mem:=sig(150%positive,0%Z)(permission,Byte(Byte.repr 1)).
Theorem GHguard_permission_control :
 load Tint8(GHone false)(150%positive,0%Z)=Some(V293_byteval 1) /\
 load Tint8(GHone true)(150%positive,0%Z)=Some(V293_byteval 1) /\
 store Tint8(GHone false)(150%positive,0%Z)(V293_byteval 0)=None /\
 store Tint8(GHone true)(150%positive,0%Z)(V293_byteval 0)=
 Some(sig(150%positive,0%Z)(true,Byte(Byte.repr 0))).
Proof.
 assert(Cell:forall permission,get(GHone permission)(150%positive,0%Z)=Some(permission,Byte(Byte.repr 1))).
 { intro permission;unfold GHone;apply map_get_sig. }
 repeat split.
 - change(match loadbytes(GHone false)(150%positive,0%Z)1 with Some bs=>Some(decode_val Tint8 bs)|None=>None end=Some(V293_byteval 1)).
   cbn[loadbytes];rewrite Cell;reflexivity.
 - change(match loadbytes(GHone true)(150%positive,0%Z)1 with Some bs=>Some(decode_val Tint8 bs)|None=>None end=Some(V293_byteval 1)).
   cbn[loadbytes];rewrite Cell;reflexivity.
 - change(storebytes(GHone false)(150%positive,0%Z)(Byte(Byte.repr 0)::nil)=None).
   cbn[storebytes];rewrite Cell;reflexivity.
 - change(storebytes(GHone true)(150%positive,0%Z)(Byte(Byte.repr 0)::nil)=Some(sig(150%positive,0%Z)(true,Byte(Byte.repr 0)))).
   cbn[storebytes];rewrite Cell;unfold GHone;rewrite map_set_sig;reflexivity.
Qed.

(* Fix a real scheduler spec rather than leave its equality as a premise. *)
Definition GHspec:osspec:=((fun _=>None),(fun _=>None),V293_scheduler).
Theorem GHinstantiated_critical_cut : forall n ip,
 n<=1 ->
 TaskSim(RCprogram,(CPpo,CGempty,ip))(curs GHcritical,(kenil,kseq sret CPcall))
 (GHge,GHle,GHmemory n,(fun _=>false),(false,nil,nil))
 (RCprogram,GHspec)(curs(hapi_code(spec_seq sched(spec_done None))),(kenil,kstop))
 (RIabstract OwnershipWaiting)V293_shared_li GHinv
 (fun st=>satp(fst st)(snd st)(RDYINV GHinv OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.
Proof.
 intros n ip Bound;apply GHnonempty_critical_cut;[exact Bound|reflexivity].
Qed.

Lemma GHoriginal_critical_shape : forall running saved,
 V293_exit_boundary_body running 130%Z 131%Z saved 105%Z 103%Z 106%Z 108%Z 109%Z 107%Z
 (V293_interrupt_handoff 103%Z 108%Z 106%Z)=
 sseq(sassign(evar saved)(econst32 Int.zero))
 (sseq(sifthen(V293_OSIntEnter_running running)GHcritical)sret).
Proof. reflexivity. Qed.
