(* Independent nonempty API-entry heap; no preallocated saved local. *)
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
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.

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
Require Import CertiOS.certiucos.v293.proofs.V293ExitActiveCallTaskSim.
Require Import CertiOS.audit.probes.V293ExitGuardHelperProbe.
Require Import CertiOS.framework.proof.memory_prop.
Require Import CertiOS.tactics.hoareforward.symbolic_lemmas.
Import ListNotations.
Local Open Scope nat_scope.
Import ListNotations.
Local Open Scope list_scope.
Definition ACge : env := set GHge 132%Z(152%positive,Tint8).
Definition ACle : env := emp.
Section ActiveHeap.
Variable n:nat.
Definition ACcells : list V293_record_cell :=
 (((150%positive,0%Z),Tint8,V293_byteval n)::
  ((151%positive,0%Z),Tint8,V293_byteval 0)::
  ((152%positive,0%Z),Tint8,V293_byteval 1)::
  ((94%positive,0%Z),Tint8,V293_byteval 6)::
  ((91%positive,0%Z),Tint8,V293_byteval 88)::
  ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)::
  ((95%positive,0%Z),Tint32,Vint32 Int.mone)::nil).
Definition ACoutputs := OwnershipCellsMemory ACcells.
Definition ACdecoder := V293_full_array_memory 92%positive 0%Z Tint8(map V293_byteval V293_ready_table).
Definition ACextra := merge ACoutputs ACdecoder.
Definition ACmemory := merge(RTfull OwnershipWaiting)ACextra.
Definition ACresource := V293_exit_active_resource 80%positive 81%positive 82%positive
 92%positive 94%positive 91%positive 93%positive 95%positive 150%positive 151%positive 152%positive
 nil OwnershipWaiting 6(Vptr OwnershipWaiting)Int.mone n(V293_byteval 88).
Lemma ACextra_join : join ACoutputs ACdecoder ACextra.
Proof.
 apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 92%positive)as[E|NE].
 - subst b;left;unfold ACoutputs;apply OwnershipCellsOutside;vm_compute;intuition congruence.
 - right;left;apply V293_full_array_outside;left;exact NE.
Qed.
Lemma ACjoin : join(RTfull OwnershipWaiting)ACextra ACmemory.
Proof.
 apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 92%positive)as[E|N92].
 - subst b;left;apply RToutside;discriminate.
 - destruct(in_dec Pos.eq_dec b [150%positive;151%positive;152%positive;94%positive;91%positive;93%positive;95%positive])as[E|NE].
   + left;repeat destruct E as[<-|E];try(apply RToutside;discriminate);contradiction.
   + right;left;unfold ACextra;rewrite map_merge_semp by reflexivity.
     unfold ACoutputs;rewrite OwnershipCellsOutside by (vm_compute in NE|-*;intuition congruence).
     assert(Empty:get ACdecoder(b,i)=None).
     { unfold ACdecoder;apply V293_full_array_outside;left;exact N92. }
     change(match get ACdecoder(b,i) with Some v=>Some v|None=>None end=None).
     rewrite Empty;reflexivity.
Qed.
Lemma ACbase : n<256 ->V293_target_wstate ACge ACle ACmemory(RIabstract OwnershipWaiting)|=ACresource.
Proof.
 intro Range.
 assert(Outputs:V293_target_wstate ACge ACle ACoutputs emp|=V293_owned_record_cells ACcells).
 { apply OwnershipCellsSpatial;[vm_compute;repeat split;intros;intuition congruence|
   constructor;[apply V293_byte_type;exact Range|repeat constructor;vm_compute;reflexivity]]. }
 assert(Decoder:V293_target_wstate ACge ACle ACdecoder emp|=
 V293_read_bytes 92%positive 0%Z V293_ready_table **V293_read_bytes 92%positive 0%Z V293_ready_table).
 { rewrite !V293_read_bytes_array;apply V293_array_borrow.
   pose proof(V293_full_array_witness(map V293_byteval V293_ready_table)ACge ACle 92%positive 0%Z Tint8)as H.
   exact H. }
 assert(Extra:V293_target_wstate ACge ACle ACextra emp|=
 V293_owned_record_cells ACcells **
 (V293_read_bytes 92%positive 0%Z V293_ready_table **V293_read_bytes 92%positive 0%Z V293_ready_table)).
 { eapply V293_target_wstate_star;[exact ACextra_join|apply map_join_emp|exact Outputs|exact Decoder]. }
 assert(Ready:V293_target_wstate ACge ACle(RTfull OwnershipWaiting)(RIabstract OwnershipWaiting)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting).
 { apply RTenv_spatial;reflexivity. }
 assert(All:V293_target_wstate ACge ACle ACmemory(RIabstract OwnershipWaiting)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cells ACcells **
 (V293_read_bytes 92%positive 0%Z V293_ready_table **V293_read_bytes 92%positive 0%Z V293_ready_table))).
 { eapply V293_target_wstate_star;[exact ACjoin|apply map_join_emp|exact Ready|exact Extra]. }
 unfold ACresource,V293_exit_active_resource,V293_exit_guard_resource,V293_helper_resource,V293_exit_active_frame.
 cbn[ACcells V293_owned_record_cells V293_storage]in All|-*.
 unfold V293_owned_record_cell in All|-*;clear -All;sep auto.
Qed.
End ActiveHeap.
Definition ACrest := V293_array_cells 92%positive 0%Z 1%Z Tint8(length V293_ready_table)++
 [((150%positive,0%Z),Tint8);((151%positive,0%Z),Tint8);((152%positive,0%Z),Tint8)].
Definition ACinv := V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type
 (((94%positive,0%Z),Tint8)::((91%positive,0%Z),Tint8)::((95%positive,0%Z),Tint32)::ACrest).
Definition ACbody := V293_exit_boundary_body 132%Z 130%Z 131%Z 120%Z
 105%Z 103%Z 106%Z 108%Z 109%Z 107%Z(V293_interrupt_handoff 103%Z 108%Z 106%Z).
Definition ACpo:progunit:=fun f=>if Z.eq_dec f 114%Z then Some
 (V293_exit_boundary_function 132%Z 130%Z 131%Z 120%Z
 105%Z 103%Z 106%Z 108%Z 109%Z 107%Z(V293_interrupt_handoff 103%Z 108%Z 106%Z))else CGpo f.
Theorem ACnonempty_API_entry : forall n ip,
 n<=1 ->
 TaskSim(RCprogram,(ACpo,CGempty,ip))(curs(sfexec 114%Z nil nil),(kenil,kstop))
 (ACge,ACle,ACmemory n,(fun _=>false),(false,nil,nil))
 (RCprogram,GHspec)(curs(hapi_code(spec_seq sched(spec_done None))),(kenil,kstop))
 (RIabstract OwnershipWaiting)V293_shared_li ACinv
 (fun st=>satp(fst st)(snd st)(RDYINV ACinv OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.
Proof.
 intros n ip Bound;unfold ACinv,ACrest,ACle.
 eapply V293_exit_active_call_TaskSim with(nc:=6)(bc:=94%positive)(bo:=93%positive)
 (oldtarget:=Vptr OwnershipWaiting)(c:=Int.mone)(oldhigh:=V293_byteval 88)
 (tasks:=OwnershipTasks)(rest:=nil)(saved:=120%Z)(helper:=107%Z)
 (running:=132%Z)(nesting:=130%Z)(lock:=131%Z)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(y:=104%Z).
 - reflexivity.
 - vm_compute;reflexivity.
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
 - discriminate.
 - discriminate.
 - discriminate.
 - discriminate.
 - discriminate.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - exact(RIfixed_tasks OwnershipWaiting).
 - split;[lia|exists(wait(os_stat_sem(72%positive,Int.repr 5))Int.one);exists(Vptr(120%positive,Int.repr 7));reflexivity].
 - intros(p&m&Task&Minimum);vm_compute in Task;discriminate.
 - exact Bound.
 - discriminate.
 - discriminate.
 - discriminate.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - apply ACbase;lia.
Qed.

Lemma ACraw_saved_read : forall b s,
 s|=Amapsto(b,0%Z)Tint32 true Vundef ->
 load Tint32(assertion.getmem s)(b,0%Z)=Some Vundef.
Proof.
 intros b s[Points Empty];unfold mapstoval in Points;destruct Points as(bytes&Encoding&Cells).
 subst bytes;pose proof(ptomvallist_loadbytes _ _ _ _ Cells)as Read.
 rewrite encode_val_length in Read;unfold load,loadm;rewrite Read;reflexivity.
Qed.

(* Omit only initialization on the identical fresh heap. No downstream run is inferred. *)
Theorem ACsaved_initialization_control : forall n b,
 n<256 ->fresh(ACmemory n)b ->exists Mz,
 load Tint32(allocb(ACmemory n)b 0%Z 4)(b,0%Z)=Some Vundef /\ store Tint32(allocb(ACmemory n)b 0%Z 4)(b,0%Z)(Vint32 Int.zero)=Some Mz /\ load Tint32 Mz(b,0%Z)=Some(Vint32 Int.zero) /\ (forall c i,c<>b ->get Mz(c,i)=get(allocb(ACmemory n)b 0%Z 4)(c,i)).
Proof.
 intros n b Range Fresh.
 pose proof(V293_tick_allocate_frame ACge ACle(ACmemory n)(fun _=>false)(false,nil,nil)
 (RIabstract OwnershipWaiting)(spec_done None)b Tint32(ACresource n)Fresh(ACbase n Range))as Raw.
 assert(Read:load Tint32(allocb(ACmemory n)b 0%Z 4)(b,0%Z)=Some Vundef).
 { change(load Tint32(assertion.getmem(V293_target_wstate ACge ACle
 (allocb(ACmemory n)b 0%Z 4)(RIabstract OwnershipWaiting)))(b,0%Z)=Some Vundef).
   eapply V293_record_star_load_l;[apply ACraw_saved_read|exact Raw]. }
 destruct(V293_tick_raw_slot_update(b,0%Z)Tint32 Vundef(Vint32 Int.zero)
 (ACresource n) _ _ _ _ _ _ _ eq_refl Raw)as(Mz&Store&Owned).
 exists Mz;split;[exact Read| ];split;[exact Store| ];split.
 - change(load Tint32(assertion.getmem(V293_target_wstate ACge ACle Mz(RIabstract OwnershipWaiting)))
   (b,0%Z)=Some(Vint32 Int.zero)).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Owned].
 - intros c i Ne;eapply V293_storebytes_outside;[exact Store|left;exact Ne].
Qed.

Lemma ACfresh_exists : forall n,exists b,fresh(ACmemory n)b.
Proof. intro n;apply memory_has_fresh_block. Qed.

(* Client scall is not the API-entry class; adding InOS here would be contradictory. *)
Theorem ACclient_call_not_OS : forall po pi,
 ~InOS(curs(scall 114%Z nil),(kenil,kstop))(pumerge po pi).
Proof.
 intros po pi(c&ke&ks&E&Cases);inversion E;subst.
 destruct Cases as[(f&vl&fc&tl&Bad&Lookup)|[(f&le&ks'&tp&d1&d2&s&s'&Bad&Lookup)|Bad]];
 cbn in *;congruence.
Qed.
