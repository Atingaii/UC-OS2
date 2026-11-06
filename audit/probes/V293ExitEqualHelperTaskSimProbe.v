(* Independent highest-current heap at the helper-call cut; not outer-entry reachability. *)
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
Require Import CertiOS.certiucos.v293.proofs.V293ExitEqualHelperTaskSim.
Definition EHge : env := set(set RHge 108%Z(94%positive,Tint8))109%Z(95%positive,Tint32).
Definition EHle := V293_cpu_lenv 120%Z 98%positive.
Definition EHcells : list V293_record_cell :=
 (((98%positive,0%Z),Tint32,Vint32 Int.zero)::
  ((94%positive,0%Z),Tint8,V293_byteval 4)::
  ((91%positive,0%Z),Tint8,V293_byteval 4)::
  ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)::
  ((95%positive,0%Z),Tint32,Vint32 Int.mone)::nil).
Definition EHoutputs := OwnershipCellsMemory EHcells.
Definition EHdecoder := V293_full_array_memory 92%positive 0%Z Tint8(map V293_byteval V293_ready_table).
Definition EHextra := merge EHoutputs EHdecoder.
Definition EHmemory := merge(RTfull OwnershipReady)EHextra.
Definition EHframe := V293_exit_helper_frame 92%positive 94%positive 93%positive 95%positive
 98%positive nil 4(Vint32 Int.zero)(Vptr OwnershipWaiting)Int.mone.
Definition EHresource := V293_helper_resource 80%positive 81%positive 82%positive
 92%positive 91%positive OwnershipReady EHframe(V293_byteval 4).
Definition EHrest := V293_array_cells 92%positive 0%Z 1%Z Tint8(length V293_ready_table)++nil.
Definition EHinv := V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type
 (((94%positive,0%Z),Tint8)::((91%positive,0%Z),Tint8)::((95%positive,0%Z),Tint32)::EHrest).
Definition EHcontinuation := kseq(V293_OSSched_target_update 105%Z 103%Z 106%Z)
 (kseq ECbranch FTpending).
Lemma EHextra_join : join EHoutputs EHdecoder EHextra.
Proof.
 apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 92%positive)as[E|NE].
 - subst b;left;unfold EHoutputs;apply OwnershipCellsOutside;vm_compute;intuition congruence.
 - right;left;apply V293_full_array_outside;left;exact NE.
Qed.
Lemma EHjoin : join(RTfull OwnershipReady)EHextra EHmemory.
Proof.
 apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 92%positive)as[E|N92].
 - subst b;left;apply RToutside;discriminate.
 - destruct(in_dec Pos.eq_dec b [98%positive;94%positive;91%positive;93%positive;95%positive])as[E|NE].
   + left;destruct E as[<-|[<-|[<-|[<-|[<-|[]]]]]];apply RToutside;discriminate.
   + right;left;unfold EHextra;rewrite map_merge_semp by reflexivity.
     unfold EHoutputs;rewrite OwnershipCellsOutside by (vm_compute in NE|-*;intuition congruence).
     assert(Empty:get EHdecoder(b,i)=None).
     { unfold EHdecoder;apply V293_full_array_outside;left;exact N92. }
     change(match get EHdecoder(b,i) with Some v=>Some v|None=>None end=None).
     rewrite Empty;reflexivity.
Qed.
Lemma EHbase : V293_target_wstate EHge EHle EHmemory(RIabstract OwnershipReady)|=EHresource.
Proof.
 assert(Outputs:V293_target_wstate EHge EHle EHoutputs emp|=V293_owned_record_cells EHcells).
 { apply OwnershipCellsSpatial;[vm_compute;repeat split;intros;intuition congruence|
   repeat constructor;vm_compute;reflexivity]. }
 assert(Decoder:V293_target_wstate EHge EHle EHdecoder emp|=
 V293_read_bytes 92%positive 0%Z V293_ready_table **V293_read_bytes 92%positive 0%Z V293_ready_table).
 { rewrite !V293_read_bytes_array;apply V293_array_borrow.
   pose proof(V293_full_array_witness(map V293_byteval V293_ready_table)EHge EHle 92%positive 0%Z Tint8)as H.
   exact H. }
 assert(Extra:V293_target_wstate EHge EHle EHextra emp|=
 V293_owned_record_cells EHcells **
 (V293_read_bytes 92%positive 0%Z V293_ready_table **V293_read_bytes 92%positive 0%Z V293_ready_table)).
 { eapply V293_target_wstate_star;[exact EHextra_join|apply map_join_emp|exact Outputs|exact Decoder]. }
 assert(Ready:V293_target_wstate EHge EHle(RTfull OwnershipReady)(RIabstract OwnershipReady)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipReady).
 { apply RTenv_spatial;reflexivity. }
 assert(All:V293_target_wstate EHge EHle EHmemory(RIabstract OwnershipReady)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipReady **
 (V293_owned_record_cells EHcells **
 (V293_read_bytes 92%positive 0%Z V293_ready_table **V293_read_bytes 92%positive 0%Z V293_ready_table))).
 { eapply V293_target_wstate_star;[exact EHjoin|apply map_join_emp|exact Ready|exact Extra]. }
 unfold EHresource,V293_helper_resource,EHframe,V293_exit_helper_frame.
 cbn[EHcells V293_owned_record_cells V293_storage]in All|-*.
 unfold V293_owned_record_cell in All|-*;clear -All;sep auto.
Qed.
Lemma EHentry : (EHge,EHle,EHmemory,(fun _=>false),(false,nil,false::nil),RIabstract OwnershipReady,spec_done None)|=EHresource.
Proof.
 pose proof EHbase as Held;unfold EHresource,V293_helper_resource in Held|-*.
 eapply V293_ready_critical_stack with(ci:=nil).
 - split;[unfold V293_owned_record_cell;cbn;auto|split;
   [apply V293_helper_read_good|apply V293_exit_helper_frame_good]].
 - exact Held.
Qed.
Theorem EHnonempty_call_cut : forall ip A,
 TaskSim(RCprogram,(CPpo,CGempty,ip))(curs(scall 107%Z nil),(kenil,EHcontinuation))
 (EHge,EHle,EHmemory,(fun _=>false),(false,nil,false::nil))
 (RCprogram,A)(SKIP,(kenil,kstop))
 (RIabstract OwnershipReady)V293_shared_li EHinv
 (fun st=>satp(fst st)(snd st)(RDYINV EHinv OwnershipReady **LINV V293_shared_li OwnershipReady nil))OwnershipReady.
Proof.
 intros ip A;unfold EHcontinuation,EHinv,EHrest,ECbranch,FTpending,CPcall,EHle.
 eapply V293_exit_equal_helper_TaskSim with(nc:=4)(bc:=94%positive)(bo:=93%positive)
 (saved_value:=Vint32 Int.zero)(oldtarget:=Vptr OwnershipWaiting)(c:=Int.mone)
 (oldhigh:=V293_byteval 4)(tasks:=OwnershipTasks)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(y:=104%Z).
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
 - exact(RIfixed_tasks OwnershipReady).
 - split;[lia|exists rdy;exists Vnull;reflexivity].
 - exact RIhighest.
 - reflexivity.
 - exact EHentry.
Qed.

(* Only current=4 becomes current=6 in this same heap; high remains 4.
   This local comparison control does not execute the helper or outer call. *)
Theorem EHcurrent_byte_control : exists M6,
 load Tint8 EHmemory(94%positive,0%Z)=Some(V293_byteval 4) /\
 load Tint8 EHmemory(91%positive,0%Z)=Some(V293_byteval 4) /\
 store Tint8 EHmemory(94%positive,0%Z)(V293_byteval 6)=Some M6 /\
 load Tint8 M6(94%positive,0%Z)=Some(V293_byteval 6) /\
 load Tint8 M6(91%positive,0%Z)=Some(V293_byteval 4) /\
 (forall b i,(b,i)<>(94%positive,0%Z) ->get M6(b,i)=get EHmemory(b,i)) /\
 evalval(V293_OSSched_different 103%Z 108%Z)(EHge,EHle,EHmemory)=Some(Vint32 Int.zero) /\
 evalval(V293_OSSched_different 103%Z 108%Z)(EHge,EHle,M6)=Some(Vint32 Int.one).
Proof.
 pose proof EHbase as Base;unfold EHresource,V293_helper_resource,EHframe,V293_exit_helper_frame in Base.
 assert(Pack:V293_target_wstate EHge EHle EHmemory(RIabstract OwnershipReady)|=
 V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **Atrue)).
 { clear -Base;sep auto. }
 assert(Read:load Tint8 EHmemory(94%positive,0%Z)=Some(V293_byteval 4)).
 { change(load Tint8(assertion.getmem(V293_target_wstate EHge EHle EHmemory(RIabstract OwnershipReady)))(94%positive,0%Z)=Some(V293_byteval 4)).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Pack]. }
 assert(High:load Tint8 EHmemory(91%positive,0%Z)=Some(V293_byteval 4)).
 { change(load Tint8(assertion.getmem(V293_target_wstate EHge EHle EHmemory(RIabstract OwnershipReady)))(91%positive,0%Z)=Some(V293_byteval 4)).
   eapply V293_record_star_load_r;[apply V293_record_star_load_l;apply V293_owned_record_cell_load|exact Pack]. }
 destruct(V293_owned_record_cell_update (94%positive,0%Z) Tint8 (V293_byteval 4)(V293_byteval 6)
 _ _ _ _ _ _ _ _ eq_refl Pack)as(M6&Store&After).
 assert(ReadAfter:load Tint8 M6(94%positive,0%Z)=Some(V293_byteval 6)).
 { change(load Tint8(assertion.getmem(V293_target_wstate EHge EHle M6(RIabstract OwnershipReady)))(94%positive,0%Z)=Some(V293_byteval 6)).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact After]. }
 assert(HighAfter:load Tint8 M6(91%positive,0%Z)=Some(V293_byteval 4)).
 { change(load Tint8(assertion.getmem(V293_target_wstate EHge EHle M6(RIabstract OwnershipReady)))(91%positive,0%Z)=Some(V293_byteval 4)).
   eapply V293_record_star_load_r;[apply V293_record_star_load_l;apply V293_owned_record_cell_load|exact After]. }
 exists M6;split;[exact Read| ];split;[exact High| ];split;[exact Store| ];
 split;[exact ReadAfter| ];split;[exact HighAfter| ];split.
 - intros b i Different;eapply V293_storebytes_outside;[exact Store| ].
   destruct(Pos.eq_dec b 94%positive)as[Same|Other];[subst b|left;exact Other].
   right;assert(i<>0%Z)by(intro E;apply Different;congruence).
   cbn[encode_val V293_byteval inj_bytes encode_int List.map length];lia.
 - split.
   + exact(proj1(V293_OSSched_byte_comparison_eval EHge EHle EHmemory 103%Z 108%Z
       91%positive 94%positive 4 4 ltac:(lia)ltac:(lia)eq_refl eq_refl eq_refl eq_refl High Read)).
   + exact(proj1(V293_OSSched_byte_comparison_eval EHge EHle M6 103%Z 108%Z
       91%positive 94%positive 4 6 ltac:(lia)ltac:(lia)eq_refl eq_refl eq_refl eq_refl HighAfter ReadAfter)).
Qed.
