(* Independent full-entry highest-current heap; no preallocated saved local. *)
Require Import CertiOS.audit.probes.V293ExitHelperTargetProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitGuardHelperTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitCriticalPrefixTaskSim.
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
Require Import CertiOS.certiucos.v293.proofs.V293ExitActiveCallTaskSim.
Require Import CertiOS.audit.probes.V293ExitGuardHelperProbe.
Require Import CertiOS.audit.probes.V293ExitActiveCallTaskSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitClientCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitEqualCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitNestedCallTaskSim.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Definition ECge : env := set GHge 132%Z(152%positive,Tint8).
Definition ECle : env := emp.
Section ActiveHeap.
Variable n:nat.
Definition ECcells : list V293_record_cell :=
 (((150%positive,0%Z),Tint8,V293_byteval n)::
  ((151%positive,0%Z),Tint8,V293_byteval 0)::
  ((152%positive,0%Z),Tint8,V293_byteval 1)::
  ((94%positive,0%Z),Tint8,V293_byteval 4)::
  ((91%positive,0%Z),Tint8,V293_byteval 88)::
  ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)::
  ((95%positive,0%Z),Tint32,Vint32 Int.mone)::nil).
Definition ECoutputs := OwnershipCellsMemory ECcells.
Definition ECdecoder := V293_full_array_memory 92%positive 0%Z Tint8(map V293_byteval V293_ready_table).
Definition ECextra := merge ECoutputs ECdecoder.
Definition ECmemory := merge(RTfull OwnershipReady)ECextra.
Definition ECresource := V293_exit_active_resource 80%positive 81%positive 82%positive
 92%positive 94%positive 91%positive 93%positive 95%positive 150%positive 151%positive 152%positive
 nil OwnershipReady 4(Vptr OwnershipWaiting)Int.mone n(V293_byteval 88).
Lemma ECextra_join : join ECoutputs ECdecoder ECextra.
Proof.
 apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 92%positive)as[E|NE].
 - subst b;left;unfold ECoutputs;apply OwnershipCellsOutside;vm_compute;intuition congruence.
 - right;left;apply V293_full_array_outside;left;exact NE.
Qed.
Lemma ECjoin : join(RTfull OwnershipReady)ECextra ECmemory.
Proof.
 apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(Pos.eq_dec b 92%positive)as[E|N92].
 - subst b;left;apply RToutside;discriminate.
 - destruct(in_dec Pos.eq_dec b [150%positive;151%positive;152%positive;94%positive;91%positive;93%positive;95%positive])as[E|NE].
   + left;repeat destruct E as[<-|E];try(apply RToutside;discriminate);contradiction.
   + right;left;unfold ECextra;rewrite map_merge_semp by reflexivity.
     unfold ECoutputs;rewrite OwnershipCellsOutside by (vm_compute in NE|-*;intuition congruence).
     assert(Empty:get ECdecoder(b,i)=None).
     { unfold ECdecoder;apply V293_full_array_outside;left;exact N92. }
     change(match get ECdecoder(b,i) with Some v=>Some v|None=>None end=None).
     rewrite Empty;reflexivity.
Qed.
Lemma ECbase : n<256 ->V293_target_wstate ECge ECle ECmemory(RIabstract OwnershipReady)|=ECresource.
Proof.
 intro Range.
 assert(Outputs:V293_target_wstate ECge ECle ECoutputs emp|=V293_owned_record_cells ECcells).
 { apply OwnershipCellsSpatial;[vm_compute;repeat split;intros;intuition congruence|
   constructor;[apply V293_byte_type;exact Range|repeat constructor;vm_compute;reflexivity]]. }
 assert(Decoder:V293_target_wstate ECge ECle ECdecoder emp|=
 V293_read_bytes 92%positive 0%Z V293_ready_table **V293_read_bytes 92%positive 0%Z V293_ready_table).
 { rewrite !V293_read_bytes_array;apply V293_array_borrow.
   pose proof(V293_full_array_witness(map V293_byteval V293_ready_table)ECge ECle 92%positive 0%Z Tint8)as H.
   exact H. }
 assert(Extra:V293_target_wstate ECge ECle ECextra emp|=
 V293_owned_record_cells ECcells **
 (V293_read_bytes 92%positive 0%Z V293_ready_table **V293_read_bytes 92%positive 0%Z V293_ready_table)).
 { eapply V293_target_wstate_star;[exact ECextra_join|apply map_join_emp|exact Outputs|exact Decoder]. }
 assert(Ready:V293_target_wstate ECge ECle(RTfull OwnershipReady)(RIabstract OwnershipReady)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipReady).
 { apply RTenv_spatial;reflexivity. }
 assert(All:V293_target_wstate ECge ECle ECmemory(RIabstract OwnershipReady)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipReady **
 (V293_owned_record_cells ECcells **
 (V293_read_bytes 92%positive 0%Z V293_ready_table **V293_read_bytes 92%positive 0%Z V293_ready_table))).
 { eapply V293_target_wstate_star;[exact ECjoin|apply map_join_emp|exact Ready|exact Extra]. }
 unfold ECresource,V293_exit_active_resource,V293_exit_guard_resource,V293_helper_resource,V293_exit_active_frame.
 cbn[ECcells V293_owned_record_cells V293_storage]in All|-*.
 unfold V293_owned_record_cell in All|-*;clear -All;sep auto.
Qed.
End ActiveHeap.
Definition ECrest := V293_array_cells 92%positive 0%Z 1%Z Tint8(length V293_ready_table)++
 [((150%positive,0%Z),Tint8);((151%positive,0%Z),Tint8);((152%positive,0%Z),Tint8)].
Definition ECinv := V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type
 (((94%positive,0%Z),Tint8)::((91%positive,0%Z),Tint8)::((95%positive,0%Z),Tint32)::ECrest).

Definition ECspec:osspec:=((fun f=>if Z.eq_dec f 114%Z then
 Some((fun _:vallist=>spec_done None),(Tvoid,nil))else None),
 (fun _=>None),V293_scheduler).
Theorem ECnonempty_client_call : forall n ip,
 n<=1 ->
 TaskSim(RCprogram,(ACpo,CGempty,ip))(curs(scall 114%Z nil),(kenil,kstop))
 (ECge,ECle,ECmemory n,(fun _=>false),(false,nil,nil))
 (RCprogram,ECspec)(curs(scall 114%Z nil),(kenil,kstop))
 (RIabstract OwnershipReady)V293_shared_li ECinv
 (fun st=>satp(fst st)(snd st)(RDYINV ECinv OwnershipReady **LINV V293_shared_li OwnershipReady nil))OwnershipReady.
Proof.
 intros n ip Bound;unfold ECinv,ECrest,ECle.
 eapply V293_exit_equal_client_call_TaskSim with(nc:=4)(bc:=94%positive)(bo:=93%positive)
 (oldtarget:=Vptr OwnershipWaiting)(c:=Int.mone)(oldhigh:=V293_byteval 88)
 (tasks:=OwnershipTasks)(rest:=nil)(saved:=120%Z)(helper:=107%Z)
 (running:=132%Z)(nesting:=130%Z)(lock:=131%Z)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(y:=104%Z).
 - vm_compute;reflexivity.
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
 - exact(RIfixed_tasks OwnershipReady).
 - split;[lia|exists rdy;exists Vnull;reflexivity].
 - exact RIhighest.
 - exact Bound.
 - discriminate.
 - discriminate.
 - discriminate.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - apply ECbase;lia.
Qed.


Lemma ECbinding_single_factor :
 fst(fst ECspec)114%Z=Some((fun _:vallist=>spec_done None),(Tvoid,nil)) /\ fst(fst GHspec)114%Z=None /\ snd ECspec=snd GHspec /\snd(fst ECspec)=snd(fst GHspec) /\ (forall f,f<>114%Z ->fst(fst ECspec)f=fst(fst GHspec)f).
Proof. repeat split;try reflexivity;intros f NE;
 change((if Z.eq_dec f 114%Z then Some((fun _:vallist=>spec_done None),(Tvoid,@nil type))else None)=None);
 destruct(Z.eq_dec f 114%Z);congruence. Qed.

Lemma ECabstract_entry : forall t cst O,
 htstep(RCprogram,ECspec)t(curs(sfexec 114%Z nil nil),(kenil,kstop))cst O
 (curs(hapi_code(spec_done None)),(kenil,kstop))cst O.
Proof. intros;apply V293_nested_nil_api_enter;vm_compute;reflexivity. Qed.

Theorem ECmissing_binding_no_high_step : forall t cst O Cf cst' O',
 ~htstep(RCprogram,GHspec)t(curs(sfexec 114%Z nil nil),(kenil,kstop))cst O Cf cst' O'.
Proof.
 intros t cst O Cf cst' O' Step;inversion Step;subst;
 repeat match goal with E:(_,_) = (_,_) |- _=>inversion E;clear E;subst end.
 - match goal with H:cstep _ _ _ _ _ |- _=>inversion H;subst end;
   match goal with
   | H:estep _ _ _ _ _ _ |- _=>inversion H;subst;discriminate
   | H:sstep _ _ _ _ _ _ _ |- _=>inversion H;subst;try discriminate
   end.
   repeat match goal with E:(_,_) = (_,_) |- _=>inversion E;clear E;subst end.
   match goal with H:RCprogram 114%Z=Some _ |- _=>vm_compute in H;discriminate H end.
 - match goal with H:hapistep _ _ _ _ _ |- _=>inversion H;subst;try discriminate end.
   repeat match goal with E:(_,_) = (_,_) |- _=>inversion E;clear E;subst end.
   match goal with E:GHspec=(?B,_,_),H:?B 114%Z=Some _ |- _=>
     pose proof(f_equal(fun A=>fst(fst A)114%Z)E)as Empty;
     change(None=B 114%Z)in Empty;rewrite <-Empty in H;discriminate H end.
Qed.

(* Removing the high API binding cannot change this concrete client step. *)
Lemma ECclient_step_unchanged : forall n,
 cstep(pumerge RCprogram ACpo)(curs(scall 114%Z nil),(kenil,kstop))
 (ECge,ECle,ECmemory n)(curs(sfexec 114%Z nil nil),(kenil,kstop))
 (ECge,ECle,ECmemory n).
Proof. intro n;eapply stmt_step;[reflexivity|apply snpcall_step]. Qed.

Definition ECclient : clientst :=
 (ECge,set(emp:cltenvs)OwnershipReady ECle,(emp:mem)).
Lemma ECactual_client_low_step : forall n ip,exists cst',
 ltstep(RCprogram,(ACpo,CGempty,ip))OwnershipReady
 (curs(scall 114%Z nil),(kenil,kstop))ECclient
 (ECge,ECle,ECmemory n,(fun _=>false),(false,nil,nil))
 (curs(sfexec 114%Z nil nil),(kenil,kstop))cst'
 (ECge,ECle,ECmemory n,(fun _=>false),(false,nil,nil)).
Proof.
 intros n ip;unfold ECclient;
 exists(ECge,set(set(emp:cltenvs)OwnershipReady ECle)OwnershipReady ECle,(emp:mem)).
 eapply clt_step with(m:=(ECge,ECle,(emp:mem)))(m':=(ECge,ECle,(emp:mem)));
 try reflexivity.
 - eapply stmt_step;[reflexivity|apply snpcall_step].
 - apply ACclient_call_not_OS.
 - apply map_get_set.
Qed.
