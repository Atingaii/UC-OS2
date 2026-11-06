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
Require Import CertiOS.certiucos.v293.proofs.V293ExitQuietCallProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickLifecycle.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.

(* A distinct fresh block is the running flag, not an alias of nesting or lock. *)
Definition QPge br:env:=set CGge 112%Z(br,Tint8).
Definition QPmemory br n run:=V293_write_byte(NPinitial n)br run.
Definition QPfinal br run:=if Nat.eqb run 1 then
 V293_exit_decrement_memory(QPmemory br 2 run)96%positive 2 else QPmemory br 2 run.
Definition QPtasks:tasks:=set emp OwnershipWaiting(curs(sfexec 114%Z nil nil),(kenil,kstop)).
Definition QPstate br M cs:osstate:=(QPge br,sig OwnershipWaiting(emp:env),M,(fun _=>false),
 sig OwnershipWaiting((false,nil,cs):localst)).

Lemma QPrunning_distinct : forall br,fresh(NPinitial 2)br ->br<>96%positive.
Proof.
 intros br Fresh;apply(V293_success_load_not_fresh(NPinitial 2)br 96%positive 2 Fresh).
 unfold NPinitial;apply V293_write_byte_load;lia.
Qed.

(* The extra byte is allocated and stored through the spatial rules. *)
Lemma QPtyped : forall br run cs,fresh(NPinitial 2)br ->run<256 ->
 CGstate OwnershipWaiting(QPmemory br 2 run)cs |=
 V293_owned_record_cell((br,0%Z),Tint8,V293_byteval run) **
 (V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 2) ** CPother).
Proof.
 intros br run cs Fresh Bound.
 pose proof(CPtyped_updated 2 cs ltac:(lia))as Held.
 pose proof(V293_tick_allocate_frame CGge CGle(NPinitial 2)(fun _=>false)(false,nil,cs)
 (RIabstract OwnershipWaiting)(spec_done None)br Tint8
 (V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 2) ** CPother)Fresh Held)as Raw.
 destruct(V293_tick_raw_slot_update(br,0%Z)Tint8 Vundef(V293_byteval run)
 (V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 2) ** CPother)
 CGge CGle(allocb(NPinitial 2)br 0%Z 1)(fun _=>false)(false,nil,cs)
 (RIabstract OwnershipWaiting)(spec_done None)(V293_byte_type run Bound)Raw)as(Mf&Store&After).
 assert(Canonical:store Tint8(allocb(NPinitial 2)br 0%Z 1)(br,0%Z)(V293_byteval run)=
 Some(QPmemory br 2 run)).
 { unfold store,V293_byteval;cbn[encode_val storebytes allocb].
   change ((match get (set (NPinitial 2) (br,0%Z) (true,Undef)) (br,0%Z) with
    | Some (true,_) => Some (set (set (NPinitial 2) (br,0%Z) (true,Undef))
      (br,0%Z) (true, Byte (Byte.repr (Int.unsigned (Int.repr (Z.of_nat run))))))
    | _ => None end) = Some (QPmemory br 2 run)).
   rewrite map_get_set;unfold QPmemory,V293_write_byte.
   apply f_equal;apply HalfPermMap.extensionality;intro a.
   change (get (set (set (NPinitial 2) (br,0%Z) (true,Undef)) (br,0%Z)
     (true, Byte (Byte.repr (Int.unsigned (Int.repr (Z.of_nat run)))))) a =
     get (set (NPinitial 2) (br,0%Z)
     (true, Byte (Byte.repr (Int.unsigned (Int.repr (Z.of_nat run)))))) a).
   destruct(HalfPermMap.dec_A(br,0%Z)a)as[Eq|Ne].
   - subst a;repeat rewrite map_get_set;reflexivity.
   - repeat rewrite map_get_set' by congruence;reflexivity. }
 assert(Mf=QPmemory br 2 run)by congruence;subst Mf;exact After.
Qed.

Theorem QPcomplete_quiet_simulation : forall br run cs ip,
 fresh(NPinitial 2)br ->run<256 ->
 ProgSim(RCprogram,(CPpo,CGempty,ip))QPtasks(QPstate br(QPmemory br 2 run)cs)
 SPph HPTh(RIabstract OwnershipWaiting)HPcst OwnershipWaiting.
Proof.
 intros br run cs ip Fresh Bound;unfold QPtasks,QPstate.
 eapply V293_exit_quiet_call_progsim with(caller:=(emp:env))(si:=nil)(cs:=cs)
 (f:=114%Z)(ks:=kstop)(entry:=sfexec 114%Z nil nil)
 (running:=112%Z)(nesting:=110%Z)(lock:=111%Z)(saved:=120%Z)(table:=105%Z)
 (high:=103%Z)(target:=106%Z)(current:=108%Z)(counter:=109%Z)(sched:=107%Z)
 (handoff:=V293_interrupt_handoff 103%Z 108%Z 106%Z)(br:=br)(run:=run)
 (bn:=96%positive)(n:=2)(locked:=0);try eassumption;try reflexivity.
 - left;reflexivity.
 - discriminate.
 - unfold QPmemory;apply V293_write_byte_load;exact Bound.
 - intro IsOne;repeat apply conj;try discriminate;try lia.
   + unfold QPge;rewrite map_get_set' by discriminate;vm_compute;reflexivity.
   + transitivity(load Tint8(NPinitial 2)(96%positive,0%Z)).
     * apply V293_load_block_frame;intro i;unfold QPmemory;apply V293_write_byte_other.
       exact(QPrunning_distinct br Fresh).
     * unfold NPinitial;apply V293_write_byte_load;lia.
   + intros _;exists(Byte(Byte.repr 2));unfold QPmemory.
     rewrite V293_write_byte_other by(exact(QPrunning_distinct br Fresh)).
     unfold NPinitial,V293_write_byte;apply map_get_set.
 - eapply SPterminal;[apply map_get_set| |reflexivity].
   unfold projS;simpl;repeat rewrite map_get_sig;reflexivity.
Qed.

(* Both original guard branches are independently simulated, with no
   simulation premise and the same functions, caller, task and saved stack. *)
Theorem QPstopped_and_running : forall br cs ip,fresh(NPinitial 2)br ->
 ProgSim(RCprogram,(CPpo,CGempty,ip))QPtasks(QPstate br(QPmemory br 2 0)cs)
 SPph HPTh(RIabstract OwnershipWaiting)HPcst OwnershipWaiting /\
 ProgSim(RCprogram,(CPpo,CGempty,ip))QPtasks(QPstate br(QPmemory br 2 1)cs)
 SPph HPTh(RIabstract OwnershipWaiting)HPcst OwnershipWaiting.
Proof. intros;split;apply QPcomplete_quiet_simulation;try assumption;lia. Qed.

Theorem QPrunning_only_changed : forall br a,
 a<>(br,0%Z) ->get(QPmemory br 2 0)a=get(QPmemory br 2 1)a.
Proof. intros br a Ne;unfold QPmemory,V293_write_byte;repeat rewrite map_get_set' by congruence;reflexivity. Qed.

Theorem QPguard_control : forall br run,fresh(NPinitial 2)br ->run<256 ->
 evalval(V293_OSIntEnter_running 112%Z)(QPge br,(emp:env),QPmemory br 2 run)=
 Some(Vint32(if Nat.eqb run 1 then Int.one else Int.zero)).
Proof.
 intros br run Fresh Bound;unfold V293_OSIntEnter_running.
 change(evalval(ebinop oeq(ecast(evar 112%Z)Tint32)(econst32(Int.repr(Z.of_nat 1))))
 (QPge br,(emp:env),QPmemory br 2 run)=Some(Vint32(if Nat.eqb run 1 then Int.one else Int.zero))).
 eapply V293_success_global_byte_eq;try eassumption;try lia.
 - apply map_emp_get.
 - unfold QPge;apply map_get_set.
 - unfold QPmemory;apply V293_write_byte_load;exact Bound.
Qed.

Theorem QPguard_changes_return : forall br,fresh(NPinitial 2)br ->
 load Tint8(QPfinal br 0)(96%positive,0%Z)=Some(V293_byteval 2) /\
 load Tint8(QPfinal br 1)(96%positive,0%Z)=Some(V293_byteval 1).
Proof.
 intros br Fresh;split.
 - unfold QPfinal;cbn[Nat.eqb].
   transitivity(load Tint8(NPinitial 2)(96%positive,0%Z)).
   + apply V293_load_block_frame;intro i;unfold QPmemory;apply V293_write_byte_other;
     exact(QPrunning_distinct br Fresh).
   + unfold NPinitial;apply V293_write_byte_load;lia.
 - unfold QPfinal,V293_exit_decrement_memory;cbn[Nat.eqb Nat.pred].
   apply V293_write_byte_load;lia.
Qed.

Theorem QPnonvacuous : exists br,fresh(NPinitial 2)br /\
 (forall cs,CGstate OwnershipWaiting(QPmemory br 2 1)cs |=
 V293_owned_record_cell((br,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 2) ** CPother)) /\
 (forall cs ip,ProgSim(RCprogram,(CPpo,CGempty,ip))QPtasks(QPstate br(QPmemory br 2 1)cs)
 SPph HPTh(RIabstract OwnershipWaiting)HPcst OwnershipWaiting).
Proof.
 destruct(memory_has_fresh_block(NPinitial 2))as[br Fresh];exists br.
 split;[exact Fresh| ];split;intros;[apply QPtyped|apply QPcomplete_quiet_simulation];try assumption;lia.
Qed.

(* All physical saved allocations have the same full released heap. *)
Theorem QPsaved_choice_independent : forall br run bs,
 fresh(NPinitial 2)br ->fresh(QPmemory br 2 run)bs ->
 exists Mz,store Tint32(allocb(QPmemory br 2 run)bs 0%Z 4)(bs,0%Z)
 (Vint32 Int.zero)=Some Mz /\
 free Tint32 bs(if Nat.eqb run 1 then V293_exit_decrement_memory Mz 96%positive 2 else Mz)=
 Some(QPfinal br run).
Proof.
 intros br run bs Fresh Saved.
 destruct(V293_success_scheduler_storage(QPmemory br 2 run)bs Saved)
 as(Mz&Store&Writable&Free&Frame);exists Mz;split;[exact Store| ].
 unfold QPfinal;destruct(Nat.eqb run 1);[ |exact Free].
 apply V293_saved_free_decrement;[exact Free| ].
 assert(Read:load Tint8(QPmemory br 2 run)(96%positive,0%Z)=Some(V293_byteval 2)).
 { transitivity(load Tint8(NPinitial 2)(96%positive,0%Z)).
   - apply V293_load_block_frame;intro i;unfold QPmemory;apply V293_write_byte_other;
     exact(QPrunning_distinct br Fresh).
   - unfold NPinitial;apply V293_write_byte_load;lia. }
 intro Eq;exact(V293_success_load_not_fresh(QPmemory br 2 run)bs 96%positive 2 Saved Read(eq_sym Eq)).
Qed.

Theorem QPrunning_flag_changes : forall br,
 load Tint8(QPmemory br 2 0)(br,0%Z)=Some(V293_byteval 0) /\
 load Tint8(QPmemory br 2 1)(br,0%Z)=Some(V293_byteval 1) /\
 V293_byteval 0<>V293_byteval 1.
Proof.
 intro br;repeat apply conj;try(unfold QPmemory;apply V293_write_byte_load;lia).
 vm_compute;discriminate.
Qed.
