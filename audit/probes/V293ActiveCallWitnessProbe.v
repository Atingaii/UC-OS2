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

(* Spatial resources for one physical dispatch heap, including both saved
   objects and the running byte in an arbitrary unchanged frame. *)
Definition FWstate (ge le:env) (M:mem) := (ge,le,M,((fun _=>false):isr),
 ((false,nil,nil):localst),RIabstract OwnershipWaiting,spec_done None).
Definition FWcells h t c count R :=
 V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval h) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr t) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval c) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 count) ** R))).
Local Ltac fw_env := unfold QPge; rewrite map_get_set' by discriminate; reflexivity.

Lemma FWdispatch_resources : forall ge le M R,
 (forall x,In x [103%Z;105%Z;106%Z;108%Z;109%Z] ->get le x=None) ->
 (forall x,x<>112%Z ->get ge x=get CGge x) ->GoodInvAsrt R ->
 (forall n,n<256 ->load Tint8 M(92%positive,Z.of_nat n)=Some(V293_byteval(V293_ready_lookup n))) ->
 FWstate ge le M |= SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 FWcells 88 OwnershipWaiting 6 Int.mone (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) ** R) ->
 exists Mt M1 Mc Msw Mret,
 store(Tptr V293_tcb_type)(V293_write_byte M 91%positive 4)(93%positive,0%Z)(Vptr OwnershipReady)=Some Mt /\
 evalval(V293_OSSched_different 103%Z 108%Z)(ge,le,Mt)=Some(Vint32 Int.one) /\
 load Tint32 Mt(95%positive,0%Z)=Some(Vint32 Int.mone) /\
 store Tint32 Mt(95%positive,0%Z)(Vint32(Int.add Int.mone Int.one))=Some M1 /\
 evaltype(evar 108%Z)(ge,le,M1)=Some Tint8 /\
 evaltype(evar 103%Z)(ge,le,M1)=Some Tint8 /\
 evalval(evar 103%Z)(ge,le,M1)=Some(V293_byteval 4) /\
 evalval(eaddrof(evar 108%Z))(ge,le,M1)=Some(Vptr(94%positive,Int.zero)) /\
 store Tint8 M1(94%positive,0%Z)(V293_byteval 4)=Some Mc /\
 load(Tptr V293_tcb_type)Mc(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Msw /\
 free Tint32 98%positive Msw=Some Mret.
Proof.
 intros ge le M R NL GE Good Lookup Held.
 pose proof(NL 108%Z ltac:(simpl;auto))as NC.
 pose proof(NL 103%Z ltac:(simpl;auto))as NH.
 assert(GH:get ge 103%Z=Some(91%positive,Tint8))by(rewrite GE by discriminate;reflexivity).
 assert(GC:get ge 108%Z=Some(94%positive,Tint8))by(rewrite GE by discriminate;reflexivity).
 assert(GCount:get ge 109%Z=Some(95%positive,Tint32))by(rewrite GE by discriminate;reflexivity).
 change (@get var (block*type) env EnvMap le 108%Z=None)in NC.
 change (@get var (block*type) env EnvMap le 103%Z=None)in NH.
 change (@get var (block*type) env EnvMap ge 108%Z=Some(94%positive,Tint8))in GC.
 change (@get var (block*type) env EnvMap ge 103%Z=Some(91%positive,Tint8))in GH.
 assert(FrameGood:GoodInvAsrt
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) ** R))))by(repeat split;try exact I;exact Good).
 destruct(V293_ready_dispatch_call 80%positive 81%positive 82%positive (pumerge CPpo CGempty) kstop
 ge le M(fun _=>false)(false,nil,nil)(RIabstract OwnershipWaiting)(spec_done None)OwnershipWaiting
 _ 107%Z 100%Z 101%Z 102%Z 103%Z 104%Z 105%Z 106%Z
 92%positive 91%positive 93%positive(V293_byteval 88)(Vptr OwnershipWaiting)
 ltac:(vm_compute;reflexivity)
 ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)ltac:(discriminate)
 ltac:(discriminate)ltac:(discriminate)
 ltac:(rewrite GE by discriminate;reflexivity)
 ltac:(rewrite GE by discriminate;reflexivity)
 ltac:(rewrite GE by discriminate;reflexivity) GH
 ltac:(rewrite GE by discriminate;reflexivity)
 (NL 103%Z ltac:(simpl;auto))(NL 105%Z ltac:(simpl;auto))(NL 106%Z ltac:(simpl;auto))
 ltac:(rewrite GE by discriminate;reflexivity) FrameGood Lookup Held)
 as(tasks&lo&hi&entries&next&message&b&Ms&Mskip&Mt&Fresh&Map&Rel&Task&Call&Skipped&Free&Removed&High&Exec&Store&After&Target&Sched&Pre&Live&Dead&CallFrame&TargetFrame).
 assert(tasks=OwnershipTasks)by(pose proof(RIfixed_tasks OwnershipWaiting);congruence);subst tasks.
 assert(Range:V293_ready_select lo hi(V293_ready_group lo hi)<13).
 { destruct Rel as[Lo[Hi[Nonempty[Bitmap Table]]]];apply V293_ready_selection_range;assumption||reflexivity. }
 destruct(RTonly_ready _ _ _ Range Task)as[Selected[Next Message]];subst next message.
 rewrite Selected in After,Skipped,High.
 assert(Cells:FWstate ge le Mskip |=
 V293_owned_record_cells (((91%positive,0%Z),Tint8,V293_byteval 4)::nil) ** Atrue).
 { cbn[V293_owned_record_cells];clear -Skipped;sep auto. }
 destruct(V293_owned_cells_byte_writable (((91%positive,0%Z),Tint8,V293_byteval 4)::nil)
 (91%positive,0%Z)(V293_byteval 4)Atrue ge le Mskip(fun _=>false)
 (false,nil,nil)(RIabstract OwnershipWaiting)(spec_done None)ltac:(simpl;auto)Cells)as[raw Full].
 pose proof(V293_full_byte_load_encoding Mskip(91%positive,0%Z)4 raw Full High)as Output.
 assert(Canonical:Mskip=V293_write_byte M 91%positive 4).
 { apply HalfPermMap.extensionality;intros[c i].
   change(get Mskip(c,i)=get(V293_write_byte M 91%positive 4)(c,i)).
   destruct(HalfPermMap.dec_A(91%positive,0%Z)(c,i))as[E|Ne].
   - inversion E;subst;unfold V293_write_byte;rewrite map_get_set;exact Output.
   - unfold V293_write_byte;rewrite map_get_set' by exact Ne;apply CallFrame;intro E;apply Ne;symmetry;exact E. }
 rewrite Canonical in Store.
 assert(High0:load Tint8 Mt(91%positive,0%Z)=Some(V293_byteval 4)).
 { eapply V293_record_star_load_l with(s:=FWstate ge le Mt)
 (P:=V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - clear -After;sep auto. }
 assert(Cache:load Tint8 Mt(94%positive,0%Z)=Some(V293_byteval 6)).
 { eapply V293_record_star_load_l with(s:=FWstate ge le Mt)
 (P:=V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - clear -After;sep auto. }
 destruct(V293_OSSched_byte_comparison_eval ge le Mt 103%Z 108%Z 91%positive 94%positive
 4 6 ltac:(lia)ltac:(lia)(NL 103%Z ltac:(simpl;auto))(NL 108%Z ltac:(simpl;auto)) GH GC High0 Cache)as[Guard _].
 change(evalval(V293_OSSched_different 103%Z 108%Z)(ge,le,Mt)=Some(Vint32 Int.one))in Guard.
 assert(Owned:FWstate ge le Mt |=
 V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **
 (SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) ** R)))))).
 { clear -After;sep auto. }
 assert(Counter:load Tint32 Mt(95%positive,0%Z)=Some(Vint32 Int.mone)).
 { eapply V293_record_star_load_l with(s:=FWstate ge le Mt);
 [intros st H;apply V293_owned_record_cell_load;exact H|exact Owned]. }
 destruct(V293_owned_record_cell_update (95%positive,0%Z)Tint32(Vint32 Int.mone)
 (Vint32(Int.add Int.mone Int.one)) _ _ _ _ _ _ _ _ eq_refl Owned)as(M1&Increment&Updated).
 assert(Raw:FWstate ge le M1 |=
 SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32(Int.add Int.mone Int.one)) **
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) ** R)))))).
 { clear -Updated;sep auto. }
 assert(High1:load Tint8 M1(91%positive,0%Z)=Some(V293_byteval 4)).
 { eapply V293_record_star_load_l with(s:=FWstate ge le M1)
 (P:=V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 4))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - clear -Raw;sep auto. }
 destruct(V293_handoff_copy_execution 80%positive 81%positive 82%positive (pumerge CPpo CGempty) kstop
 ge le M1(fun _=>false)(false,nil,nil)(RIabstract OwnershipWaiting)(spec_done None)
 OwnershipWaiting _ 103%Z 108%Z 106%Z 91%positive 94%positive 93%positive 4 6 OwnershipReady
 ltac:(lia)(NL 103%Z ltac:(simpl;auto))(NL 108%Z ltac:(simpl;auto))GH GC Raw)
 as(Mc&CopyTrace&Copy&Copied&OutsideCopy).
 assert(TargetCopy:load(Tptr V293_tcb_type)Mc(93%positive,0%Z)=Some(Vptr OwnershipReady)).
 { eapply V293_record_star_load_l with(s:=FWstate ge le Mc)
 (P:=V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipReady))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - clear -Copied;sep auto. }
 assert(SwitchOwned:FWstate ge le Mc |=
 SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) ** Atrue)).
 { clear -Copied;sep auto. }
 destruct(V293_ready_current_write 80%positive 81%positive 82%positive OwnershipWaiting OwnershipReady _
 ge le Mc(fun _=>false)(false,nil,nil)(RIabstract OwnershipWaiting)(spec_done None)
 1%positive V293_tcb_type SwitchOwned ltac:(rewrite GE by discriminate;reflexivity))
 as(Msw&PhysicalStore&AfterSwitch&ReadCurrent&Frame).
 assert(Saved:(ge,le,Msw,(fun _=>false),(false,nil,nil),SPOf,spec_done None)|=
 Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) ** Atrue).
 { unfold SPOf;clear -AfterSwitch;sep auto. }
 destruct(V293_cpu_release _ _ _ _ _ _ _ _ _ _ Saved)as(Mret&FreeTarget&Rest&RemovedTarget&Outside).
 exists Mt;exists M1;exists Mc;exists Msw;exists Mret;split;[exact Store| ];split;[exact Guard| ];split;[exact Counter| ];split;[exact Increment| ].
 split.
 - unfold evaltype;rewrite NC,GC;reflexivity.
 - split.
   + unfold evaltype;rewrite NH,GH;reflexivity.
   + split.
     * unfold evalval,evaltype,get_lenv,get_genv,get_mem;rewrite NH,GH;cbn -[load];exact High1.
     * split.
       -- unfold evalval,evaltype,evaladdr,get_lenv,get_genv;rewrite NC,GC;reflexivity.
       -- repeat split;assumption.
Qed.

Lemma FWbase : forall ge le,
 get ge OSTCBCur=Some(1%positive,Tptr V293_tcb_type) ->
 FWstate ge le CEM |= SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 FWcells 88 OwnershipWaiting 6 Int.mone(CGframe 0 0).
Proof.
 intros ge le Env.
 assert(Core:V293_target_wstate ge le(CGwith OwnershipWaiting true 0 0)(RIabstract OwnershipWaiting)|=
 SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 V293_owned_record_cells(CGcells true 0 0)).
 { eapply V293_target_wstate_star with(m1:=RTfull OwnershipWaiting)(m2:=CGoutputs true 0 0)
 (o1:=RIabstract OwnershipWaiting)(o2:=emp).
 - apply CGoutputs_join.
 - apply map_join_emp.
 - apply RSenv_spatial with(tp:=V293_tcb_type);exact Env.
 - eapply V293_owned_cells_context;apply CGoutputs_spatial;lia. }
 assert(Both:V293_target_wstate ge le CEM(RIabstract OwnershipWaiting)|=
 (SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 V293_owned_record_cells(CGcells true 0 0)) **V293_read_bytes 92%positive 0%Z V293_ready_table).
 { eapply V293_target_wstate_star with(m1:=CGwith OwnershipWaiting true 0 0)(m2:=RTdecoder)
 (o1:=RIabstract OwnershipWaiting)(o2:=emp).
 - apply CGdecoder_join.
 - apply map_join_emp.
 - exact Core.
 - apply V293_read_bytes_witness. }
 cbn[CGcells STcells CGextra app V293_owned_record_cells]in Both.
 unfold FWstate,FWcells,CGframe,RCframe;cbn[CGextra V293_owned_record_cells].
 clear Core;sep auto.
Qed.

Lemma FWinitial_owned : forall br le,fresh(NPinitial 1)br ->
 FWstate(QPge br)le(QPmemory br 1 1)|=
 V293_owned_record_cell((br,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 1) **CPother).
Proof.
 intros br le Fresh.
 assert(Base:FWstate(QPge br)le CEM |=
 V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 0) **CPother).
 { pose proof(FWbase(QPge br)le ltac:(fw_env))as Held.
   unfold FWcells,CGframe,CPother in *;cbn[CGextra V293_owned_record_cells]in Held.
   clear -Held;sep auto. }
 pose proof(proj2(V293_owned_byte_update(96%positive,0%Z)(V293_byteval 0)1 CPother
 (QPge br)le CEM(fun _=>false)(false,nil,nil)(RIabstract OwnershipWaiting)(spec_done None)ltac:(lia)Base))as Held.
 change(FWstate(QPge br)le(NPinitial 1)|=
 V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 1) **CPother)in Held.
 pose proof(V293_tick_allocate_frame(QPge br)le(NPinitial 1)(fun _=>false)(false,nil,nil)
 (RIabstract OwnershipWaiting)(spec_done None)br Tint8
 (V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 1) **CPother)Fresh Held)as Raw.
 destruct(V293_tick_raw_slot_update(br,0%Z)Tint8 Vundef(V293_byteval 1)
 (V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 1) **CPother)
 (QPge br)le(allocb(NPinitial 1)br 0%Z 1)(fun _=>false)(false,nil,nil)
 (RIabstract OwnershipWaiting)(spec_done None)(V293_byte_type 1 ltac:(lia))Raw)as(Mf&Store&After).
 assert(Canonical:store Tint8(allocb(NPinitial 1)br 0%Z 1)(br,0%Z)(V293_byteval 1)=
 Some(QPmemory br 1 1)).
 { unfold store,V293_byteval;cbn[encode_val storebytes allocb].
   change((match get(set(NPinitial 1)(br,0%Z)(true,Undef))(br,0%Z)with
   |Some(true,_)=>Some(set(set(NPinitial 1)(br,0%Z)(true,Undef))(br,0%Z)(true,Byte(Byte.repr 1)))
   |_=>None end)=Some(QPmemory br 1 1)).
   rewrite map_get_set;unfold QPmemory,V293_write_byte.
   apply f_equal;apply HalfPermMap.extensionality;intro a.
   change(get(set(set(NPinitial 1)(br,0%Z)(true,Undef))(br,0%Z)(true,Byte(Byte.repr 1)))a=
   get(set(NPinitial 1)(br,0%Z)(true,Byte(Byte.repr 1)))a).
   destruct(HalfPermMap.dec_A(br,0%Z)a)as[E|N].
   - subst a;repeat rewrite map_get_set;reflexivity.
   - repeat rewrite map_get_set' by congruence;reflexivity. }
 assert(Mf=QPmemory br 1 1)by congruence;subst Mf;exact After.
Qed.

Lemma FWfresh_present : forall M b c j v,
 fresh M b ->get M(c,j)=Some v ->b<>c.
Proof.
 intros M b c j v Fresh Present Same;subst c.
 pose proof(V293_success_fresh_none M b Fresh j)as Empty.
 change(@get addr(bool*memval)mem memMap M(b,j)=None)in Empty.
 change(@get addr(bool*memval)mem memMap M(b,j)=Some v)in Present.
 rewrite Empty in Present;discriminate.
Qed.

Lemma FWentry_frame : forall br bs Mz,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->
 store Tint32(allocb(QPmemory br 1 1)bs 0%Z 4)(bs,0%Z)(Vint32 Int.zero)=Some Mz ->
 forall b i,b<>96%positive ->(exists j v,get CEM(b,j)=Some v) ->
 get(V293_exit_decrement_memory Mz 96%positive 1)(b,i)=get CEM(b,i).
Proof.
 intros br bs Mz FreshRunning FreshSaved Init b i NotNest(j&v&Present).
 assert(RunningNe:br<>b).
 { eapply FWfresh_present;[exact FreshRunning| ].
   unfold NPinitial;rewrite V293_write_byte_other;[exact Present| ].
   intro E;apply NotNest;symmetry;exact E. }
 assert(EntryPresent:get(QPmemory br 1 1)(b,j)=Some v).
 { unfold QPmemory;rewrite V293_write_byte_other by exact RunningNe.
   unfold NPinitial;rewrite V293_write_byte_other;[exact Present| ].
   intro E;apply NotNest;symmetry;exact E. }
 assert(SavedNe:bs<>b)by(eapply FWfresh_present;eassumption).
 destruct(V293_success_scheduler_storage(QPmemory br 1 1)bs FreshSaved)
 as(Ms&Init'&Writable&Free&Frame).
 assert(Mz=Ms)by congruence;subst Mz.
 change(get(V293_write_byte Ms 96%positive 0)(b,i)=get CEM(b,i)).
 rewrite V293_write_byte_other by(intro E;apply NotNest;symmetry;exact E).
 rewrite Frame by(intro E;apply SavedNe;symmetry;exact E).
 unfold QPmemory;rewrite V293_write_byte_other by exact RunningNe.
 unfold NPinitial;apply V293_write_byte_other.
 intro E;apply NotNest;symmetry;exact E.
Qed.

Lemma FWread_present : forall tp M b j v,
 (tp=Tint8 \/tp=Tptr V293_tcb_type) ->load tp M(b,j)=Some v ->
 exists i raw,get M(b,i)=Some raw.
Proof.
 intros tp M b j v [E|E] Read;subst tp;unfold load,loadm in Read;cbn[typelen loadbytes]in Read;
 destruct(@get addr(bool*memval)mem memMap M(b,j))as [raw | ] eqn:Cell;try discriminate;
 exists j;exists raw;exact Cell.
Qed.

Lemma FWentry_observations : forall br bs Mz,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->
 store Tint32(allocb(QPmemory br 1 1)bs 0%Z 4)(bs,0%Z)(Vint32 Int.zero)=Some Mz ->
 V293_sched_read_memory(V293_exit_decrement_memory Mz 96%positive 1)
 92%positive 81%positive 80%positive 16 0 1 /\
 get(V293_exit_decrement_memory Mz 96%positive 1)(91%positive,0%Z)=Some(true,Byte(Byte.repr 88)) /\
 load(Tptr V293_tcb_type)(V293_write_byte(V293_exit_decrement_memory Mz 96%positive 1)91%positive 4)
 (82%positive,(4*Z.of_nat 4)%Z)=Some(Vptr OwnershipReady).
Proof.
 intros br bs Mz FR FS Init.
 assert(Frame:forall b i,In b[80%positive;81%positive;82%positive;91%positive;92%positive] ->
 get(V293_exit_decrement_memory Mz 96%positive 1)(b,i)=get CEM(b,i)).
 { intros b i Which;apply(FWentry_frame br bs Mz FR FS Init b i).
   - destruct Which as[E|[E|[E|[E|[E|[]]]]]];subst b;discriminate.
   - destruct Which as[E|[E|[E|[E|[E|[]]]]]];subst b.
     + eapply FWread_present;[left;reflexivity|exact(proj1(proj2(proj2(proj1 CFinput))))].
     + eapply FWread_present;[left;reflexivity|exact(proj1(proj1 CFinput))].
     + eapply FWread_present;[right;reflexivity| ].
       transitivity(load(Tptr V293_tcb_type)CFfinal(82%positive,(4*Z.of_nat 4)%Z));[ |exact XPtable].
       symmetry;apply V293_load_block_frame;intro j;unfold CFfinal;apply V293_write_byte_other;discriminate.
     + exists 0%Z;exists(true,Byte(Byte.repr 88));exact(proj2 CFinput).
     + eapply FWread_present;[left;reflexivity|exact(proj1(proj2(proj1 CFinput))0 ltac:(lia))]. }
 destruct(proj1 CFinput)as[Group[Decoder[Low High]]].
 split.
 - unfold V293_sched_read_memory;split.
   + transitivity(load Tint8 CEM(81%positive,0%Z));[apply V293_load_block_frame;intros;apply Frame;simpl;tauto|exact Group].
   + split.
     * intros n Bound;transitivity(load Tint8 CEM(92%positive,Z.of_nat n));
       [apply V293_load_block_frame;intros;apply Frame;simpl;tauto|apply Decoder;exact Bound].
     * split.
       -- transitivity(load Tint8 CEM(80%positive,0%Z));[apply V293_load_block_frame;intros;apply Frame;simpl;tauto|exact Low].
       -- transitivity(load Tint8 CEM(80%positive,1%Z));[apply V293_load_block_frame;intros;apply Frame;simpl;tauto|exact High].
 - split.
   + rewrite Frame by(simpl;tauto);exact(proj2 CFinput).
   + transitivity(load(Tptr V293_tcb_type)CFfinal(82%positive,(4*Z.of_nat 4)%Z));[ |exact XPtable].
     apply V293_load_block_frame;intro i;unfold CFfinal.
     repeat rewrite V293_write_byte_other by discriminate;apply Frame;simpl;tauto.
Qed.

Theorem FWactive_resources : forall br bs,
 fresh(NPinitial 1)br ->fresh(QPmemory br 1 1)bs ->
 exists Mz Mt M1 Mc Msw Mret,
 store Tint32(allocb(QPmemory br 1 1)bs 0%Z 4)(bs,0%Z)(Vint32 Int.zero)=Some Mz /\
 evalval(V293_OSIntEnter_running 112%Z)(QPge br,V293_cpu_lenv 120%Z bs,Mz)=Some(Vint32 Int.one) /\
 load Tint8 Mz(96%positive,0%Z)=Some(V293_byteval 1) /\
 (0<1 ->exists raw,get Mz(96%positive,0%Z)=Some(true,raw)) /\
 (exists bl,get(QPge br)111%Z=Some(bl,Tint8) /\
 load Tint8(V293_exit_decrement_memory Mz 96%positive 1)(bl,0%Z)=Some(V293_byteval 0)) /\
 V293_sched_read_memory(V293_exit_decrement_memory Mz 96%positive 1)
 92%positive 81%positive 80%positive 16 0 1 /\
 get(V293_exit_decrement_memory Mz 96%positive 1)(91%positive,0%Z)=Some(true,Byte(Byte.repr 88)) /\
 load(Tptr V293_tcb_type)(V293_write_byte(V293_exit_decrement_memory Mz 96%positive 1)91%positive 4)
 (82%positive,(4*Z.of_nat 4)%Z)=Some(Vptr OwnershipReady) /\
 store(Tptr V293_tcb_type)(V293_write_byte(V293_exit_decrement_memory Mz 96%positive 1)91%positive 4)
 (93%positive,0%Z)(Vptr OwnershipReady)=Some Mt /\
 evalval(V293_OSSched_different 103%Z 108%Z)(QPge br,V293_cpu_lenv 120%Z bs,Mt)=Some(Vint32 Int.one) /\
 load Tint32 Mt(95%positive,0%Z)=Some(Vint32 Int.mone) /\
 store Tint32 Mt(95%positive,0%Z)(Vint32(Int.add Int.mone Int.one))=Some M1 /\
 evaltype(evar 108%Z)(QPge br,V293_cpu_lenv 120%Z bs,M1)=Some Tint8 /\
 evaltype(evar 103%Z)(QPge br,V293_cpu_lenv 120%Z bs,M1)=Some Tint8 /\
 evalval(evar 103%Z)(QPge br,V293_cpu_lenv 120%Z bs,M1)=Some(V293_byteval 4) /\
 evalval(eaddrof(evar 108%Z))(QPge br,V293_cpu_lenv 120%Z bs,M1)=Some(Vptr(94%positive,Int.zero)) /\
 store Tint8 M1(94%positive,0%Z)(V293_byteval 4)=Some Mc /\
 load(Tptr V293_tcb_type)Mc(93%positive,0%Z)=Some(Vptr OwnershipReady) /\
 store(Tptr V293_tcb_type)Mc(1%positive,0%Z)(Vptr OwnershipReady)=Some Msw /\
 free Tint32 98%positive Msw=Some Mret.
Proof.
 intros br bs FR FS.
 pose proof(FWinitial_owned br(V293_cpu_lenv 120%Z bs)FR)as Initial.
 destruct(V293_success_scheduler_storage(QPmemory br 1 1)bs FS)as(Mz&Init&Writable&Free&Frame).
 assert(Allocated:FWstate(QPge br)(V293_cpu_lenv 120%Z bs)Mz |=
 Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cell((br,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 1) **CPother))).
 { eapply V293_cpu_initialized_frame;[exact FS|exact Initial|exact Init]. }
 assert(ReadRunning:load Tint8 Mz(br,0%Z)=Some(V293_byteval 1)).
 { eapply V293_record_star_load_l with(s:=FWstate(QPge br)(V293_cpu_lenv 120%Z bs)Mz)
 (P:=V293_owned_record_cell((br,0%Z),Tint8,V293_byteval 1))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - clear -Allocated;sep auto. }
 assert(Running:evalval(V293_OSIntEnter_running 112%Z)(QPge br,V293_cpu_lenv 120%Z bs,Mz)=Some(Vint32 Int.one)).
 { change(evalval(ebinop oeq(ecast(evar 112%Z)Tint32)(econst32(Int.repr(Z.of_nat 1))))
 (QPge br,V293_cpu_lenv 120%Z bs,Mz)=Some(Vint32 Int.one)).
 eapply V293_success_global_byte_eq with(b:=br)(n:=1)(k:=1);try lia;try exact ReadRunning.
 - unfold V293_cpu_lenv;rewrite map_get_set' by discriminate;apply map_emp_get.
 - unfold QPge;apply map_get_set. }
 assert(ReadNest:load Tint8 Mz(96%positive,0%Z)=Some(V293_byteval 1)).
 { eapply V293_record_star_load_l with(s:=FWstate(QPge br)(V293_cpu_lenv 120%Z bs)Mz)
 (P:=V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 1))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - clear -Allocated;sep auto. }
 assert(NestOwned:FWstate(QPge br)(V293_cpu_lenv 120%Z bs)Mz |=
 V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 1) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cell((br,0%Z),Tint8,V293_byteval 1) **CPother))).
 { clear -Allocated;sep auto. }
 destruct(V293_owned_byte_update(96%positive,0%Z)(V293_byteval 1)0 _
 (QPge br)(V293_cpu_lenv 120%Z bs)Mz(fun _=>false)(false,nil,nil)
 (RIabstract OwnershipWaiting)(spec_done None)ltac:(lia)NestOwned)as[WN After].
 change(FWstate(QPge br)(V293_cpu_lenv 120%Z bs)(V293_exit_decrement_memory Mz 96%positive 1)|=
 V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 0) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cell((br,0%Z),Tint8,V293_byteval 1) **CPother)))in After.
 assert(ReadLock:load Tint8(V293_exit_decrement_memory Mz 96%positive 1)(97%positive,0%Z)=Some(V293_byteval 0)).
 { eapply V293_record_star_load_l with(s:=FWstate(QPge br)(V293_cpu_lenv 120%Z bs)(V293_exit_decrement_memory Mz 96%positive 1))
 (P:=V293_owned_record_cell((97%positive,0%Z),Tint8,V293_byteval 0))(Q:=Atrue).
 - intros st H;apply V293_owned_record_cell_load;exact H.
 - unfold CPother in After;clear -After;sep auto. }
 destruct(FWentry_observations br bs Mz FR FS Init)as[Reads[High Table]].
 set(R:=V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_owned_record_cell((97%positive,0%Z),Tint8,V293_byteval 0) **
 (Amapsto(bs,0%Z)Tint32 true(Vint32 Int.zero) **
 (V293_owned_record_cell((br,0%Z),Tint8,V293_byteval 1) **RCframe)))).
 assert(Dispatch:FWstate(QPge br)(V293_cpu_lenv 120%Z bs)(V293_exit_decrement_memory Mz 96%positive 1)|=
 SWINVt(V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 FWcells 88 OwnershipWaiting 6 Int.mone(Amapsto(98%positive,0%Z)Tint32 true(Vint32 Int.zero) **R)).
 { unfold FWcells,R,CPother in *;unfold V293_owned_record_cell in *;clear -After;sep auto. }
 destruct(FWdispatch_resources(QPge br)(V293_cpu_lenv 120%Z bs)
 (V293_exit_decrement_memory Mz 96%positive 1)R
 ltac:(intros x Which;unfold V293_cpu_lenv;rewrite map_get_set' by(destruct Which as[E|[E|[E|[E|[E|[]]]]]];subst x;discriminate);apply map_emp_get)
 ltac:(intros x Ne;unfold QPge;rewrite map_get_set' by(intro E;apply Ne;symmetry;exact E);reflexivity)
 ltac:(unfold R,RCframe;repeat split;exact I)
 (proj1(proj2 Reads))Dispatch)as(Mt&M1&Mc&Msw&Mret&D).
 exists Mz;exists Mt;exists M1;exists Mc;exists Msw;exists Mret.
 split;[exact Init| ];split;[exact Running| ];split;[exact ReadNest| ];split.
 - intros _;exact WN.
 - split.
   + exists 97%positive;split;[fw_env|exact ReadLock].
   + split;[exact Reads| ];split;[exact High| ];split;[exact Table|exact D].
Qed.

Definition FWtasks:tasks:=set RPtasks OwnershipWaiting(curs(sfexec 114%Z nil nil),(kenil,kstop)).
Definition FWos br cs ncs:osstate:=
 (QPge br,RPenvs,QPmemory br 1 1,(fun _=>false),RPaux cs ncs).

Theorem FWcomplete_active_simulation : forall br cs ncs ip,
 fresh(NPinitial 1)br ->
 ProgSim(RCprogram,(CPpo,CGempty,ip))FWtasks(FWos br cs ncs)
 SPph HPTh(RIabstract OwnershipWaiting)HPcst OwnershipWaiting.
Proof.
 intros runningblock cs ncs ip Fresh;unfold FWos.
 eapply V293_exit_active_call_progsim with(caller:=(emp:env))(si:=nil)(cs:=cs)
 (f:=114%Z)(sched:=107%Z)(exitf:=114%Z)(ks:=kstop)(entry:=sfexec 114%Z nil nil)
 (running:=112%Z)(nesting:=110%Z)(lock:=111%Z)(saved:=120%Z)
 (unmap:=100%Z)(group:=101%Z)(rows:=102%Z)(high:=103%Z)(y:=104%Z)
 (table:=105%Z)(target:=106%Z)(current:=108%Z)(counter:=109%Z)
 (bt:=92%positive)(bg:=81%positive)(br:=80%positive)(bh:=91%positive)(bp:=82%positive)
 (bo:=93%positive)(bn:=96%positive)(bk:=95%positive)(bcache:=94%positive)(bc:=1%positive)
 (lo:=16)(hi:=0)(g:=1)(n:=1)(count:=Int.mone)(tp:=V293_tcb_type)
 (value:=Vptr OwnershipReady)(v:=V293_byteval 4)(next:=OwnershipReady)
 (nextbody:=CPfullbody)(nextcaller:=(emp:env))(nexttail:=kstop)(nexttau:=Tvoid)
 (nextd1:=dnil)(nextd2:=dcons 120%Z Tint32 dnil)(nextsaved:=120%Z)(nextbs:=98%positive)
 (nsi:=nil)(ncs:=ncs)(Thf:=HPThf)(Of:=SPOf);
 try reflexivity;try discriminate;try lia;
 try(apply map_get_set);
 try(unfold QPge;rewrite map_get_set' by discriminate;reflexivity).
 - eapply hp_stepS;[apply HPschedule|apply hp_stepO].
 - exists 4;left;repeat split;try lia;reflexivity.
 - change(4<13);lia.
 - left;reflexivity.
 - intros bs SavedFresh.
   destruct(FWactive_resources runningblock bs Fresh SavedFresh)as
   (Mz&Mt&M1&Mc&Msw&Mret&Init&Running&Nest&Writable&Lock&Reads&High&Table&TargetStore&Guard&Counter&Increment&CurrentType&HighType&HighValue&Address&Copy&Target&Store&Free).
   exists Mz;exists Mt;exists M1;exists Mc;exists Msw;exists Mret;exists(Byte(Byte.repr 88)).
   split;[exact Init| ];split;[exact Running| ];split;[exact Nest| ];split;[exact Writable| ];split;[exact Lock| ];
   split;[exact Reads| ];split;[exact High| ];split;[exact Table| ];split;[exact TargetStore| ];
   split;[exact Guard| ];split;[exact Counter| ];split;[exact Increment| ];split;[exact CurrentType| ];
   split;[exact HighType| ];split;[exact HighValue| ];split;[exact Address| ];split;[exact Copy| ];
   split;[exact Target| ];split;[exact Store| ];split;[exact Free| ].
   eapply SPterminal;[apply map_get_set| |unfold SPOf;apply map_get_set].
   unfold projS,projD;cbn;repeat rewrite map_get_set;reflexivity.
Qed.

Theorem FWnonvacuous : exists br,
 fresh(NPinitial 1)br /\
 (forall le,FWstate(QPge br)le(QPmemory br 1 1) |=
 V293_owned_record_cell((br,0%Z),Tint8,V293_byteval 1) **
 V293_owned_record_cell((96%positive,0%Z),Tint8,V293_byteval 1) **CPother) /\
 (forall cs ncs ip,
 ProgSim(RCprogram,(CPpo,CGempty,ip))FWtasks(FWos br cs ncs)
 SPph HPTh(RIabstract OwnershipWaiting)HPcst OwnershipWaiting).
Proof.
 destruct(memory_has_fresh_block(NPinitial 1))as[br Fresh].
 exists br;split;[exact Fresh| ];split.
 - intros le;apply FWinitial_owned;exact Fresh.
 - intros cs ncs ip;apply FWcomplete_active_simulation;exact Fresh.
Qed.

Theorem FWpending_contract_control :
 get FWtasks OwnershipReady=Some RPpending /\
 ~get(set FWtasks OwnershipReady(SKIP,(kenil,kstop)))OwnershipReady=Some RPpending.
Proof.
 split.
 - unfold FWtasks,RPtasks;rewrite map_get_set' by discriminate.
   rewrite map_get_set' by discriminate;apply map_get_sig.
 - rewrite map_get_set;unfold RPpending;intro E;inversion E.
Qed.
