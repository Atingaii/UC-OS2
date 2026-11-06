(* Independent nonempty locked heap; no saved local or helper binding. *)
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293ExitNestedCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitCriticalPrefixTaskSim.
Require Import CertiOS.audit.probes.V293ExitActiveCallTaskSimProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitLockedCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitActiveCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyTaskInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchStorage.
Require Import CertiOS.certiucos.v293.proofs.V293DispatchState.
Require Import CertiOS.certiucos.v293.proofs.V293HandoffProgSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitBoundarySwitch.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedStoragePrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TimeTickStorage.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSIntEnter.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.framework.proof.rulesoundlib.
Require Import CertiOS.framework.proof.invariant_prop.
Require Import CertiOS.framework.proof.lmachLib.
Require Import CertiOS.framework.auxlibs.MapLib.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Local Open Scope list_scope.
Definition LCcells n l : list V293_record_cell :=
 (((150%positive,0%Z),Tint8,V293_byteval n)::
 ((151%positive,0%Z),Tint8,V293_byteval l)::
 ((152%positive,0%Z),Tint8,V293_byteval 1)::
 ((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting)::nil).
Definition LCoutputs n l:=OwnershipCellsMemory(LCcells n l).
Definition LCmemory n l:=merge(RTfull OwnershipWaiting)(LCoutputs n l).
Definition LCresource:=V293_exit_locked_resource 80%positive 81%positive 82%positive
 150%positive 151%positive 152%positive 106%Z V293_tcb_type nil OwnershipWaiting.
Definition LCinv:=V293_ready_storage_inv 80%positive 81%positive 82%positive
 106%Z V293_tcb_type (((150%positive,0%Z),Tint8)::((151%positive,0%Z),Tint8)::((152%positive,0%Z),Tint8)::nil).
Definition LCpo:progunit:=fun f=>if Z.eq_dec f 114%Z then Some
 (V293_exit_boundary_function 132%Z 130%Z 131%Z 120%Z
 105%Z 103%Z 106%Z 108%Z 109%Z 107%Z(V293_interrupt_handoff 103%Z 108%Z 106%Z))else None.
Definition LCspec:osspec:=((fun f=>if Z.eq_dec f 114%Z then
 Some((fun _:vallist=>spec_done None),(Tvoid,nil))else None),(fun _=>None),V293_scheduler).

Lemma LCjoin : forall n l,join(RTfull OwnershipWaiting)(LCoutputs n l)(LCmemory n l).
Proof.
 intros n l;apply map_join_merge;apply map_disjoint;intros[b i].
 destruct(in_dec Pos.eq_dec b (150%positive::151%positive::152%positive::93%positive::nil))as[E|NE].
 - left;repeat destruct E as[<-|E];try(apply RToutside;discriminate);contradiction.
 - right;left;apply OwnershipCellsOutside;vm_compute in NE|-*;intuition congruence.
Qed.
Lemma LCtarget : forall m o,
 V293_target_wstate ACge ACle m o|=
 V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) ->
 V293_target_wstate ACge ACle m o|=V293_dispatch_cell 106%Z V293_tcb_type.
Proof.
 intros m o H;unfold V293_dispatch_cell.
 apply astar_l_apure_elim in H;destruct H as[Typed H].
 exists(Vptr OwnershipWaiting);apply astar_l_apure_intro;[ |exact Typed].
 exists 93%positive;unfold Agvarenv',Aptrmapsto;cbn[addrval_to_addr].
 apply astar_l_agvarenv_intro;[exact H|split;reflexivity].
Qed.
Lemma LCbase : forall n l,n<256 ->l<256 ->
 V293_target_wstate ACge ACle(LCmemory n l)(RIabstract OwnershipWaiting)|=LCresource n l.
Proof.
 intros n l NB LB.
 assert(Outputs:V293_target_wstate ACge ACle(LCoutputs n l)emp|=V293_owned_record_cells(LCcells n l)).
 { apply OwnershipCellsSpatial;[vm_compute;repeat split;intros;intuition congruence|
   repeat constructor;try(apply V293_byte_type;lia);vm_compute;reflexivity]. }
 assert(Ready:V293_target_wstate ACge ACle(RTfull OwnershipWaiting)(RIabstract OwnershipWaiting)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting).
 { apply RTenv_spatial;reflexivity. }
 assert(All:V293_target_wstate ACge ACle(LCmemory n l)(RIabstract OwnershipWaiting)|=
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 V293_owned_record_cells(LCcells n l)).
 { eapply V293_target_wstate_star;[exact(LCjoin n l)|apply map_join_emp|exact Ready|exact Outputs]. }
 cbn[LCcells V293_owned_record_cells]in All.
 assert(Targets:V293_target_wstate ACge ACle(LCmemory n l)(RIabstract OwnershipWaiting)|=
 V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (V293_owned_record_cell((150%positive,0%Z),Tint8,V293_byteval n) **
 (V293_owned_record_cell((151%positive,0%Z),Tint8,V293_byteval l) **
 (V293_owned_record_cell((152%positive,0%Z),Tint8,V293_byteval 1) **
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting))))by(sep auto).
 apply sat_split in Targets;destruct Targets as(mt&mr&ot&orr&JM&JO&Cell&Rest).
 apply LCtarget in Cell.
 assert(Targets:V293_target_wstate ACge ACle(LCmemory n l)(RIabstract OwnershipWaiting)|=
 V293_dispatch_cell 106%Z V293_tcb_type **
 (V293_owned_record_cell((150%positive,0%Z),Tint8,V293_byteval n) **
 (V293_owned_record_cell((151%positive,0%Z),Tint8,V293_byteval l) **
 (V293_owned_record_cell((152%positive,0%Z),Tint8,V293_byteval 1) **
 SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting)))).
 { apply sat_split';exists mt;exists mr;exists ot;exists orr;repeat first[assumption|split]. }
 unfold SWINVt in Targets;fold(CurTid OwnershipWaiting)in Targets.
 assert(Pack:V293_target_wstate ACge ACle(LCmemory n l)(RIabstract OwnershipWaiting)|=
 SWINV(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive) **
 (V293_dispatch_cell 106%Z V293_tcb_type **
 (V293_owned_record_cell((150%positive,0%Z),Tint8,V293_byteval n) **
 (V293_owned_record_cell((151%positive,0%Z),Tint8,V293_byteval l) **
 (V293_owned_record_cell((152%positive,0%Z),Tint8,V293_byteval 1) **CurTid OwnershipWaiting)))))by(sep auto).
 eapply astar_mono in Pack;[ |apply V293ReadyTaskInvariant.V293_ready_switch_open|intros st H;exact H].
 assert(Empty:V293_shared_flags ==>Aemp).
 { intros s Flags;unfold V293_shared_flags in Flags.
   apply astar_l_aemp_elim.
   eapply astar_mono with(P:=isrclr **Aie false)(Q:=EX k:hid,ATopis k);
   [ |intros s0[k[_ E]];exact E|exact Flags].
   intros s0 F;apply astar_l_aemp_elim.
   eapply astar_mono with(P:=isrclr)(Q:=Aie false);
   [ |intros s1[_ E];exact E|exact F].
   intros s1[r[Flag Clear]];exact(proj2 Flag). }
 assert(NoFlags:V293_target_wstate ACge ACle(LCmemory n l)(RIabstract OwnershipWaiting)|=
 V293ReadyTaskInvariant.V293_ready_core 80%positive 81%positive 82%positive **
 (V293_dispatch_cell 106%Z V293_tcb_type **
 (V293_owned_record_cell((150%positive,0%Z),Tint8,V293_byteval n) **
 (V293_owned_record_cell((151%positive,0%Z),Tint8,V293_byteval l) **
 (V293_owned_record_cell((152%positive,0%Z),Tint8,V293_byteval 1) **CurTid OwnershipWaiting))))).
 { apply astar_l_aemp_elim;eapply astar_mono;[exact Empty|intros st H;exact H| ].
   clear Empty;sep auto. }
 unfold LCresource,V293_exit_locked_resource,V293_locked_guard_resource,V293_ready_storage_core,V293_ready_storage_extra.
 cbn[V293_storage];clear -NoFlags;sep auto.
Qed.
Theorem LCnonempty_client_call : forall n l ip,n<256 ->0<l ->l<256 ->
 TaskSim(RCprogram,(LCpo,CGempty,ip))(curs(scall 114%Z nil),(kenil,kstop))
 (ACge,ACle,LCmemory n l,(fun _=>false),(false,nil,nil))
 (RCprogram,LCspec)(curs(scall 114%Z nil),(kenil,kstop))
 (RIabstract OwnershipWaiting)V293_shared_li LCinv
 (fun st=>satp(fst st)(snd st)(RDYINV LCinv OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.
Proof.
 intros n l ip NB LP LB;unfold LCinv,ACle.
 eapply V293_exit_locked_client_call_TaskSim with(saved:=120%Z)(running:=132%Z)(nesting:=130%Z)(lock:=131%Z)(n:=n)(l:=l).
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - right;right;reflexivity.
 - reflexivity.
 - exact NB.
 - exact LP.
 - exact LB.
 - discriminate.
 - discriminate.
 - discriminate.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - apply LCbase;assumption.
Qed.

(* Change only lock=1 to lock=0; this does not execute the dispatch branch. *)
Theorem LClock_control : exists M0,
 load Tint8(LCmemory 1 1)(151%positive,0%Z)=Some(V293_byteval 1) /\
 store Tint8(LCmemory 1 1)(151%positive,0%Z)(V293_byteval 0)=Some M0 /\
 load Tint8 M0(151%positive,0%Z)=Some(V293_byteval 0) /\
 (forall b i,(b,i)<>(151%positive,0%Z) ->get M0(b,i)=get(LCmemory 1 1)(b,i)) /\
 evalval(V293_OSSched_zero 131%Z)(ACge,ACle,LCmemory 1 1)=Some(Vint32 Int.zero) /\
 evalval(V293_OSSched_zero 131%Z)(ACge,ACle,M0)=Some(Vint32 Int.one).
Proof.
 pose proof(LCbase 1 1 ltac:(lia)ltac:(lia))as Base.
 unfold LCresource,V293_exit_locked_resource,V293_locked_guard_resource in Base.
 assert(Pack:V293_target_wstate ACge ACle(LCmemory 1 1)(RIabstract OwnershipWaiting)|=
 V293_owned_record_cell((151%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((152%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((150%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_ready_storage_core 80%positive 81%positive 82%positive 106%Z V293_tcb_type nil **CurTid OwnershipWaiting)))).
 { clear -Base;sep auto. }
 assert(Read:load Tint8(LCmemory 1 1)(151%positive,0%Z)=Some(V293_byteval 1)).
 { change(load Tint8(assertion.getmem(V293_target_wstate ACge ACle(LCmemory 1 1)(RIabstract OwnershipWaiting)))
 (151%positive,0%Z)=Some(V293_byteval 1)).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Pack]. }
 destruct(V293_owned_record_cell_update (151%positive,0%Z) Tint8 (V293_byteval 1)(V293_byteval 0)
 _ _ _ _ _ _ _ _ eq_refl Pack)as(M0&Store&After).
 assert(ReadAfter:load Tint8 M0(151%positive,0%Z)=Some(V293_byteval 0)).
 { change(load Tint8(assertion.getmem(V293_target_wstate ACge ACle M0(RIabstract OwnershipWaiting)))
 (151%positive,0%Z)=Some(V293_byteval 0)).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact After]. }
 exists M0;split;[exact Read| ];split;[exact Store| ];split;[exact ReadAfter| ];split.
 - intros b i Different;eapply V293_storebytes_outside;[exact Store| ].
   destruct(Pos.eq_dec b 151%positive)as[Same|Other];[subst b|left;exact Other].
   right;assert(i<>0%Z)by(intro E;apply Different;congruence).
   cbn[encode_val V293_byteval inj_bytes encode_int List.map length];lia.
 - split.
   + eapply V293_nested_zero_eval with(n:=1);[lia|lia|reflexivity|reflexivity|exact Read].
   + eapply V293_exit_zero_eval;[reflexivity|reflexivity|exact ReadAfter].
Qed.
