(* Same full AC input, changing only the running byte; exact ACinv retained. *)
Require Import CertiOS.audit.probes.V293ExitActiveCallTaskSimProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitQuietCallTaskSim.
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
Require Import CertiOS.audit.probes.V293ExitQuietCallTaskSimProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitQuietStorageCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitCriticalPrefixTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperBodyTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperTaskSim.
Require Import CertiOS.certiucos.v293.code.V293ReadyTable.
Require Import CertiOS.certiucos.v293.proofs.V293ExitHelperTargetTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293OSIntExitSharedReclose.
Import ListNotations.
Local Open Scope list_scope.

Definition QSprefix:=
 (((94%positive,0%Z),Tint8)::((91%positive,0%Z),Tint8)::((95%positive,0%Z),Tint32)::nil)++
 (V293_array_cells 92%positive 0%Z 1%Z Tint8(length V293_ready_table)++
 (((150%positive,0%Z),Tint8)::((151%positive,0%Z),Tint8)::nil)).
Definition QSresource:=V293_exit_quiet_resource 80%positive 81%positive 82%positive
 152%positive 106%Z V293_tcb_type (QSprefix++nil) OwnershipWaiting.
Definition QSrest n:=V293_exit_guard_resource 150%positive 151%positive n
 (V293_helper_resource 80%positive 81%positive 82%positive 92%positive 91%positive OwnershipWaiting
 (V293_exit_active_frame 92%positive 94%positive 93%positive 95%positive nil
 6(Vptr OwnershipWaiting)Int.mone)(V293_byteval 88)).

Lemma QSupdated_resource : forall n M,
 V293_target_wstate ACge ACle M(RIabstract OwnershipWaiting)|=
 V293_owned_record_cell((152%positive,0%Z),Tint8,V293_byteval 0) **QSrest n ->
 V293_target_wstate ACge ACle M(RIabstract OwnershipWaiting)|=QSresource.
Proof.
 intros n M Held.
 assert(CellsOwned:
 V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **
 (V293_read_bytes 92%positive 0%Z V293_ready_table **
 (V293_read_bytes 92%positive 0%Z V293_ready_table **
 (V293_owned_record_cell((150%positive,0%Z),Tint8,V293_byteval n) **
 (V293_owned_record_cell((151%positive,0%Z),Tint8,V293_byteval 0) **Aemp)))))) ==>
 V293_storage QSprefix).
 { intros s H.
   assert(Pair:s|=(V293_read_bytes 92%positive 0%Z V293_ready_table **
    V293_read_bytes 92%positive 0%Z V293_ready_table) **
    (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
    (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
    (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **
    (V293_owned_record_cell((150%positive,0%Z),Tint8,V293_byteval n) **
    (V293_owned_record_cell((151%positive,0%Z),Tint8,V293_byteval 0) **Aemp))))))by(sep auto).
   eapply astar_mono in Pair;[ |apply V293_helper_decoder_storage|intros st H';exact H'].
   assert(Pack:s|=V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
    (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
    (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **
    (V293_storage(V293_array_cells 92%positive 0%Z 1%Z Tint8(length V293_ready_table)) **
    (V293_owned_record_cell((150%positive,0%Z),Tint8,V293_byteval n) **
    (V293_owned_record_cell((151%positive,0%Z),Tint8,V293_byteval 0) **Aemp))))))by(clear H;sep auto).
   unfold QSprefix;cbn[V293_storage app].
   eapply astar_mono;[apply V293_exit_cell_to_storage| |exact Pack].
   apply astar_mono;[apply V293_exit_cell_to_storage| ].
   apply astar_mono;[apply V293_exit_cell_to_storage| ].
   intros st Owned;apply V293_storage_append.
   eapply astar_mono;[intros st' H';exact H'| |exact Owned].
   cbn[V293_storage];repeat apply astar_mono;try(intros st' H';exact H');
   apply V293_exit_cell_to_storage. }
 assert(Pack:V293_target_wstate ACge ACle M(RIabstract OwnershipWaiting)|=
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **
 (V293_read_bytes 92%positive 0%Z V293_ready_table **
 (V293_read_bytes 92%positive 0%Z V293_ready_table **
 (V293_owned_record_cell((150%positive,0%Z),Tint8,V293_byteval n) **
 (V293_owned_record_cell((151%positive,0%Z),Tint8,V293_byteval 0) **Aemp))))))) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 V293_owned_record_cell((152%positive,0%Z),Tint8,V293_byteval 0)))).
 { unfold QSrest,V293_exit_guard_resource,V293_helper_resource,V293_exit_active_frame in Held.
   cbn[V293_storage]in Held;sep auto. }
 eapply astar_mono in Pack;[ |exact CellsOwned|intros st H;exact H].
 assert(Reorder:V293_target_wstate ACge ACle M(RIabstract OwnershipWaiting)|=
 V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((152%positive,0%Z),Tint8,V293_byteval 0) **V293_storage QSprefix)))by(clear Held;sep auto).
 apply sat_split in Reorder;destruct Reorder as(mt&mr&ot&orr&JM&JO&Cell&Rest).
 apply QCtarget in Cell.
 assert(Targets:V293_target_wstate ACge ACle M(RIabstract OwnershipWaiting)|=
 V293_dispatch_cell 106%Z V293_tcb_type **
 (SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((152%positive,0%Z),Tint8,V293_byteval 0) **V293_storage QSprefix))).
 { apply sat_split';exists mt;exists mr;exists ot;exists orr;repeat first[assumption|split]. }
 unfold SWINVt in Targets;fold(CurTid OwnershipWaiting)in Targets.
 assert(Open:V293_target_wstate ACge ACle M(RIabstract OwnershipWaiting)|=
 SWINV(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive) **
 (V293_dispatch_cell 106%Z V293_tcb_type **
 (V293_owned_record_cell((152%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_storage QSprefix **CurTid OwnershipWaiting))))by(sep auto).
 eapply astar_mono in Open;[ |apply V293ReadyTaskInvariant.V293_ready_switch_open|intros st H;exact H].
 assert(Empty:V293_shared_flags ==>Aemp).
 { intros s Flags;unfold V293_shared_flags in Flags.
   apply astar_l_aemp_elim.
   eapply astar_mono with(P:=isrclr **Aie false)(Q:=EX k:hid,ATopis k);
   [ |intros s0[k[_ E]];exact E|exact Flags].
   intros s0 F;apply astar_l_aemp_elim.
   eapply astar_mono with(P:=isrclr)(Q:=Aie false);
   [ |intros s1[_ E];exact E|exact F].
   intros s1[r[Flag Clear]];exact(proj2 Flag). }
 assert(NoFlags:V293_target_wstate ACge ACle M(RIabstract OwnershipWaiting)|=
 V293ReadyTaskInvariant.V293_ready_core 80%positive 81%positive 82%positive **
 (V293_dispatch_cell 106%Z V293_tcb_type **
 (V293_owned_record_cell((152%positive,0%Z),Tint8,V293_byteval 0) **
 (V293_storage QSprefix **CurTid OwnershipWaiting)))).
 { apply astar_l_aemp_elim;eapply astar_mono;[exact Empty|intros s H;exact H| ].
   clear Empty;sep auto. }
 unfold QSresource,V293_exit_quiet_resource,V293_ready_storage_core,V293_ready_storage_extra.
 rewrite app_nil_r;clear -NoFlags;sep auto.
Qed.

Lemma QSsame_invariant :
 V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type
 (QSprefix++((152%positive,0%Z),Tint8)::nil)=ACinv.
Proof.
 unfold QSprefix,ACinv,ACrest.
 rewrite <-app_assoc;reflexivity.
Qed.

Theorem QSnonempty_client_call : forall M ip,
 V293_target_wstate ACge ACle M(RIabstract OwnershipWaiting)|=QSresource ->
 TaskSim(RCprogram,(ACpo,CGempty,ip))(curs(scall 114%Z nil),(kenil,kstop))
 (ACge,ACle,M,(fun _=>false),(false,nil,nil))
 (RCprogram,QCspec)(curs(scall 114%Z nil),(kenil,kstop))
 (RIabstract OwnershipWaiting)V293_shared_li ACinv
 (fun st=>satp(fst st)(snd st)(RDYINV ACinv OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.
Proof.
 intros M ip Held;rewrite <-QSsame_invariant;unfold ACle.
 eapply V293_exit_quiet_storage_client_call_TaskSim with(saved:=120%Z)(running:=132%Z).
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - right;right;reflexivity.
 - reflexivity.
 - discriminate.
 - reflexivity.
 - exact Held.
Qed.

(* Single-factor full-input contrast, not a claim of one common abstract API. *)
Theorem QSrunning_single_factor_complete_call : forall n ip,
 n<256 ->exists M0,
 load Tint8(ACmemory n)(152%positive,0%Z)=Some(V293_byteval 1) /\
 store Tint8(ACmemory n)(152%positive,0%Z)(V293_byteval 0)=Some M0 /\
 load Tint8 M0(152%positive,0%Z)=Some(V293_byteval 0) /\
 (forall b i,(b,i)<>(152%positive,0%Z) ->get M0(b,i)=get(ACmemory n)(b,i)) /\
 evalval(V293_OSIntEnter_running 132%Z)(ACge,ACle,ACmemory n)=Some(Vint32 Int.one) /\
 evalval(V293_OSIntEnter_running 132%Z)(ACge,ACle,M0)=Some(Vint32 Int.zero) /\
 TaskSim(RCprogram,(ACpo,CGempty,ip))(curs(scall 114%Z nil),(kenil,kstop))
 (ACge,ACle,M0,(fun _=>false),(false,nil,nil))
 (RCprogram,QCspec)(curs(scall 114%Z nil),(kenil,kstop))
 (RIabstract OwnershipWaiting)V293_shared_li ACinv
 (fun st=>satp(fst st)(snd st)(RDYINV ACinv OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.
Proof.
 intros n ip Bound.
 pose proof(ACbase n Bound)as Base.
 change(V293_target_wstate ACge ACle(ACmemory n)(RIabstract OwnershipWaiting)|=
 V293_owned_record_cell((152%positive,0%Z),Tint8,V293_byteval 1) **QSrest n)in Base.
 assert(Read:load Tint8(ACmemory n)(152%positive,0%Z)=Some(V293_byteval 1)).
 { change(load Tint8(assertion.getmem(V293_target_wstate ACge ACle(ACmemory n)(RIabstract OwnershipWaiting)))
 (152%positive,0%Z)=Some(V293_byteval 1)).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Base]. }
 destruct(V293_owned_record_cell_update ((152%positive,0%Z)) Tint8 (V293_byteval 1) (V293_byteval 0) _ _ _ _ _ _ _ _ eq_refl Base)
 as(M0&Store&After).
 assert(ReadAfter:load Tint8 M0(152%positive,0%Z)=Some(V293_byteval 0)).
 { change(load Tint8(assertion.getmem(V293_target_wstate ACge ACle M0(RIabstract OwnershipWaiting)))
 (152%positive,0%Z)=Some(V293_byteval 0)).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact After]. }
 exists M0;split;[exact Read| ];split;[exact Store| ];split;[exact ReadAfter| ];split.
 - intros b i Different;eapply V293_storebytes_outside;[exact Store| ].
   destruct(Pos.eq_dec b 152%positive)as[Same|Other];[subst b|left;exact Other].
   right;assert(i<>0%Z)by(intro E;apply Different;congruence).
   cbn[encode_val V293_byteval inj_bytes encode_int List.map length];lia.
 - split.
   + eapply V293_exit_active_running_eval;[reflexivity|reflexivity|exact Read].
   + split.
     * eapply V293_quiet_running_eval;[reflexivity|reflexivity|exact ReadAfter].
     * apply QSnonempty_client_call;eapply QSupdated_resource;exact After.
Qed.
