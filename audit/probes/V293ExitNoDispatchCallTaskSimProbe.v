(* Full AC inputs; one no-dispatch API and invariant for nested/locked/quiet. *)
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

Require Import CertiOS.certiucos.v293.proofs.V293ExitNoDispatchCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitLockedCallTaskSim.
Require Import CertiOS.audit.probes.V293ExitQuietStorageCallTaskSimProbe.

Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.

Require Import CertiOS.certiucos.v293.proofs.V293ExitNestedCallTaskSim.

Definition NDprefix:=
 (((94%positive,0%Z),Tint8)::((91%positive,0%Z),Tint8)::((95%positive,0%Z),Tint32)::nil)++
 V293_array_cells 92%positive 0%Z 1%Z Tint8(length V293_ready_table).
Definition NDresource:=V293_exit_locked_resource 80%positive 81%positive 82%positive
 150%positive 151%positive 152%positive 106%Z V293_tcb_type (NDprefix++nil) OwnershipWaiting.
Definition NDrest n:=
 V293_owned_record_cell((152%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((150%positive,0%Z),Tint8,V293_byteval n) **
 V293_helper_resource 80%positive 81%positive 82%positive 92%positive 91%positive OwnershipWaiting
 (V293_exit_active_frame 92%positive 94%positive 93%positive 95%positive nil
 6(Vptr OwnershipWaiting)Int.mone)(V293_byteval 88)).

Lemma NDupdated_resource : forall n l M,
 V293_target_wstate ACge ACle M(RIabstract OwnershipWaiting)|=
 V293_owned_record_cell((151%positive,0%Z),Tint8,V293_byteval l) **NDrest n ->
 V293_target_wstate ACge ACle M(RIabstract OwnershipWaiting)|=NDresource n l.
Proof.
 intros n l M Held.
 assert(CellsOwned:
 V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **
 (V293_read_bytes 92%positive 0%Z V293_ready_table **
 (V293_read_bytes 92%positive 0%Z V293_ready_table **
 (Aemp))))) ==>
 V293_storage NDprefix).
 { intros s H.
   assert(Pair:s|=(V293_read_bytes 92%positive 0%Z V293_ready_table **V293_read_bytes 92%positive 0%Z V293_ready_table) **
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **
 (Aemp)))))by(sep auto).
   eapply astar_mono in Pair;[ |apply V293_helper_decoder_storage|intros st H';exact H'].
   assert(Pack:s|=V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **
 (V293_storage(V293_array_cells 92%positive 0%Z 1%Z Tint8(length V293_ready_table)) **
 (Aemp)))))by(clear H;sep auto).
   unfold NDprefix;cbn[V293_storage app].
   eapply astar_mono;[apply V293_exit_cell_to_storage| |exact Pack].
   apply astar_mono;[apply V293_exit_cell_to_storage| ].
   apply astar_mono;[apply V293_exit_cell_to_storage| ].
   intros st H';apply astar_r_aemp_elim in H';exact H'. }
 assert(Pack:V293_target_wstate ACge ACle M(RIabstract OwnershipWaiting)|=
 (V293_owned_record_cell((94%positive,0%Z),Tint8,V293_byteval 6) **
 (V293_owned_record_cell((91%positive,0%Z),Tint8,V293_byteval 88) **
 (V293_owned_record_cell((95%positive,0%Z),Tint32,Vint32 Int.mone) **
 (V293_read_bytes 92%positive 0%Z V293_ready_table **
 (V293_read_bytes 92%positive 0%Z V293_ready_table **
 (Aemp)))))) **
 (V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((151%positive,0%Z),Tint8,V293_byteval l) **
 (V293_owned_record_cell((152%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((150%positive,0%Z),Tint8,V293_byteval n))))))).
 { unfold NDrest,V293_helper_resource,V293_exit_active_frame in Held.
   cbn[V293_storage]in Held;sep auto. }
 eapply astar_mono in Pack;[ |exact CellsOwned|intros st H;exact H].
 assert(Reorder:V293_target_wstate ACge ACle M(RIabstract OwnershipWaiting)|=
 V293_owned_record_cell((93%positive,0%Z),Tptr V293_tcb_type,Vptr OwnershipWaiting) **
 (SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((151%positive,0%Z),Tint8,V293_byteval l) **
 (V293_owned_record_cell((152%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((150%positive,0%Z),Tint8,V293_byteval n) **
 (V293_storage NDprefix))))))by(clear Held;sep auto).
 apply sat_split in Reorder;destruct Reorder as(mt&mr&ot&orr&JM&JO&Cell&Rest).
 apply QCtarget in Cell.
 assert(Targets:V293_target_wstate ACge ACle M(RIabstract OwnershipWaiting)|=
 V293_dispatch_cell 106%Z V293_tcb_type **
 (SWINVt(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive)OwnershipWaiting **
 (V293_owned_record_cell((151%positive,0%Z),Tint8,V293_byteval l) **
 (V293_owned_record_cell((152%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((150%positive,0%Z),Tint8,V293_byteval n) **
 (V293_storage NDprefix)))))).
 { apply sat_split';exists mt;exists mr;exists ot;exists orr;repeat first[assumption|split]. }
 unfold SWINVt in Targets;fold(CurTid OwnershipWaiting)in Targets.
 assert(Open:V293_target_wstate ACge ACle M(RIabstract OwnershipWaiting)|=
 SWINV(V293ReadyTaskInvariant.V293_ready_inv 80%positive 81%positive 82%positive) **
 (V293_dispatch_cell 106%Z V293_tcb_type **
 (V293_owned_record_cell((151%positive,0%Z),Tint8,V293_byteval l) **
 (V293_owned_record_cell((152%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((150%positive,0%Z),Tint8,V293_byteval n) **
 (V293_storage NDprefix **
 (CurTid OwnershipWaiting)))))))by(sep auto).
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
 (V293_owned_record_cell((151%positive,0%Z),Tint8,V293_byteval l) **
 (V293_owned_record_cell((152%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((150%positive,0%Z),Tint8,V293_byteval n) **
 (V293_storage NDprefix **
 (CurTid OwnershipWaiting))))))).
 { apply astar_l_aemp_elim;eapply astar_mono;[exact Empty|intros s H;exact H| ].
   clear Empty;sep auto. }
 unfold NDresource,V293_exit_locked_resource,V293_locked_guard_resource,
 V293_ready_storage_core,V293_ready_storage_extra.
 rewrite app_nil_r;clear -NoFlags;sep auto.
Qed.

Lemma NDsame_invariant :
 V293_ready_storage_inv 80%positive 81%positive 82%positive 106%Z V293_tcb_type
 (NDprefix++((150%positive,0%Z),Tint8)::((151%positive,0%Z),Tint8)::((152%positive,0%Z),Tint8)::nil)=ACinv.
Proof.
 unfold NDprefix,ACinv,ACrest;rewrite <-app_assoc;reflexivity.
Qed.

Theorem NDnonempty_client_call : forall n l M ip,
 n<256 ->l<256 ->(2<=n \/ 0<l) ->
 V293_target_wstate ACge ACle M(RIabstract OwnershipWaiting)|=NDresource n l ->
 TaskSim(RCprogram,(ACpo,CGempty,ip))(curs(scall 114%Z nil),(kenil,kstop))
 (ACge,ACle,M,(fun _=>false),(false,nil,nil))
 (RCprogram,QCspec)(curs(scall 114%Z nil),(kenil,kstop))
 (RIabstract OwnershipWaiting)V293_shared_li ACinv
 (fun st=>satp(fst st)(snd st)(RDYINV ACinv OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.
Proof.
 intros n l M ip NB LB Stop Held;rewrite <-NDsame_invariant;unfold ACle.
 eapply V293_exit_no_dispatch_client_call_TaskSim with(saved:=120%Z)(running:=132%Z)
 (nesting:=130%Z)(lock:=131%Z)(n:=n)(l:=l).
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - right;right;reflexivity.
 - reflexivity.
 - discriminate.
 - discriminate.
 - discriminate.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - right;apply astar_l_apure_intro;[exact Held|repeat split;assumption].
Qed.

Theorem NDnested_original_input_call : forall n ip,2<=n ->n<256 ->
 TaskSim(RCprogram,(ACpo,CGempty,ip))(curs(scall 114%Z nil),(kenil,kstop))
 (ACge,ACle,ACmemory n,(fun _=>false),(false,nil,nil))
 (RCprogram,QCspec)(curs(scall 114%Z nil),(kenil,kstop))
 (RIabstract OwnershipWaiting)V293_shared_li ACinv
 (fun st=>satp(fst st)(snd st)(RDYINV ACinv OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.
Proof.
 intros n ip Lower Bound;apply NDnonempty_client_call with(n:=n)(l:=0);try lia.
 apply NDupdated_resource;pose proof(ACbase n Bound)as Held.
 unfold ACresource,V293_exit_active_resource,V293_exit_guard_resource,NDrest in *;sep auto.
Qed.

Theorem NDquiet_original_API_call : forall M ip,
 V293_target_wstate ACge ACle M(RIabstract OwnershipWaiting)|=QSresource ->
 TaskSim(RCprogram,(ACpo,CGempty,ip))(curs(scall 114%Z nil),(kenil,kstop))
 (ACge,ACle,M,(fun _=>false),(false,nil,nil))
 (RCprogram,QCspec)(curs(scall 114%Z nil),(kenil,kstop))
 (RIabstract OwnershipWaiting)V293_shared_li ACinv
 (fun st=>satp(fst st)(snd st)(RDYINV ACinv OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.
Proof.
 intros M ip Held;rewrite <-NDsame_invariant;unfold ACle.
 eapply V293_exit_no_dispatch_client_call_TaskSim with(saved:=120%Z)(running:=132%Z)
 (nesting:=130%Z)(lock:=131%Z)(n:=0)(l:=0).
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - right;right;reflexivity.
 - reflexivity.
 - discriminate.
 - discriminate.
 - discriminate.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - left;unfold QSresource,QSprefix,NDprefix in *.
   rewrite app_nil_r in Held;rewrite <-app_assoc;exact Held.
Qed.

(* Only lock changes in the complete pre-call input; not a return-frame claim. *)
Theorem NDlock_single_factor_complete_call : forall n l ip,
 n<256 ->l<256 ->(2<=n \/ 0<l) ->exists Ml,
 load Tint8(ACmemory n)(151%positive,0%Z)=Some(V293_byteval 0) /\
 store Tint8(ACmemory n)(151%positive,0%Z)(V293_byteval l)=Some Ml /\
 load Tint8 Ml(151%positive,0%Z)=Some(V293_byteval l) /\
 (forall b i,(b,i)<>(151%positive,0%Z) ->get Ml(b,i)=get(ACmemory n)(b,i)) /\
 evalval(V293_OSSched_zero 131%Z)(ACge,ACle,ACmemory n)=Some(Vint32 Int.one) /\
 evalval(V293_OSSched_zero 131%Z)(ACge,ACle,Ml)=
  Some(if Nat.eqb l 0 then Vint32 Int.one else Vint32 Int.zero) /\
 TaskSim(RCprogram,(ACpo,CGempty,ip))(curs(scall 114%Z nil),(kenil,kstop))
 (ACge,ACle,Ml,(fun _=>false),(false,nil,nil))
 (RCprogram,QCspec)(curs(scall 114%Z nil),(kenil,kstop))
 (RIabstract OwnershipWaiting)V293_shared_li ACinv
 (fun st=>satp(fst st)(snd st)(RDYINV ACinv OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.
Proof.
 intros n l ip NB LB Stop.
 pose proof(ACbase n NB)as Base.
 unfold ACresource,V293_exit_active_resource,V293_exit_guard_resource in Base.
 assert(Pack:V293_target_wstate ACge ACle(ACmemory n)(RIabstract OwnershipWaiting)|=
 V293_owned_record_cell((151%positive,0%Z),Tint8,V293_byteval 0) **NDrest n).
 { unfold NDrest;clear -Base;sep auto. }
 assert(Read:load Tint8(ACmemory n)(151%positive,0%Z)=Some(V293_byteval 0)).
 { change(load Tint8(assertion.getmem(V293_target_wstate ACge ACle(ACmemory n)(RIabstract OwnershipWaiting)))
   (151%positive,0%Z)=Some(V293_byteval 0)).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Pack]. }
 destruct(V293_owned_record_cell_update (151%positive,0%Z) Tint8(V293_byteval 0)(V293_byteval l)
 _ _ _ _ _ _ _ _ (V293_byte_type l LB) Pack)as(Ml&Store&After).
 assert(ReadAfter:load Tint8 Ml(151%positive,0%Z)=Some(V293_byteval l)).
 { change(load Tint8(assertion.getmem(V293_target_wstate ACge ACle Ml(RIabstract OwnershipWaiting)))
   (151%positive,0%Z)=Some(V293_byteval l)).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact After]. }
 exists Ml;split;[exact Read| ];split;[exact Store| ];split;[exact ReadAfter| ];split.
 - intros b i Different;eapply V293_storebytes_outside;[exact Store| ].
   destruct(Pos.eq_dec b 151%positive)as[Same|Other];[subst b|left;exact Other].
   right;assert(i<>0%Z)by(intro E;apply Different;congruence).
   cbn[encode_val V293_byteval inj_bytes encode_int List.map length];lia.
 - split.
   + eapply V293_exit_zero_eval;[reflexivity|reflexivity|exact Read].
   + split.
     * destruct l as[ |l].
       -- eapply V293_exit_zero_eval;[reflexivity|reflexivity|exact ReadAfter].
       -- eapply V293_nested_zero_eval with(n:=S l);[lia|exact LB|reflexivity|reflexivity|exact ReadAfter].
     * eapply NDnonempty_client_call;[exact NB|exact LB|exact Stop| ].
       eapply NDupdated_resource;exact After.
Qed.
