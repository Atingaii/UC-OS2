(* Nested call on the original nonempty heap; no abstract scheduling. *)
Require Import CertiOS.audit.probes.V293ExitActiveCallTaskSimProbe.
Require Import CertiOS.audit.probes.V293ExitGuardHelperProbe.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.certiucos.v293.proofs.V293ExitNestedCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitActiveCallTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293ExitCriticalPrefixTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.proofs.V293ExitNestingProgSim.
Require Import CertiOS.certiucos.v293.code.V293OSSchedGuards.
Require Import CertiOS.certiucos.v293.proofs.V293ReadyStorageInvariant.
Require Import CertiOS.certiucos.v293.proofs.V293SharedState.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.framework.proof.simulation.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.proofs.V293SchedHelperBodyTaskSim.
Require Import CertiOS.certiucos.v293.proofs.V293TCBJointShared.
Require Import CertiOS.certiucos.v293.proofs.V293TaskPrioRekey.
Require Import CertiOS.tactics.sepauto.seplog_tactics.
Require Import CertiOS.tactics.sepauto.seplog_lemmas.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedTargetWitness.
Require Import Coq.Lists.List Lia.
Import ListNotations.
Local Open Scope nat_scope.
Definition NCspec:osspec:=((fun f=>if Z.eq_dec f 114%Z then
 Some((fun _:vallist=>spec_done None),(Tvoid,nil))else None),
 (fun _=>None),V293_scheduler).
Theorem NCnonempty_client_call : forall n ip,
 2<=n ->n<256 ->
 TaskSim(RCprogram,(ACpo,CGempty,ip))(curs(scall 114%Z nil),(kenil,kstop))
 (ACge,ACle,ACmemory n,(fun _=>false),(false,nil,nil))
 (RCprogram,NCspec)(curs(scall 114%Z nil),(kenil,kstop))
 (RIabstract OwnershipWaiting)V293_shared_li ACinv
 (fun st=>satp(fst st)(snd st)(RDYINV ACinv OwnershipWaiting **LINV V293_shared_li OwnershipWaiting nil))OwnershipWaiting.
Proof.
 intros n ip Nested Bound;unfold ACinv,ACrest,ACle.
 eapply V293_exit_nested_client_call_TaskSim with(nc:=6)(bc:=94%positive)(bo:=93%positive)
 (oldtarget:=Vptr OwnershipWaiting)(c:=Int.mone)(oldhigh:=V293_byteval 88)
 (rest:=nil)(saved:=120%Z)(helper:=107%Z)
 (running:=132%Z)(nesting:=130%Z)(lock:=131%Z).
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - right;right;reflexivity.
 - exact Nested.
 - exact Bound.
 - discriminate.
 - discriminate.
 - reflexivity.
 - reflexivity.
 - reflexivity.
 - apply ACbase;exact Bound.
Qed.

Definition NCframe:=
 V293_owned_record_cell((152%positive,0%Z),Tint8,V293_byteval 1) **
 (V293_owned_record_cell((151%positive,0%Z),Tint8,V293_byteval 0) **
 V293_helper_resource 80%positive 81%positive 82%positive 92%positive 91%positive OwnershipWaiting
 (V293_exit_active_frame 92%positive 94%positive 93%positive 95%positive nil 6
 (Vptr OwnershipWaiting)Int.mone)(V293_byteval 88)).

(* Single-factor local store control: both guards are false, but the byte differs.
   This does not assert an omitted-decrement whole-body execution theorem. *)
Theorem NCdecrement_control : forall n,
 2<=n ->n<256 ->exists Md,
 load Tint8(ACmemory n)(150%positive,0%Z)=Some(V293_byteval n) /\
 store Tint8(ACmemory n)(150%positive,0%Z)(V293_byteval(Nat.pred n))=Some Md /\
 load Tint8 Md(150%positive,0%Z)=Some(V293_byteval(Nat.pred n)) /\
 V293_byteval(Nat.pred n)<>V293_byteval n /\
 (forall b i,(b,i)<>(150%positive,0%Z) ->get Md(b,i)=get(ACmemory n)(b,i)) /\
 evalval(V293_OSSched_zero 130%Z)(ACge,ACle,Md)=Some(Vint32 Int.zero) /\
 evalval(V293_OSSched_zero 130%Z)(ACge,ACle,ACmemory n)=Some(Vint32 Int.zero).
Proof.
 intros n Nested Bound.
 pose proof(ACbase n Bound)as Base.
 assert(Own:V293_target_wstate ACge ACle(ACmemory n)(RIabstract OwnershipWaiting)|=
 V293_owned_record_cell((150%positive,0%Z),Tint8,V293_byteval n) **NCframe).
 { unfold ACresource,V293_exit_active_resource,V293_exit_guard_resource in Base.
   unfold NCframe,V293_target_wstate in *;clear -Base;sep auto. }
 assert(Read:load Tint8(ACmemory n)(150%positive,0%Z)=Some(V293_byteval n)).
 { change(load Tint8(assertion.getmem(V293_target_wstate ACge ACle(ACmemory n)(RIabstract OwnershipWaiting)))
 (150%positive,0%Z)=Some(V293_byteval n)).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact Own]. }
 destruct(V293_owned_record_cell_update _ _ _ (V293_byteval(Nat.pred n)) _ _ _ _ _ _ _ _
  (V293_byte_type(Nat.pred n)ltac:(lia)) Own)as(Md&Store&After).
 assert(ReadAfter:load Tint8 Md(150%positive,0%Z)=Some(V293_byteval(Nat.pred n))).
 { change(load Tint8(assertion.getmem(V293_target_wstate ACge ACle Md(RIabstract OwnershipWaiting)))
 (150%positive,0%Z)=Some(V293_byteval(Nat.pred n))).
   eapply V293_record_star_load_l;[apply V293_owned_record_cell_load|exact After]. }
 exists Md;split;[exact Read| ];split;[exact Store| ];split;[exact ReadAfter| ];split.
 - intro E;assert(Nat.pred n=n)by(eapply V293_byteval_injective_bounded;[lia|exact Bound|exact E]);lia.
 - split.
   + intros b i Different;eapply V293_storebytes_outside;[exact Store| ].
     destruct(Pos.eq_dec b 150%positive)as[Same|Other];[subst b|left;exact Other].
     right;assert(i<>0%Z)by(intro E;apply Different;congruence).
     cbn[encode_val V293_byteval inj_bytes encode_int List.map length];lia.
   + split.
     * eapply V293_nested_zero_eval with(n:=Nat.pred n)(b:=150%positive);try reflexivity;try exact ReadAfter;lia.
     * eapply V293_nested_zero_eval with(n:=n)(b:=150%positive);try reflexivity;try exact Read;lia.
Qed.

Corollary NCdecrement_control_2 : exists Md,
 load Tint8(ACmemory 2)(150%positive,0%Z)=Some(V293_byteval 2) /\
 store Tint8(ACmemory 2)(150%positive,0%Z)(V293_byteval 1)=Some Md /\
 load Tint8 Md(150%positive,0%Z)=Some(V293_byteval 1).
Proof. destruct(NCdecrement_control 2 ltac:(lia)ltac:(lia))as(Md&R&S&A&Rest);exists Md;auto. Qed.
Corollary NCdecrement_control_255 : exists Md,
 load Tint8(ACmemory 255)(150%positive,0%Z)=Some(V293_byteval 255) /\
 store Tint8(ACmemory 255)(150%positive,0%Z)(V293_byteval 254)=Some Md /\
 load Tint8 Md(150%positive,0%Z)=Some(V293_byteval 254).
Proof. destruct(NCdecrement_control 255 ltac:(lia)ltac:(lia))as(Md&R&S&A&Rest);exists Md;auto. Qed.
