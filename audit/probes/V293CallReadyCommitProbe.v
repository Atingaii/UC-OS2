(* Closed physical entry reused without copying its byte fixture.
   Removing only the main function binding checks entry, not later commits. *)
Require Import CertiOS.framework.include_frm.
Require Import CertiOS.certiucos.v293.proofs.V293CallReadyCommit.
Require Import CertiOS.certiucos.v293.proofs.V293CriticalReturn.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitFunction.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitEntry.
Require Import CertiOS.certiucos.v293.proofs.V293InitRdyList.
Require Import CertiOS.certiucos.v293.proofs.V293TCBInitPrefix.
Require Import CertiOS.certiucos.v293.proofs.V293TCBPriorityHook.
Require Import CertiOS.certiucos.v293.proofs.V293TaskRecordOwnership.
Require Import CertiOS.certiucos.v293.proofs.V293PublishRecords.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewExec.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewHoare.
Require Import CertiOS.certiucos.v293.code.V293OSTCBInitFunction.
Require Import CertiOS.certiucos.v293.code.V293OSTaskChangePrio.
Require Import CertiOS.audit.probes.V293CallRecordsProbe.
Require Import Coq.Lists.List.
Import ListNotations.

Definition CRCProgram (bound : bool) (f : fid) : option function :=
 if Z.eq_dec f 900%Z then
  if bound then Some(V293_TCBInit_function 901%Z 902%Z) else None
 else CallFixtureProgram f.

Theorem CRCBindingOnly :
 CRCProgram true 900%Z=Some(V293_TCBInit_function 901%Z 902%Z) /\
 CRCProgram false 900%Z=None /\
 (forall f, f<>900%Z -> CRCProgram true f=CRCProgram false f).
Proof.
 split;[reflexivity | ]. split;[reflexivity | ].
 intros f Different. unfold CRCProgram. destruct(Z.eq_dec f 900%Z);congruence.
Qed.

Theorem CRCInitialLocalsAbsent : forall b i,
 In b CallBlocks -> get(CallMemory CallCells)(b,i)=None.
Proof. exact CallNoInitialLocals. Qed.

Theorem CRCActualPrefix : forall ks enabled si ci, exists Mf,
 V293_local_steps (CRCProgram true) (curs(CallCode 900%Z),(kenil,ks))
 ((CallGE,CallCaller,CallMemory CallCells),(fun _=>false),(enabled,si,ci))
 (curs(sfexec 901%Z [Vptr CallNewTid] [Tptr V293_tcb_type]),
  (kenil,V293_tcb_first_hook_cont 900%Z 901%Z 902%Z CallCaller ks))
 ((CallGE,CallLE,Mf),(fun _=>false),(enabled,si,ci)) /\
 (CallEntryState Mf |= V293_owned_task_records CallUpdated ** V293_rdy_raw_cells (CallHookCells false) Atrue).
Proof.
 intros ks enabled si ci. apply CallPrefix. reflexivity.
Qed.

Theorem CRCMissingEntryRejected : forall ks enabled si ci,
 (~exists C' state', loststep (CRCProgram false) (curs(CallCode 900%Z),(kenil,ks))
  ((CallGE,CallCaller,CallMemory CallCells),(fun _=>false),(enabled,si,ci)) C' state') /\
 (forall ret ks' state', ~V293_local_steps (CRCProgram false)
  (curs(CallCode 900%Z),(kenil,ks))
  ((CallGE,CallCaller,CallMemory CallCells),(fun _=>false),(enabled,si,ci))
  (curs(sskip ret),(kenil,ks')) state').
Proof.
 intros ks enabled si ci. split.
 - apply V293_missing_port_has_no_step. reflexivity.
 - intros ret ks' state'. apply V293_tcb_missing_call_cannot_return. reflexivity.
Qed.
Print Assumptions CRCBindingOnly.
Print Assumptions CRCInitialLocalsAbsent.
Print Assumptions CRCActualPrefix.
Print Assumptions CRCMissingEntryRejected.
