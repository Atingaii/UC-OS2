(* One fixed front end over actual heaps. Old complete calls below still have
   distinct CCspec/QCspec; no old WFInt or concrete trace is inferred. *)
Require Import CertiOS.audit.probes.V293InterruptControlRetentionProbe.
Require Import CertiOS.audit.probes.V293ExitDispatchCallTaskSimProbe.
Require Import CertiOS.audit.probes.V293ExitActiveCallTaskSimProbe.
Require Import CertiOS.audit.probes.V293ReadyTaskInvariantProbe.
Require Import CertiOS.audit.probes.V293TaskRecordOwnershipProbe.
Require Import CertiOS.audit.probes.V293TaskRecordInvariantProbe.
Require Import CertiOS.audit.probes.V293ExitClientCallTaskSimProbe.
Require Import CertiOS.audit.probes.V293ExitQuietCallTaskSimProbe.
Require Import CertiOS.audit.probes.V293ReadyCriticalGlobalProbe.
Require Import CertiOS.audit.probes.V293ReadySchedCallProbe.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptFixedControlSpec.
Require Import CertiOS.certiucos.v293.proofs.V293InterruptControlRetention.
Require Import CertiOS.certiucos.v293.proofs.V293OSSchedNewEval.
Require Import CertiOS.certiucos.v293.model.V293SchedulerTasks.
Require Import CertiOS.framework.include_frm.
Require Import Coq.Lists.List Lia.
Local Open Scope nat_scope.

Theorem FCexit_lock_pair : forall n i,n<=1 ->i<INUM ->exists Ml,
 store Tint8(ACmemory n)(151%positive,0%Z)(V293_byteval 1)=Some Ml /\
 (forall b off,(b,off)<>(151%positive,0%Z) ->get Ml(b,off)=get(ACmemory n)(b,off)) /\
 V293_control_read 152%positive 150%positive 151%positive(ACmemory n)=Some(V293_control 1 n 0) /\
 V293_control_read 152%positive 150%positive 151%positive Ml=Some(V293_control 1 n 1) /\
 V293_fixed_control_intspec i=Some V293_fixed_control_handler /\
 V293_control_step V293_scheduler V293_control_Exit(RIabstract OwnershipWaiting,V293_control 1 n 0)
 (V293_control_Core(sched;;spec_done None))(RIabstract OwnershipWaiting,V293_control 1 0 0) /\
 V293_control_step V293_scheduler V293_control_Exit(RIabstract OwnershipWaiting,V293_control 1 n 1)
 (V293_control_Core(spec_done None))(RIabstract OwnershipWaiting,V293_control 1 0 1) /\
 CRcall(ACmemory n)CCspec (fun _=>None) /\ CRcall Ml QCspec (fun _=>None).
Proof.
 intros n i N I.
 destruct(CRlock_only_pair n (fun _=>None) N)as[Ml[Store[Outside[Read[Read'[_[_[_[Enabled[Quiet Calls]]]]]]]]]].
 exists Ml;split;[exact Store| ];split;[exact Outside| ];split;[exact Read| ];split;[exact Read'| ];split.
 - apply V293_fixed_control_lookup;exact I.
 - assert(Depth:Nat.pred n=0)by lia.
   assert(Exit0:V293_control_exit(V293_control 1 n 0)=V293_control 1 0 0).
   { unfold V293_control_exit;cbn;rewrite Depth;reflexivity. }
   assert(Exit1:V293_control_exit(V293_control 1 n 1)=V293_control 1 0 1).
   { unfold V293_control_exit;cbn;rewrite Depth;reflexivity. }
   split;[ |split;[ |exact Calls]].
   + rewrite <-Enabled,<-Exit0;constructor;unfold V293_control_valid;cbn;lia.
   + rewrite <-Quiet,<-Exit1;constructor;unfold V293_control_valid;cbn;lia.
Qed.

(* The whole fixed Enter/Exit prefix, not completion of the enabled scheduler. *)
Theorem FCpair_boundaries : forall sd O,
 V293_control_steps sd V293_fixed_control_handler(O,V293_control 1 0 0)
  (V293_control_Core(sched;;spec_done None))(O,V293_control 1 0 0) /\
 V293_control_steps sd V293_fixed_control_handler(O,V293_control 1 1 0)
  (V293_control_Core(spec_done None))(O,V293_control 1 1 0) /\
 V293_control_steps sd V293_fixed_control_handler(O,V293_control 1 255 0)
  (V293_control_Core(spec_done None))(O,V293_control 1 254 0) /\
 V293_control_steps sd V293_fixed_control_handler(O,V293_control 0 255 0)
  (V293_control_Core(spec_done None))(O,V293_control 0 255 0) /\
 V293_control_steps sd V293_fixed_control_handler(O,V293_control 2 0 0)
  (V293_control_Core(spec_done None))(O,V293_control 2 0 0) /\
 V293_control_steps sd V293_fixed_control_handler(O,V293_control 1 0 255)
  (V293_control_Core(spec_done None))(O,V293_control 1 0 255).
Proof.
 intros;repeat split;apply V293_fixed_control_handler_prefix;unfold V293_control_valid;cbn;lia.
Qed.

Theorem FCquiet_nonhighest :
 ~spec_step V293_scheduler sched(RIabstract OwnershipWaiting)
 (spec_done None)(RIabstract OwnershipWaiting) /\
 V293_control_step V293_scheduler V293_control_Exit(RIabstract OwnershipWaiting,V293_control 1 1 1)
 (V293_control_Core(spec_done None))(RIabstract OwnershipWaiting,V293_control 1 0 1).
Proof.
 split;[exact DCwaiting_no_self_sched| ];constructor;unfold V293_control_valid;cbn;lia.
Qed.

(* Global switching has not been ported; Core does not invent a self step. *)
Theorem FCenabled_not_self : forall c,
 ~V293_control_step V293_scheduler(V293_control_Core sched)(RIabstract OwnershipWaiting,c)
 (V293_control_Core(spec_done None))(RIabstract OwnershipWaiting,c).
Proof.
 intros c H;apply V293_control_core_exact in H.
 destruct H as[b[O'[Code[State Step]]]];inversion Code;inversion State;subst.
 exact(DCwaiting_no_self_sched Step).
Qed.

Theorem FCsingle_decrement : forall sd O,
 V293_control_step sd V293_control_Exit(O,V293_control 1 2 0)
 (V293_control_Core(spec_done None))(O,V293_control 1 1 0) /\
 V293_control_step sd V293_control_Exit(O,V293_control 1 1 0)
 (V293_control_Core(sched;;spec_done None))(O,V293_control 1 0 0) /\
 V293_control_exit_code(V293_control_exit(V293_control 1 2 0))<>
 V293_control_exit_code(V293_control 1 2 0).
Proof.
 intros;split;[constructor;unfold V293_control_valid;cbn;lia| ];split.
 - constructor;unfold V293_control_valid;cbn;lia.
 - discriminate.
Qed.
